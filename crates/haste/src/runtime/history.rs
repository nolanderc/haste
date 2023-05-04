#![allow(dead_code)]

mod bit_set;
mod range_query;

use std::{collections::BTreeMap, num::NonZeroU32};

use crate::{
    revision::{InputId, Revision},
    Durability, InputRange,
};

use self::{
    bit_set::{BitSet, RangeBitSet},
    range_query::BitHistory,
};

pub struct ChangeHistory {
    histories: [History; Durability::LEVELS],
}

impl ChangeHistory {
    pub fn new() -> Self {
        Self {
            histories: std::array::from_fn(|_| {
                let mut history = History::new();
                history.record_change(None, None);
                history
            }),
        }
    }

    pub fn current_revision(&self) -> Revision {
        let index = self.histories[0].len() as u32;
        Revision::from_index(unsafe { NonZeroU32::new_unchecked(index) })
    }

    /// When an input has been modified, this function is called with that input's ID and
    /// durability. This allows queries which depend on the input to detect the change.
    ///
    /// Returns the new revision.
    ///
    /// Time complexity: `O(log n)`
    pub fn push_update(&mut self, input: Option<InputId>, durability: Durability) -> Revision {
        let new =
            Revision::new(self.histories[0].len() as u32 + 1).expect("exhausted revision IDs");

        let durability_level = durability.index() + 1;
        let (lower, higher) = self.histories.split_at_mut(durability_level);

        // any queries with lower durability might be affected by the change
        for history in lower {
            history.record_change(input, Some(new));
        }

        // no detectable change for queries with higher durability:
        for history in higher {
            history.record_change(None, Some(new));
        }

        new
    }

    /// Checks if any of the inputs from the given range have been changed in one of the revisions
    /// `rev+1, rev+2, ..`.
    ///
    /// The worst time complexity of this operaiton is `O(log^2 n)` where `n` is the size of the
    /// history, but in reality it is often closer to `O(1)` when changes are mostly contained to a
    /// small set of inputs (which is the average case).
    pub fn any_changed_since(
        &self,
        range: InputRange,
        rev: Revision,
        durability: Durability,
    ) -> bool {
        let history = &self.histories[durability.index()];
        history.any_changed_since(range, rev)
    }
}

struct History {
    /// The revision in which the last change happened
    last_change: Option<Revision>,
    /// A detailed accounting of all changes that have ever been made.
    detailed: BitHistory<InputSet>,
    /// Disables the revision history, only using the last change to durability.
    disabled: bool,
}

impl History {
    fn new() -> Self {
        let disabled = matches!(
            std::env::var("HASTE_HISTORY").as_deref(),
            Ok("off" | "disabled" | "0")
        );

        Self {
            last_change: None,
            detailed: BitHistory::default(),
            disabled,
        }
    }

    fn len(&self) -> usize {
        self.detailed.len()
    }

    fn record_change(&mut self, change: Option<InputId>, current: Option<Revision>) -> usize {
        if change.is_some() {
            self.last_change = current;
        }

        self.detailed.push(change)
    }

    fn any_changed_since(&self, range: InputRange, rev: Revision) -> bool {
        if self.last_change <= Some(rev) {
            // fast path if there have been no changes at all
            return false;
        }

        if self.disabled {
            return true;
        }

        // more detailed check if there has been an update:
        let index = rev.index() as usize;

        let mut has_changed = false;
        self.detailed.query(index.., |changed| {
            has_changed |= changed.contains_range(range);
        });
        has_changed
    }
}

enum InputSet {
    Small(RangeBitSet),
    Tree(BTreeMap<u32, BitSet>),
}

const SEGMENT_SHIFT: u32 = BitSet::BITS.ilog2();
const SEGMENT_MASK: u32 = BitSet::BITS as u32 - 1;

const fn segment(index: u32) -> u32 {
    index >> SEGMENT_SHIFT
}

const fn segment_index(index: u32) -> u32 {
    index & SEGMENT_MASK
}

impl InputSet {
    fn new() -> Self {
        Self::Small(RangeBitSet::new())
    }

    fn insert(&mut self, input: InputId) {
        let index = input.index();

        match self {
            InputSet::Small(small) => {
                if small.insert(index).is_err() {
                    let mut tree = BTreeMap::new();

                    let first = small.first().unwrap();
                    let segment = segment(first);
                    let next_segment = segment + 1;
                    let first_in_next_segment = next_segment << SEGMENT_SHIFT;

                    let (left_bits, right_bits) = small.split_at_raw(first_in_next_segment);

                    if !left_bits.is_empty() {
                        tree.insert(segment, left_bits);
                    }
                    if !right_bits.is_empty() {
                        tree.insert(next_segment, right_bits);
                    }

                    Self::insert_tree(&mut tree, index);

                    *self = InputSet::Tree(tree);
                }
            }
            InputSet::Tree(tree) => Self::insert_tree(tree, index),
        }
    }

    fn insert_tree(tree: &mut BTreeMap<u32, BitSet>, index: u32) {
        tree.entry(segment(index))
            .or_insert(BitSet::new())
            .insert(segment_index(index));
    }

    fn contains_range(&self, range: InputRange) -> bool {
        let min = range.min.index();
        let max = range.max.index();

        match self {
            InputSet::Small(small) => small.contains_range(min..=max),
            InputSet::Tree(tree) => {
                let min_segment = segment(min);
                let max_segment = segment(max);

                if min_segment == max_segment {
                    let Some(bits) = tree.get(&min_segment) else { return false };
                    return bits.contains_range(segment_index(min)..=segment_index(max));
                }

                let mut segments = tree.range(min_segment..=max_segment);

                macro_rules! next {
                    () => {{
                        let Some((segment, bits)) = segments.next() else { return false };
                        (*segment, *bits)
                    }};
                }

                let (mut segment, mut bits) = next!();

                if segment == min_segment {
                    if bits.contains_range(segment_index(min)..) {
                        return true;
                    }
                    (segment, bits) = next!();
                }

                if segment == max_segment {
                    return bits.contains_range(..=segment_index(max));
                }

                // we found a segment in-between the min and max segments, since there are no empty
                // segments in the tree, the range contained an item
                true
            }
        }
    }

    fn iter(&self) -> impl Iterator<Item = InputId> + '_ {
        let mut inner = match self {
            InputSet::Small(bits) => Ok(bits.iter()),
            InputSet::Tree(tree) => Err(tree.iter().flat_map(|(segment, bits)| {
                let segment_start = segment << SEGMENT_SHIFT;
                bits.iter().map(move |i| segment_start + i)
            })),
        };
        std::iter::from_fn(move || {
            let next = match &mut inner {
                Ok(a) => a.next(),
                Err(b) => b.next(),
            };
            next.map(|i| InputId::new(i).unwrap())
        })
    }
}

impl std::fmt::Debug for InputSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl range_query::Set for InputSet {
    type Element = Option<InputId>;

    fn make(element: Self::Element) -> Self {
        let mut this = InputSet::new();
        if let Some(revision) = element {
            this.insert(revision);
        }
        this
    }

    fn insert(&mut self, element: &Self::Element) {
        if let Some(revision) = element {
            self.insert(*revision);
        }
    }

    fn merge(&mut self, other: &Self) {
        for input in other.iter() {
            self.insert(input);
        }
    }
}
