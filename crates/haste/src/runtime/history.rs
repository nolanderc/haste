#![allow(dead_code)]

mod bit_set;
mod range_query;

use std::{collections::BTreeMap, num::NonZeroU32};

use crate::{revision::Revision, Durability, RevisionRange};

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
                let mut history = History::default();
                history.record_change(None, None);
                history
            }),
        }
    }

    pub fn current(&self) -> Revision {
        let index = self.histories[0].len() as u32;
        Revision::from_index(unsafe { NonZeroU32::new_unchecked(index) })
    }

    /// When an input has been modified, this function is called with the previous revision in
    /// which was modified in (or `None` if the input is new). Returns a new revision for the
    /// input.
    ///
    /// Time complexity: `O(log n)`
    pub fn push_update(
        &mut self,
        last_changed: Option<Revision>,
        durability: Durability,
    ) -> Revision {
        let new =
            Revision::new(self.histories[0].len() as u32 + 1).expect("exhausted revision IDs");

        let durability_level = durability.index() + 1;
        let (lower, higher) = self.histories.split_at_mut(durability_level);

        // any queries with lower durability might be affected by the change
        for history in lower {
            history.record_change(last_changed, Some(new));
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
        range: RevisionRange,
        rev: Revision,
        durability: Durability,
    ) -> bool {
        let history = &self.histories[durability.index()];
        history.any_changed_since(range, rev)
    }
}

#[derive(Default)]
struct History {
    /// The revision in which the last change happened
    last_change: Option<Revision>,
    /// A detailed accounting of all changes that have ever been made.
    detailed: BitHistory<RevisionSet>,
}

impl History {
    fn len(&self) -> usize {
        self.detailed.len()
    }

    fn record_change(&mut self, change: Option<Revision>, current: Option<Revision>) -> usize {
        if change.is_some() {
            self.last_change = current;
        }
        self.detailed.push(change)
    }

    fn any_changed_since(&self, range: RevisionRange, rev: Revision) -> bool {
        if self.last_change <= Some(rev) {
            // fast path if there have been no changes at all
            return false;
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

enum RevisionSet {
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

impl RevisionSet {
    fn new() -> Self {
        Self::Small(RangeBitSet::new())
    }

    fn insert(&mut self, revision: Revision) {
        let index = revision.index();

        match self {
            RevisionSet::Small(small) => {
                if small.insert(index).is_err() {
                    let mut tree = BTreeMap::new();

                    let first = small.first().unwrap();
                    let segment = segment(first);
                    let next_segment = segment + 1;
                    let first_in_next_segment = next_segment << SEGMENT_SHIFT;

                    let (left_bits, right_bits) = small.split_at_raw(first_in_next_segment);

                    tree.insert(segment, left_bits);

                    if !right_bits.is_empty() {
                        tree.insert(next_segment, right_bits);
                    }

                    *self = RevisionSet::Tree(tree);
                }
            }
            RevisionSet::Tree(tree) => {
                tree.entry(segment(index))
                    .or_insert(BitSet::new())
                    .insert(segment_index(index));
            }
        }
    }

    fn contains_range(&self, range: RevisionRange) -> bool {
        let min = range.earliest.index();
        let max = range.latest.index();

        match self {
            RevisionSet::Small(small) => small.contains_range(min..=max),
            RevisionSet::Tree(tree) => {
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

    fn iter(&self) -> impl Iterator<Item = Revision> + '_ {
        let mut inner = match self {
            RevisionSet::Small(bits) => Ok(bits.iter()),
            RevisionSet::Tree(tree) => Err(tree.iter().flat_map(|(segment, bits)| {
                let segment_start = segment << SEGMENT_SHIFT;
                bits.iter().map(move |i| segment_start + i)
            })),
        };
        std::iter::from_fn(move || {
            let next = match &mut inner {
                Ok(a) => a.next(),
                Err(b) => b.next(),
            };
            next.map(|i| Revision::new(i).unwrap())
        })
    }
}

impl std::fmt::Debug for RevisionSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl range_query::Set for RevisionSet {
    type Element = Option<Revision>;

    fn make(element: Self::Element) -> Self {
        let mut this = RevisionSet::new();
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
        for revision in other.iter() {
            self.insert(revision);
        }
    }
}
