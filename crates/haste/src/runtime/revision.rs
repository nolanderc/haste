#![allow(dead_code)]

use std::{
    num::NonZeroU32,
    sync::atomic::{
        AtomicU32, AtomicU64,
        Ordering::{self, Relaxed},
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Revision(NonZeroU32);

impl Revision {
    fn new(x: u32) -> Option<Revision> {
        Some(Self(NonZeroU32::new(x)?))
    }
}

unsafe impl bytemuck::ZeroableInOption for Revision {}

fn to_u32(rev: Option<Revision>) -> u32 {
    rev.map(|x| x.0.get()).unwrap_or(0)
}

#[derive(Debug, bytemuck::Zeroable)]
pub struct AtomicRevision(AtomicU32);

impl AtomicRevision {
    pub fn new(revision: Option<Revision>) -> Self {
        Self(AtomicU32::new(to_u32(revision)))
    }

    pub fn load(&self, order: Ordering) -> Option<Revision> {
        Self::from_u32(self.0.load(order))
    }

    pub fn store(&self, rev: Option<Revision>, order: Ordering) {
        self.0.store(to_u32(rev), order)
    }

    pub fn swap(&self, rev: Option<Revision>, order: Ordering) -> Option<Revision> {
        Self::from_u32(self.0.swap(to_u32(rev), order))
    }

    pub(crate) fn set(&mut self, rev: Option<Revision>) {
        *self.0.get_mut() = to_u32(rev);
    }

    pub(crate) fn get(&mut self) -> Option<Revision> {
        Self::from_u32(*self.0.get_mut())
    }

    fn from_u32(num: u32) -> Option<Revision> {
        Some(Revision(NonZeroU32::new(num)?))
    }
}

pub struct RevisionHistory {
    history: MinHistory,
}

impl RevisionHistory {
    pub fn new() -> Self {
        let mut history = MinHistory::new();
        history.push(1);
        Self { history }
    }

    pub fn current(&self) -> Revision {
        let index = self.history.len() as u32;
        Revision(unsafe { NonZeroU32::new_unchecked(index) })
    }

    /// When an input has been modified, this function is called with the previous revision in
    /// which was modified in (or `None` if the input is new). Returns a new revision for the
    /// input.
    ///
    /// Time complexity: `O(log n)`
    pub fn push_update(&mut self, last_changed: Option<Revision>) -> Revision {
        let new = Revision::new(self.history.len() as u32 + 1).unwrap();
        let revision = last_changed.unwrap_or(new);
        self.history.push(revision.0.get());
        new
    }

    /// Given some revision `rev`, finds the earliest input that has been changed in one of the
    /// revisions `rev+1, rev+2, ..`.
    ///
    /// Time complexity: `O(log n)`
    pub fn earliest_change_since(&self, rev: Revision) -> Revision {
        Revision::new(self.history.min_since(rev.0.get() as usize).unwrap()).unwrap()
    }
}

/// A Binary-Indxed-Tree (BIT) which for each index `i` stores the minimum of values `i..` in
/// a growable list.
///
/// The implementation is heavily inspired by the paper [Efficient Range Minimum Queries using
/// Binary Indexed Trees](https://ioinformatics.org/journal/v9_2015_39_44.pdf), but since we
/// are only interested in `i..` queries (and not the more general `a..b`) we can get away with
/// a single BIT (BIT2 in the paper). By using the invariant that the BIT's size is always a
/// power-of-two we don't even need to store the original values, effectively reducing the
/// memory usage by two thirds.
///
/// Since we are expected to query the same ranges repeatedly, there is also a thin caching
/// layer on top: any time a query `i..` is executed, we cache the current length of the
/// history and the minimum value at the index `i`. Then, if we encounter that index `i` later
/// and the length hasn't changed (ie. no modifications have happened) we returned the cached
/// value.
struct MinHistory {
    len: usize,
    min_bit: Vec<u32>,
    cache: Vec<Cached>,
}

struct Cached {
    /// Combines two `u32`s:
    /// - the length of the history when this slot was created.
    /// - the minimum element at that time.
    bits: AtomicU64,
}

impl Cached {
    fn new(len: usize, min: u32) -> Cached {
        Cached {
            bits: AtomicU64::new(Self::make_bits(len, min)),
        }
    }

    fn store(&self, len: usize, min: u32) {
        self.bits.store(Self::make_bits(len, min), Relaxed);
    }

    fn get(&self, len: usize) -> Option<u32> {
        let bits = self.bits.load(Relaxed);
        let (cached_len, min) = Self::from_bits(bits);
        if cached_len == len {
            Some(min)
        } else {
            None
        }
    }

    fn make_bits(len: usize, min: u32) -> u64 {
        let index = u64::from(min);
        let len = u64::from(u32::try_from(len).unwrap());
        (index << 32) | len
    }

    fn from_bits(bits: u64) -> (usize, u32) {
        let min = (bits >> 32) as u32;
        let len = bits as u32;
        (len as usize, min)
    }
}

impl MinHistory {
    pub fn new() -> Self {
        Self {
            len: 0,
            min_bit: Vec::new(),
            cache: Vec::new(),
        }
    }

    /// Create a history from an existing list of items.
    pub fn from_vec(mut values: Vec<u32>) -> Self {
        // pad to the next power of two
        let len = values.len();
        let required_len = len.next_power_of_two();
        values.resize(required_len, u32::MAX);

        let mut bit = values;
        for i in (1..len + 1).rev() {
            let parent = i - lsb(i);
            if parent > 0 {
                bit[parent - 1] = std::cmp::min(bit[parent - 1], bit[i - 1]);
            }
        }

        let mut cache = Vec::new();
        cache.resize_with(required_len, || Cached::new(0, 0));

        Self {
            len,
            min_bit: bit,
            cache,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Push a new value onto the end of the list, returning its index.
    pub fn push(&mut self, value: u32) {
        let index = self.len;
        self.len += 1;

        // pad to the next power of two
        let required_len = self.len.next_power_of_two();
        self.min_bit.resize(required_len, u32::MAX);
        self.cache.resize_with(required_len, || Cached::new(0, 0));

        self.min_bit[index] = value;

        let mut i = index + 1;
        loop {
            i -= lsb(i);
            if i == 0 {
                break;
            }
            self.min_bit[i - 1] = std::cmp::min(value, self.min_bit[i - 1]);
        }
    }

    pub fn min_since(&self, index: usize) -> Option<u32> {
        let cache = self.cache.get(index)?;
        if let Some(cached) = cache.get(self.len) {
            return Some(cached);
        }

        let mut min = u32::MAX;

        let mut i = index + 1;
        loop {
            min = std::cmp::min(min, self.min_bit[i - 1]);
            i += lsb(i);
            if i > self.min_bit.len() {
                break;
            }
        }

        cache.store(self.len, min);

        Some(min)
    }
}

impl Default for MinHistory {
    fn default() -> Self {
        Self::new()
    }
}

/// Returns the least significant bit of `x`
fn lsb(x: usize) -> usize {
    x & (!x).wrapping_add(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn revision_history_query() {
        let mut history = MinHistory::new();
        history.push(1);
        history.push(2);
        history.push(3);
        assert_eq!(history.min_since(0), Some(1));
        assert_eq!(history.min_since(1), Some(2));
        assert_eq!(history.min_since(2), Some(3));
    }

    #[test]
    fn revision_history_from_vec() {
        let history = MinHistory::from_vec(vec![1, 2, 3, 1, 8, 5, 6, 9]);
        assert_eq!(history.min_since(0), Some(1));
        assert_eq!(history.min_since(1), Some(1));
        assert_eq!(history.min_since(2), Some(1));
        assert_eq!(history.min_since(3), Some(1));
        assert_eq!(history.min_since(4), Some(5));
        assert_eq!(history.min_since(5), Some(5));
        assert_eq!(history.min_since(6), Some(6));
        assert_eq!(history.min_since(7), Some(9));
    }

    #[test]
    fn revision_history_sequential() {
        let mut history = MinHistory::new();
        for i in 0..32 {
            history.push(i as u32);
            assert_eq!(history.min_since(i), Some(i as u32));
        }

        let mut history = MinHistory::new();
        for i in 0..32 {
            history.push(32 - i as u32);
            assert_eq!(history.min_since(i), Some(32 - i as u32));
        }
    }

    fn xorshift(state: &mut u32) -> u32 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *state = x;
        x
    }

    #[test]
    fn revision_history_random() {
        let count = 12703;
        let mut rng = 123;
        let values = (0..count).map(|_| xorshift(&mut rng)).collect::<Vec<_>>();

        let mut minimums = values.clone();
        let mut min = u32::MAX;
        for i in (0..count).rev() {
            min = std::cmp::min(minimums[i], min);
            minimums[i] = min;
        }

        let history = MinHistory::from_vec(values);

        for _ in 0..10 {
            for (i, &min) in minimums.iter().enumerate() {
                assert_eq!(history.min_since(i), Some(min));
            }
        }
    }
}
