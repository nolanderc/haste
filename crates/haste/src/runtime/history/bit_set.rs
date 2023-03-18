use std::ops::RangeBounds;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitSet {
    bits: u64,
}

impl BitSet {
    pub const BITS: usize = 64;

    pub const fn new() -> Self {
        Self { bits: 0 }
    }

    pub fn insert(&mut self, index: u32) {
        self.bits |= 1 << index;
    }

    pub fn contains(&self, index: u32) -> bool {
        self.bits & (1 << index) != 0
    }

    pub fn contains_range(&self, range: impl RangeBounds<u32>) -> bool {
        let min = match range.start_bound() {
            std::ops::Bound::Included(x) => *x,
            std::ops::Bound::Excluded(x) => *x + 1,
            std::ops::Bound::Unbounded => 0,
        };
        let max = match range.end_bound() {
            std::ops::Bound::Included(x) => *x,
            std::ops::Bound::Excluded(0) => return false,
            std::ops::Bound::Excluded(x) => *x - 1,
            std::ops::Bound::Unbounded => u32::MAX,
        };

        if min >= 64 {
            return false;
        }

        let len = max - min + 1;
        let mask = if len >= 64 { u64::MAX } else { (1 << len) - 1 };

        (self.bits >> min) & mask != 0
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.bits == 0
    }

    pub(crate) fn iter(self) -> impl Iterator<Item = u32> {
        let mut bits = self.bits;
        std::iter::from_fn(move || {
            if bits == 0 {
                return None;
            }

            let offset = bits.trailing_zeros();
            bits ^= 1 << offset;
            Some(offset)
        })
    }
}

/// A bitset over a small range of indices.
//
// Invariants:
//
// - if `bits == 0` then `first == 0`
// - if `first > 0` then `bits & 1 == 1`
// - if `(bits >> i) & 1 == 1` then `first + i` is in the set.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct RangeBitSet {
    /// Value of the first index in the bitset.
    first: u32,
    /// Bit `i` in this determines if `first + i` is in the set or not.
    bits: u64,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BitSetFull;

impl std::fmt::Debug for BitSetFull {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "index falls outside active range of bitset")
    }
}

impl RangeBitSet {
    pub const BITS: usize = 64;

    pub const fn new() -> Self {
        Self { first: 0, bits: 0 }
    }

    /// Attempts to insert an index into the bitset, returning `Err` if the index does not fit.
    pub fn insert(&mut self, index: u32) -> Result<(), BitSetFull> {
        if self.bits == 0 {
            // the set is empty, so we can just insert
            self.first = index;
            self.bits = 1;
            return Ok(());
        }

        // if `index >= first`;
        let i = index.wrapping_sub(self.first);
        if i < Self::BITS as u32 {
            // set the appropriate bit
            self.bits |= 1 << i;
            return Ok(());
        }

        // if `index < first`;
        let i = self.first.wrapping_sub(index);
        if i < Self::BITS as u32 {
            // move the other bits up so that we can fit the new index
            let rotated_bits = self.bits << i;
            if self.bits != rotated_bits >> i {
                // could not shift without losing information
                return Err(BitSetFull);
            }

            self.first = index;
            self.bits = 1 | rotated_bits;
            return Ok(());
        }

        Err(BitSetFull)
    }

    pub fn contains(&self, index: u32) -> bool {
        let Some(i) = index.checked_sub(self.first) else { return false };
        if i >= Self::BITS as u32 {
            return false;
        }
        self.bits & (1 << i) != 0
    }

    pub fn contains_range(&self, range: impl RangeBounds<u32>) -> bool {
        let min = match range.start_bound() {
            std::ops::Bound::Included(x) => *x,
            std::ops::Bound::Excluded(x) => *x + 1,
            std::ops::Bound::Unbounded => 0,
        };
        let max = match range.end_bound() {
            std::ops::Bound::Included(x) => *x,
            std::ops::Bound::Excluded(0) => return false,
            std::ops::Bound::Excluded(x) => *x - 1,
            std::ops::Bound::Unbounded => u32::MAX,
        };

        let start = std::cmp::max(self.first, min);
        let end = std::cmp::min(self.first.saturating_add(Self::BITS as u32 - 1), max);

        if end < start {
            return false;
        }

        let i = start - self.first;
        let len = end - start + 1;
        let mask = if len == 64 { u64::MAX } else { (1 << len) - 1 };

        (self.bits >> i) & mask != 0
    }

    pub fn first(&self) -> Option<u32> {
        if self.bits == 0 {
            None
        } else {
            Some(self.first)
        }
    }

    pub(crate) fn raw_bits(&self) -> BitSet {
        BitSet { bits: self.bits }
    }

    /// Creates two bit sets such that the first ends right before `mid`, and the second starts
    /// with `mid`.
    pub(crate) fn split_at_raw(&self, mid: u32) -> (BitSet, BitSet) {
        // i: 9 8 7 6 5 4 3 2 1 0
        //          ^-mid       ^-first
        let i = mid.wrapping_sub(self.first);
        debug_assert!(i <= Self::BITS as u32);

        // we may not shift by 64, so treat special cases here:
        if i == 0 {
            return (BitSet { bits: 0 }, BitSet { bits: self.bits });
        }
        if i == Self::BITS as u32 {
            return (BitSet { bits: self.bits }, BitSet { bits: 0 });
        }

        let left_bits = self.bits << (Self::BITS as u32 - i);
        let right_bits = self.bits >> i;

        (BitSet { bits: left_bits }, BitSet { bits: right_bits })
    }

    pub(crate) fn iter(self) -> impl Iterator<Item = u32> {
        BitSet { bits: self.bits }
            .iter()
            .map(move |i| self.first + i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_bitset() {
        let mut set = RangeBitSet::new();
        assert_eq!(set.insert(1), Ok(()));
        assert_eq!(set.insert(3), Ok(()));
        assert_eq!(set.insert(7), Ok(()));
        assert_eq!(set.insert(1234), Err(BitSetFull));

        assert_eq!(set.first, 1);
        assert_eq!(set.bits, (1 << 0) | (1 << 2) | (1 << 6));

        assert!(set.contains(1));
        assert!(set.contains(3));
        assert!(set.contains(7));

        assert!(!set.contains(0));
        assert!(!set.contains(2));
        assert!(!set.contains(4));
        assert!(!set.contains(5));
        assert!(!set.contains(6));
        assert!(!set.contains(8));
        assert!(!set.contains(1023));

        assert!(set.contains_range(..));
        assert!(set.contains_range(2..=5));
        assert!(set.contains_range(7..=7));

        assert!(!set.contains_range(0..=0));
        assert!(!set.contains_range(4..=6));
        assert!(!set.contains_range(64..=66));
        assert!(!set.contains_range(65..=66));
    }
}
