use std::num::NonZeroU32;

/// A `u32` with the inveriant that it can never be `u32::MAX`.
///
/// This is similar to a [`NonZeroU32`] in that it uses a specific bit-pattern for
/// niche-optimizations. That is, this type guarantees that
///
/// ```
/// # use std::mem::size_of;
/// # use haste::non_max::NonMaxU32;
/// assert_eq!(size_of::<NonMaxU32>(), size_of::<Option<NonMaxU32>>());
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NonMaxU32 {
    /// We use `NonZeroU32` for its special property that it has `0` as a niche. In order to use
    /// `u32::MAX` as the niche instead, we always store the bitwise-inverted value (ie. we flip
    /// all bits: 1s become 0s and 0s become 1s).
    inverted: NonZeroU32,
}

impl PartialOrd for NonMaxU32 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NonMaxU32 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.inverted.cmp(&self.inverted)
    }
}

impl std::fmt::Debug for NonMaxU32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl std::fmt::Display for NonMaxU32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl NonMaxU32 {
    pub const ZERO: Self = match Self::new(0) {
        Some(value) => value,
        None => unreachable!(),
    };

    pub const fn new(value: u32) -> Option<Self> {
        match NonZeroU32::new(!value) {
            None => None,
            Some(inverted) => Some(Self { inverted }),
        }
    }

    pub fn get(self) -> u32 {
        !self.inverted.get()
    }
}
