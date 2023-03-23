use std::num::{NonZeroU16, NonZeroU32};

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
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct NonMaxU32 {
    /// We use `NonZeroU32` for its special property that it has `0` as a niche. In order to use
    /// `u32::MAX` as the niche instead, we always store the value `x` as `x + 1`.
    encoded: NonZeroU32,
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
        match value.checked_add(1) {
            None => None,
            Some(non_zero) => {
                // SAFETY: we just added 1 to `value` and checked for overflow, thus it cannot be
                // `0`
                let encoded = unsafe { NonZeroU32::new_unchecked(non_zero) };
                Some(Self { encoded })
            }
        }
    }

    pub fn get(self) -> u32 {
        self.encoded.get() - 1
    }
}

/// A `u16` with the inveriant that it can never be `u16::MAX`.
///
/// This is similar to a [`NonZeroU16`] in that it uses a specific bit-pattern for
/// niche-optimizations. That is, this type guarantees that
///
/// ```
/// # use std::mem::size_of;
/// # use haste::non_max::NonMaxU16;
/// assert_eq!(size_of::<NonMaxU16>(), size_of::<Option<NonMaxU16>>());
/// ```
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct NonMaxU16 {
    /// We use `NonZeroU16` for its special property that it has `0` as a niche. In order to use
    /// `u16::MAX` as the niche instead, we always store the value `x` as `x + 1`.
    encoded: NonZeroU16,
}

impl std::fmt::Debug for NonMaxU16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl std::fmt::Display for NonMaxU16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl NonMaxU16 {
    pub const ZERO: Self = match Self::new(0) {
        Some(value) => value,
        None => unreachable!(),
    };

    pub const fn new(value: u16) -> Option<Self> {
        match value.checked_add(1) {
            None => None,
            Some(non_zero) => {
                // SAFETY: we just added 1 to `value` and checked for overflow, thus it cannot be
                // `0`
                let encoded = unsafe { NonZeroU16::new_unchecked(non_zero) };
                Some(Self { encoded })
            }
        }
    }

    pub fn get(self) -> u16 {
        self.encoded.get() - 1
    }
}

/// A `u32`, but it only needs to be aligned to a single byte (instead of the usual 4).
///
/// This allows certain memory layout optimizations by the compiler.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct B32 {
    bytes: [u8; 4],
}

impl PartialOrd for B32 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.get().partial_cmp(&other.get())
    }
}

impl Ord for B32 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl std::fmt::Display for B32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl std::fmt::Debug for B32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl B32 {
    pub const fn new(x: u32) -> Self {
        Self {
            bytes: x.to_ne_bytes(),
        }
    }

    pub const fn get(self) -> u32 {
        u32::from_ne_bytes(self.bytes)
    }
}

impl From<u32> for B32 {
    fn from(value: u32) -> Self {
        Self::new(value)
    }
}

/// A `u16`, but it only needs to be aligned to a single byte (instead of the usual 4).
///
/// This allows certain memory layout optimizations by the compiler.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct B16 {
    bytes: [u8; 2],
}

impl PartialOrd for B16 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.get().partial_cmp(&other.get())
    }
}

impl Ord for B16 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl std::fmt::Display for B16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl std::fmt::Debug for B16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl B16 {
    pub const fn new(x: u16) -> Self {
        Self {
            bytes: x.to_ne_bytes(),
        }
    }

    pub const fn get(self) -> u16 {
        u16::from_ne_bytes(self.bytes)
    }
}

impl From<u16> for B16 {
    fn from(value: u16) -> Self {
        Self::new(value)
    }
}

/// A 24-bit unsigned integer.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct U24 {
    bytes: [u8; 3],
}

impl PartialOrd for U24 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.get().partial_cmp(&other.get())
    }
}

impl Ord for U24 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl std::fmt::Display for U24 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl std::fmt::Debug for U24 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get().fmt(f)
    }
}

impl U24 {
    pub const fn new(x: u32) -> Option<Self> {
        let [a, b, c, d] = x.to_le_bytes();
        if d != 0 {
            return None;
        }
        Some(Self { bytes: [a, b, c] })
    }

    pub const fn get(self) -> u32 {
        let [a, b, c] = self.bytes;
        u32::from_ne_bytes([a, b, c, 0])
    }
}
