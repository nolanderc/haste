use std::num::NonZeroU32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Revision(NonZeroU32);

impl Revision {
    pub const MAX: Revision = Revision(unsafe { NonZeroU32::new_unchecked(u32::MAX >> 2) });

    pub(crate) const fn new(index: NonZeroU32) -> Option<Self> {
        if index.get() > Self::MAX.0.get() {
            return None;
        }
        Some(Self(index))
    }

    pub(crate) const fn index(self) -> NonZeroU32 {
        self.0
    }

    pub(crate) const fn encode_u32(this: Option<Self>) -> u32 {
        unsafe { std::mem::transmute(this) }
    }

    pub(crate) const unsafe fn decode_u32_unchecked(value: u32) -> Option<Self> {
        std::mem::transmute(value)
    }
}
