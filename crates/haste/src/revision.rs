use std::{
    num::NonZeroU32,
    sync::atomic::{AtomicU32, Ordering},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Revision(NonZeroU32);

impl std::fmt::Debug for Revision {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Revision({})", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InputId(NonZeroU32);

impl std::fmt::Debug for InputId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "InputId({})", self.0)
    }
}

impl Revision {
    pub(crate) const fn new(x: u32) -> Option<Revision> {
        match NonZeroU32::new(x) {
            None => None,
            Some(val) => Some(Self(val)),
        }
    }

    pub(crate) fn index(self) -> u32 {
        self.0.get()
    }

    pub(crate) fn from_index(index: NonZeroU32) -> Revision {
        Revision(index)
    }
}

unsafe impl bytemuck::ZeroableInOption for Revision {}

fn to_u32(rev: Option<Revision>) -> u32 {
    rev.map(|x| x.0.get()).unwrap_or(0)
}

#[derive(Debug, bytemuck::Zeroable)]
pub struct AtomicRevision(AtomicU32);

impl AtomicRevision {
    pub fn load(&self, order: Ordering) -> Option<Revision> {
        Self::from_u32(self.0.load(order))
    }

    pub fn store(&self, rev: Option<Revision>, order: Ordering) {
        self.0.store(to_u32(rev), order)
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
