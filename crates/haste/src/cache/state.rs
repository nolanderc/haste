use std::sync::atomic::{
    AtomicU64,
    Ordering::{self, Acquire, Relaxed, Release},
};

use crate::{revision::Revision, runtime::StackId};

use super::ClaimResult;

pub struct SlotState {
    /// `Parts` encoded in 64 bits
    bits: AtomicU64,
}

unsafe impl bytemuck::Zeroable for SlotState {}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(C)]
struct Parts {
    stack: Option<StackId>,
    last_verified_and_flags: u32,
}

unsafe impl bytemuck::Zeroable for Parts {}
unsafe impl bytemuck::Pod for Parts {}

impl Parts {
    fn new(stack: Option<StackId>, last_verified: Option<Revision>, flags: u32) -> Self {
        Self {
            stack,
            last_verified_and_flags: flags | Revision::encode_u32(last_verified),
        }
    }

    fn last_verified(self) -> Option<Revision> {
        unsafe { Revision::decode_u32_unchecked(self.last_verified_and_flags & !flags::MASK) }
    }

    fn flags(self) -> u32 {
        self.last_verified_and_flags & flags::MASK
    }
}

fn encode(parts: Parts) -> u64 {
    bytemuck::cast(parts)
}

fn decode(bits: u64) -> Parts {
    bytemuck::cast(bits)
}

mod flags {
    use crate::revision::Revision;

    /// Another thread is blocked on this result.
    pub const BLOCKING: u32 = 1 << 31;
    /// The query is part of a dependency cycle.
    pub const CYCLIC: u32 = 1 << 30;

    pub const MASK: u32 = BLOCKING | CYCLIC;

    #[allow(dead_code)]
    const _: () = assert!(
        Revision::MAX.index().get() & MASK == 0,
        "flags should not intersect revision range"
    );
}

impl SlotState {
    pub(super) fn init_claim(&mut self, current: StackId) {
        *self.bits.get_mut() = encode(Parts::new(Some(current), None, 0));
    }

    #[inline(always)]
    pub fn is_ready(&self, revision: Revision, order: Ordering) -> bool {
        let state = decode(self.bits.load(order));
        state.last_verified() >= Some(revision)
    }

    pub(super) fn claim(&self, stack: StackId, revision: Revision, block: bool) -> ClaimResult {
        let mut state = decode(self.bits.load(Acquire));

        loop {
            if state.last_verified() >= Some(revision) {
                return ClaimResult::Ready;
            }

            if let Some(id) = state.stack {
                if block {
                    let new_state = self.set_flag(flags::BLOCKING, Relaxed);
                    if new_state != state {
                        state = new_state;
                        continue;
                    }
                }

                return ClaimResult::Pending(id);
            }

            match self.bits.compare_exchange_weak(
                encode(state),
                encode(Parts {
                    stack: Some(stack),
                    ..state
                }),
                Relaxed,
                Acquire,
            ) {
                Ok(_) => return ClaimResult::Claimed(state.last_verified()),

                // another thread has claimed the query, it could have been verified
                Err(new) => state = decode(new),
            }
        }
    }

    pub(super) fn finish(&self, revision: Revision) -> FinishResult {
        let parts = decode(
            self.bits
                .swap(encode(Parts::new(None, Some(revision), 0)), Release),
        );

        FinishResult {
            has_blocking: parts.flags() & flags::BLOCKING != 0,
        }
    }

    fn set_flag(&self, flags: u32, order: Ordering) -> Parts {
        decode(self.bits.fetch_or(
            encode(Parts {
                stack: None,
                last_verified_and_flags: flags,
            }),
            order,
        ))
    }

    pub(super) fn last_verified(&mut self) -> Option<Revision> {
        decode(*self.bits.get_mut()).last_verified()
    }

    pub(crate) fn is_initialized(&self, order: Ordering) -> bool {
        self.bits.load(order) != 0
    }
}

pub struct FinishResult {
    pub has_blocking: bool,
}
