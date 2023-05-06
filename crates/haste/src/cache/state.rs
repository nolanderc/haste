use std::sync::atomic::{
    AtomicU64,
    Ordering::{self, Acquire, Relaxed, Release},
};

use crate::runtime::StackId;

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
    last_verified: u16,
    flags: u16,
}

unsafe impl bytemuck::Zeroable for Parts {}
unsafe impl bytemuck::Pod for Parts {}

fn encode(parts: Parts) -> u64 {
    bytemuck::cast(parts)
}

fn decode(bits: u64) -> Parts {
    bytemuck::cast(bits)
}

mod flags {
    /// Another thread is blocked on this result
    pub const BLOCKING: u16 = 0x1;
}

impl SlotState {
    pub(super) fn init_claim(&mut self, current: StackId) {
        *self.bits.get_mut() = encode(Parts {
            stack: Some(current),
            last_verified: 0,
            flags: 0,
        });
    }

    pub fn is_ready(&self) -> bool {
        let state = decode(self.bits.load(Acquire));
        // TODO: compare against the current revision
        state.last_verified != 0
    }

    pub(super) fn claim(&self, current: StackId, block: bool) -> ClaimResult {
        let mut state = decode(self.bits.load(Acquire));

        loop {
            // TODO: compare against the current revision
            if state.last_verified != 0 {
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
                    stack: Some(current),
                    ..state
                }),
                Relaxed,
                Acquire,
            ) {
                Ok(_) => return ClaimResult::Claimed,

                // another thread has claimed the query, it could have been verified
                Err(new) => state = decode(new),
            }
        }
    }

    pub(super) fn finish(&self) -> FinishResult {
        let parts = decode(self.bits.swap(
            encode(Parts {
                stack: None,
                // TODO: insert the current revision
                last_verified: 1,
                flags: 0,
            }),
            Release,
        ));

        FinishResult {
            has_blocking: parts.flags & flags::BLOCKING != 0,
        }
    }

    fn set_flag(&self, flags: u16, order: Ordering) -> Parts {
        decode(self.bits.fetch_or(
            encode(Parts {
                flags,
                ..bytemuck::Zeroable::zeroed()
            }),
            order,
        ))
    }
}

pub struct FinishResult {
    pub has_blocking: bool,
}
