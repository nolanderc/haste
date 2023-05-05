use std::sync::atomic::{
    AtomicU32,
    Ordering::{Acquire, Relaxed, Release},
};

use super::ClaimResult;

pub struct SlotState {
    bits: AtomicU32,
}

unsafe impl bytemuck::Zeroable for SlotState {}

const HAS_OUTPUT: u32 = 0x1;
const CLAIMED: u32 = 0x2;

impl SlotState {
    pub(super) fn init_claim(&mut self) {
        *self.bits.get_mut() = CLAIMED;
    }

    pub(super) fn claim(&self) -> ClaimResult {
        let mut state = self.bits.load(Acquire);

        loop {
            if state & CLAIMED != 0 {
                return ClaimResult::Pending;
            }

            if state & HAS_OUTPUT != 0 {
                return ClaimResult::Ready;
            }

            match self
                .bits
                .compare_exchange_weak(state, CLAIMED, Relaxed, Acquire)
            {
                Ok(_) => return ClaimResult::Claimed,
                Err(new) => state = new,
            }
        }
    }

    pub(super) fn finish(&self) {
        self.bits.store(HAS_OUTPUT, Release);
    }
}
