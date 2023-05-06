use std::hash::Hash;

use crate::{
    arena::Arena,
    runtime::StackId,
    shard::{self, ShardLookup},
    Query,
};

use super::{Slot, SlotId};

#[derive(Default)]
pub struct HashLookup {
    shards: ShardLookup,
}

impl HashLookup {
    pub(super) fn get_or_allocate<Q: Query>(
        &self,
        input: Q::Input,
        slots: &Arena<Slot<Q>>,
        stack: impl FnOnce() -> StackId,
    ) -> LookupResult
    where
        Q::Input: Hash + Eq,
    {
        #[inline(always)]
        unsafe fn get_input<Q: Query>(slots: &Arena<Slot<Q>>, index: u32) -> &Q::Input {
            slots.get_unchecked(index as usize).input_unchecked()
        }

        let result = self.shards.get_or_insert(
            fxhash::hash64(&input),
            |index| unsafe { get_input(slots, index) == &input },
            |index| unsafe { fxhash::hash64(get_input(slots, index)) },
        );

        match result {
            shard::LookupResult::Cached(existing) => LookupResult {
                id: SlotId(existing),
                claim: None,
            },
            shard::LookupResult::Insert(index, guard) => {
                let stack = stack();
                let slot = slots.get_or_allocate(index as usize);
                unsafe { slot.init_claim(input, stack) }

                drop(guard);

                LookupResult {
                    id: SlotId(index),
                    claim: Some(stack),
                }
            }
        }
    }
}

pub(super) struct LookupResult {
    pub id: SlotId,
    pub claim: Option<StackId>,
}
