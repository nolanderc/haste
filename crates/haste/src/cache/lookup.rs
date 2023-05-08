use std::hash::Hash;

use crate::{
    arena::Arena,
    runtime::StackId,
    shard::{ShardLookup, ShardResult},
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
        args: Q::Arguments,
        slots: &Arena<Slot<Q>>,
        stack: impl FnOnce() -> Option<StackId>,
    ) -> LookupResult
    where
        Q::Arguments: Hash + Eq,
    {
        #[inline(always)]
        unsafe fn get_arguments<Q: Query>(slots: &Arena<Slot<Q>>, index: u32) -> &Q::Arguments {
            slots.get_unchecked(index as usize).arguments_unchecked()
        }

        let result = self.shards.get_or_insert(
            fxhash::hash64(&args),
            |index| unsafe { get_arguments(slots, index) == &args },
            |index| unsafe { fxhash::hash64(get_arguments(slots, index)) },
        );

        match result {
            ShardResult::Cached(existing) => LookupResult {
                id: SlotId(existing),
                claim: None,
            },
            ShardResult::Insert(index, guard) => {
                let slot = slots.get_or_allocate(index as usize);

                let stack = stack();
                if let Some(stack) = stack {
                    unsafe { slot.init_claim(args, stack) }
                } else {
                    unsafe { slot.init(args) }
                }

                drop(guard);

                LookupResult {
                    id: SlotId(index),
                    claim: stack,
                }
            }
        }
    }
}

pub(super) struct LookupResult {
    pub id: SlotId,
    pub claim: Option<StackId>,
}
