use crate::{shard_map::ShardLookup, Id, Query, TrackedReference};

use super::storage::{QuerySlot, QueryStorage};

use std::hash::Hash;

pub trait LookupStrategy<Q: Query>: Sync {
    /// Get the slot with the given input, or insert it if it does not exist.
    fn get_or_insert<'a>(
        &self,
        input: Q::Input,
        storage: &'a QueryStorage<Q>,
    ) -> (Id, &'a QuerySlot<Q>);

    /// Get the slot with the given input.
    fn get_mut<'a>(
        &mut self,
        input: &Q::Input,
        storage: &'a mut QueryStorage<Q>,
    ) -> Option<(Id, &'a mut QuerySlot<Q>)>;
}

/// Uses the hash of the input as the key.
#[derive(Default)]
pub struct HashStrategy {
    entries: ShardLookup,
}

impl<Q: Query> LookupStrategy<Q> for HashStrategy
where
    Q::Input: Hash + Eq,
{
    fn get_or_insert<'a>(
        &self,
        input: Q::Input,
        storage: &'a QueryStorage<Q>,
    ) -> (Id, &'a QuerySlot<Q>) {
        let hash = fxhash::hash64(&input);

        unsafe fn slot<Q: Query>(storage: &QueryStorage<Q>, index: u32) -> &QuerySlot<Q> {
            storage.get_slot_unchecked(Id::try_from_usize(index as usize).unwrap())
        }

        let result = self.entries.get_or_insert(
            hash,
            |index| unsafe { slot(storage, index).input_unchecked() == &input },
            |index| unsafe { fxhash::hash64(slot(storage, index).input_unchecked()) },
        );

        match result {
            crate::shard_map::ShardResult::Cached(index) => {
                let id = Id::try_from_usize(index as usize).unwrap();
                (id, unsafe { storage.get_slot_unchecked(id) })
            }
            crate::shard_map::ShardResult::Insert(index, _write_guard) => {
                let id = Id::try_from_usize(index as usize).unwrap();
                (id, storage.init_slot(id, input))
            }
        }
    }

    fn get_mut<'a>(
        &mut self,
        input: &<Q as Query>::Input,
        storage: &'a mut QueryStorage<Q>,
    ) -> Option<(Id, &'a mut QuerySlot<Q>)> {
        let hash = fxhash::hash64(input);
        let index = self.entries.get(hash, |index| unsafe {
            storage
                .get_slot_unchecked(Id::try_from_usize(index as usize).unwrap())
                .input_unchecked()
                == input
        })?;

        let id = Id::try_from_usize(index as usize).unwrap();

        Some((id, storage.slot_mut(id)))
    }
}

/// Uses the `Id` of the input as the key.
#[derive(Default)]
pub struct TrackedStrategy;

impl<Q: Query> LookupStrategy<Q> for TrackedStrategy
where
    Q::Input: TrackedReference + Copy,
{
    fn get_or_insert<'a>(
        &self,
        input: Q::Input,
        storage: &'a QueryStorage<Q>,
    ) -> (Id, &'a QuerySlot<Q>) {
        let id = input.id();
        let slot = storage.init_slot(id, input);
        (id, slot)
    }

    fn get_mut<'a>(
        &mut self,
        input: &<Q as Query>::Input,
        storage: &'a mut QueryStorage<Q>,
    ) -> Option<(Id, &'a mut QuerySlot<Q>)> {
        let id = input.id();
        let slot = storage.try_get_slot_mut(id)?;
        Some((id, slot))
    }
}
