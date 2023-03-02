use crate::{shard_map::ShardMap, Id, Query, TrackedReference};

use super::storage::{QuerySlot, QueryStorage};

use std::hash::Hash;

pub trait LookupStrategy<Q: Query>: Sync {
    fn get_or_insert<'a>(
        &self,
        input: Q::Input,
        storage: &'a QueryStorage<Q>,
    ) -> (Id, &'a QuerySlot<Q>);
}

/// Uses the hash of the input as the key.
#[derive(Default)]
pub struct HashStrategy {
    entries: ShardMap<Id>,
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
        let eq_fn = |key: &Id| {
            // SAFETY: all entries are valid
            let slot = unsafe { storage.get_slot_unchecked(*key) };
            *slot.input() == input
        };

        let hash = self.entries.hash(&input);

        // First check if the value already exists.
        let shard = self.entries.shard(hash).read().unwrap();
        if let Some(&id) = shard.get(hash, eq_fn) {
            return (id, unsafe { storage.get_slot_unchecked(id) });
        }

        let len_before = shard.len();
        drop(shard);

        let mut shard = self.entries.shard(hash).write().unwrap();
        let len_after = shard.len();

        // Make sure the value was not inserted while we waited on the write lock
        if len_before != len_after {
            // a value has been inserted (we never remove values, so the comparison above is sound)
            if let Some(&id) = shard.get(hash, eq_fn) {
                return (id, unsafe { storage.get_slot_unchecked(id) });
            }
        }

        let (id, slot) = storage.allocate_slot(input);

        shard.insert(hash, id, |key| {
            // SAFETY: all IDs in the cache are valid
            let slot = unsafe { storage.get_slot_unchecked(*key) };
            self.entries.hash(slot.input())
        });

        (id, slot)
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
}
