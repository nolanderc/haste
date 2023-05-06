use std::{hash::Hash, sync::Mutex};

use hashbrown::raw::RawTable;

use crate::{runtime::StackId, Query};

use super::{SlotArena, SlotId};

pub struct HashLookup {
    shards: Vec<Mutex<Shard>>,
}

struct Shard {
    entries: RawTable<SlotId>,
    reserved: std::ops::Range<usize>,
}

impl Default for HashLookup {
    fn default() -> Self {
        let thread_count = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        let shard_count = (4 * thread_count).next_power_of_two();

        let mut shards = Vec::new();
        shards.resize_with(shard_count, || Mutex::new(Shard::new()));

        Self { shards }
    }
}

impl Shard {
    fn new() -> Self {
        Self {
            entries: RawTable::new(),
            reserved: 0..0,
        }
    }
}

impl HashLookup {
    pub(super) fn get_or_allocate<Q: Query>(
        &self,
        input: Q::Input,
        arena: &SlotArena<Q>,
        stack: impl FnOnce() -> StackId,
    ) -> LookupResult
    where
        Q::Input: Hash + Eq,
    {
        let hash = fxhash::hash64(&input);
        let shards = &self.shards;
        let index = shard_index(hash, shards.len());
        let mut shard = shards[index].lock().unwrap();

        if let Some(&id) = shard.entries.get(hash, |&id| unsafe {
            arena.get_input_unchecked(id) == &input
        }) {
            return LookupResult { id, claim: None };
        }

        let id = if let Some(index) = shard.reserved.next() {
            SlotId::new(index)
        } else {
            shard.reserved = arena.ids.allocate(1024);
            SlotId::new(shard.reserved.next().unwrap())
        };

        let stack = stack();

        unsafe {
            let slot = arena.slots.get_or_allocate(id.index());
            slot.init_claim(input, stack)
        }

        shard.entries.insert(hash, id, |&id| unsafe {
            fxhash::hash64(arena.get_input_unchecked(id))
        });

        LookupResult {
            id,
            claim: Some(stack),
        }
    }
}

pub(super) struct LookupResult {
    pub id: SlotId,
    pub claim: Option<StackId>,
}

fn shard_index(hash: u64, shard_count: usize) -> usize {
    let shard_bits = shard_count.trailing_zeros();
    // hashbrown uses the top 7 bits
    let top_bits = hash >> (64 - 7 - shard_bits);
    (top_bits as usize) & (shard_count - 1)
}
