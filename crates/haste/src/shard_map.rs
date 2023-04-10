use dashmap::RwLock;
use std::{
    hash::{BuildHasher, Hash, Hasher},
    sync::atomic::AtomicUsize,
};

use crossbeam_utils::CachePadded;
use hashbrown::raw::RawTable;

type BuildHasherDefault = std::hash::BuildHasherDefault<ahash::AHasher>;

pub struct ShardMap<T, Hasher = BuildHasherDefault> {
    pub(crate) shards: Box<[CachePadded<Shard<T>>]>,
    hasher: Hasher,
}

pub type Shard<T> = RwLock<RawTable<T>>;

impl<T, Hasher> Default for ShardMap<T, Hasher>
where
    Hasher: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

static SHARDS: AtomicUsize = AtomicUsize::new(0);

fn get_shard_count() -> usize {
    let old = SHARDS.load(std::sync::atomic::Ordering::Relaxed);
    if old != 0 {
        return old;
    }

    let threads = 1 + crate::runtime::executor::worker_threads();

    let shard_count = (4 * threads).next_power_of_two();
    SHARDS.store(shard_count, std::sync::atomic::Ordering::Relaxed);
    shard_count
}

impl<T, Hasher> ShardMap<T, Hasher> {
    pub fn new() -> Self
    where
        Hasher: Default,
    {
        let shard_count = get_shard_count();
        let mut shards = Vec::with_capacity(shard_count);

        for _ in 0..shard_count {
            shards.push(CachePadded::new(Shard::new(RawTable::with_capacity(64))));
        }

        assert!(shards.len().is_power_of_two());

        Self {
            shards: shards.into(),
            hasher: Default::default(),
        }
    }

    pub fn hash<U: ?Sized>(&self, value: &U) -> u64
    where
        U: Hash,
        Hasher: BuildHasher,
    {
        hash_one(value, &self.hasher)
    }

    pub fn shard_index(&self, hash: u64) -> usize {
        // get the highest bits of the hash to reduce the likelihood of hash collisions
        let shards = self.shards.len();
        let shard_bits = shards.ilog2();
        let shift_amount = (64 - 7) - shard_bits;
        (hash as usize >> shift_amount) & (shards - 1)
    }

    pub fn shard(&self, hash: u64) -> &Shard<T> {
        &self.shards[self.shard_index(hash)]
    }

    pub fn shard_mut(&mut self, hash: u64) -> &mut Shard<T> {
        &mut self.shards[self.shard_index(hash)]
    }
}

/// Use a hasher to hash a single value.
fn hash_one<T: Hash + ?Sized, Hasher>(key: &T, builder: &Hasher) -> u64
where
    Hasher: BuildHasher,
{
    let mut state = builder.build_hasher();
    key.hash(&mut state);
    state.finish()
}
