use std::{
    hash::{BuildHasher, Hash, Hasher},
    sync::RwLock,
};

use hashbrown::raw::RawTable;

type BuildHasherDefault = std::hash::BuildHasherDefault<ahash::AHasher>;

pub struct ShardMap<T, Hasher = BuildHasherDefault, const SHARDS: usize = 32> {
    shards: [Shard<T>; SHARDS],
    hasher: Hasher,
}

pub type Shard<T> = RwLock<RawTable<T>>;

impl<T, Hasher, const SHARDS: usize> Default for ShardMap<T, Hasher, SHARDS>
where
    Hasher: Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, Hasher, const SHARDS: usize> ShardMap<T, Hasher, SHARDS> {
    pub fn new() -> Self
    where
        Hasher: Default,
    {
        Self {
            shards: std::array::from_fn(|_| Shard::default()),
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
        let shard_bits = 8 * std::mem::size_of_val(&SHARDS) as u32 - SHARDS.leading_zeros();
        let shift_amount = (64 - 7) - shard_bits;
        ((hash >> shift_amount) % (SHARDS as u64)) as usize
    }

    pub fn shard(&self, hash: u64) -> &Shard<T> {
        &self.shards[self.shard_index(hash)]
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
