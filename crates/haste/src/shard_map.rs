use std::{
    hash::{BuildHasher, Hash, Hasher},
    sync::Mutex,
};

use hashbrown::raw::RawTable;

type BuildHasherDefault = std::hash::BuildHasherDefault<ahash::AHasher>;

pub struct ShardMap<K, V, const SHARDS: usize = 8> {
    shards: [Shard<K, V>; SHARDS],
    hasher: BuildHasherDefault,
}

pub struct Shard<K, V> {
    table: Mutex<RawTable<Entry<K, V>>>,
}

impl<K, V> Shard<K, V> {
    pub fn raw(&self) -> &Mutex<RawTable<Entry<K, V>>> {
        &self.table
    }
}

impl<K, V> Default for Shard<K, V> {
    fn default() -> Self {
        Self {
            table: Default::default(),
        }
    }
}

pub struct Entry<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> Entry<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self { key, value }
    }
}

impl<K, V, const SHARDS: usize> Default for ShardMap<K, V, SHARDS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, const SHARDS: usize> ShardMap<K, V, SHARDS> {
    pub fn new() -> Self {
        Self {
            shards: std::array::from_fn(|_| Shard::default()),
            hasher: Default::default(),
        }
    }

    pub fn hash<T>(&self, value: &T) -> u64
    where
        T: Hash,
    {
        hash_one(value, &self.hasher)
    }

    pub fn shard_index(&self, hash: u64) -> usize {
        // get the highest bits of the hash to reduce the likelihood of hash collisions
        let shard_bits = 8 * std::mem::size_of_val(&SHARDS) as u32 - SHARDS.leading_zeros();
        let shift_amount = (64 - 7) - shard_bits;
        ((hash >> shift_amount) % (SHARDS as u64)) as usize
    }

    pub fn shard(&self, hash: u64) -> &Shard<K, V> {
        &self.shards[self.shard_index(hash)]
    }

    #[inline(always)]
    pub fn hash_fn(&self) -> impl Fn(&Entry<K, V>) -> u64 + '_
    where
        K: Hash,
    {
        move |entry| hash_one(&entry.key, &self.hasher)
    }

    #[inline(always)]
    pub fn eq_fn<'a>(&self, key: &'a K) -> impl Fn(&Entry<K, V>) -> bool + 'a
    where
        K: Eq,
    {
        move |entry| key == &entry.key
    }
}

/// Use a hasher to hash a single value.
fn hash_one<T: Hash>(key: &T, builder: &BuildHasherDefault) -> u64 {
    let mut state = builder.build_hasher();
    key.hash(&mut state);
    state.finish()
}
