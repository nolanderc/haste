use std::hash::{BuildHasher, Hash, Hasher};

use hashbrown::raw::RawTable;
use parking_lot::{MappedRwLockReadGuard, RwLock, RwLockReadGuard as ReadGuard};

type BuildHasherDefault = std::hash::BuildHasherDefault<ahash::AHasher>;

pub type EntryRef<'a, K, V> = MappedRwLockReadGuard<'a, Entry<K, V>>;

pub struct ShardMap<K, V, const SHARDS: usize = 16> {
    shards: [Shard<K, V>; SHARDS],
    hasher: BuildHasherDefault,
}

pub struct Shard<K, V> {
    table: RwLock<RawTable<Entry<K, V>>>,
}

impl<K, V> Shard<K, V> {
    pub fn raw(&self) -> &RwLock<RawTable<Entry<K, V>>> {
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
        (hash % (SHARDS as u64)) as usize
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

    #[allow(unused)]
    pub fn insert(&self, key: K, value: V) -> Option<V>
    where
        K: Hash + Eq,
    {
        let hash = self.hash(&key);
        let shard = self.shard(hash);
        let entry = Entry { key, value };

        let mut table = shard.table.write();
        match table.get_mut(hash, self.eq_fn(&entry.key)) {
            Some(old) => Some(std::mem::replace(old, entry).value),
            None => {
                table.insert_entry(hash, entry, self.hash_fn());
                None
            }
        }
    }

    #[allow(unused)]
    pub fn get(&self, key: &K) -> Option<EntryRef<K, V>>
    where
        K: Hash + Eq,
    {
        let hash = self.hash(key);
        let shard = self.shard(hash);

        let table = shard.table.read();
        ReadGuard::try_map(table, |table| table.get(hash, self.eq_fn(key))).ok()
    }
}

/// Use a hasher to hash a single value.
fn hash_one<T: Hash>(key: &T, builder: &BuildHasherDefault) -> u64 {
    let mut state = builder.build_hasher();
    key.hash(&mut state);
    state.finish()
}
