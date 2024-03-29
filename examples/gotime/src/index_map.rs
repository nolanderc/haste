#![allow(dead_code)]

use hashbrown::raw::RawTable;

use fxhash::hash64;

use std::{borrow::Borrow, hash::Hash};

#[derive(Clone)]
pub struct IndexMap<K, V> {
    lookup: RawTable<u32>,
    entries: Vec<(K, V)>,
}

impl<K, V> Default for IndexMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> IndexMap<K, V> {
    pub const fn new() -> Self {
        Self {
            lookup: RawTable::new(),
            entries: Vec::new(),
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            lookup: RawTable::with_capacity(cap),
            entries: Vec::with_capacity(cap),
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Hash + Eq,
    {
        let hash = hash64(&key);

        if let Some(index) = self.find(hash, &key) {
            return Some(std::mem::replace(&mut self.entries[index].1, value));
        }

        self.insert_no_check(hash, key, value);
        None
    }

    fn insert_no_check(&mut self, hash: u64, key: K, value: V) -> usize
    where
        K: Hash,
    {
        let index = self.entries.len();
        self.entries.push((key, value));
        self.lookup
            .insert(hash, index as u32, Self::hash_fn(&self.entries));
        index
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Q: Borrow<K>,
        K: Hash + Eq,
    {
        let key = key.borrow();
        let hash = hash64(key);
        self.find(hash, key).is_some()
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Borrow<K>,
        K: Hash + Eq,
    {
        let key = key.borrow();
        let hash = hash64(key);
        let index = self.find(hash, key)?;
        Some(&self.entries[index].1)
    }

    pub fn find_index<Q>(&self, key: &Q) -> Option<usize>
    where
        Q: Borrow<K>,
        K: Hash + Eq,
    {
        let key = key.borrow();
        let hash = hash64(key);
        self.find(hash, key)
    }

    pub fn get_index(&self, index: usize) -> &V {
        &self.entries[index].1
    }

    pub fn get_or_insert_with(&mut self, key: K, init: impl FnOnce() -> V) -> &mut V
    where
        K: Hash + Eq,
    {
        let hash = hash64(&key);
        let index = match self.find(hash, &key) {
            Some(index) => index,
            None => self.insert_no_check(hash, key, init()),
        };
        &mut self.entries[index].1
    }

    fn find<'a>(&'a self, hash: u64, key: &'a K) -> Option<usize>
    where
        K: Eq,
    {
        let index = self.lookup.get(hash, self.eq_fn(key))?;
        Some(*index as usize)
    }

    fn eq_fn<'a>(&'a self, key: &'a K) -> impl Fn(&u32) -> bool + 'a
    where
        K: Eq,
    {
        move |&index| key == &self.entries[index as usize].0
    }

    fn hash_fn(entries: &[(K, V)]) -> impl Fn(&u32) -> u64 + '_
    where
        K: Hash,
    {
        move |&index| hash64(&entries[index as usize].0)
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&'_ K, &'_ V)> + ExactSizeIterator + '_ {
        self.entries.iter().map(|(key, value)| (key, value))
    }

    pub fn keys(&self) -> impl Iterator<Item = &'_ K> {
        self.entries.iter().map(|(key, _)| key)
    }

    pub fn values(&self) -> impl Iterator<Item = &'_ V> {
        self.entries.iter().map(|(_, value)| value)
    }

    pub fn shrink_to_fit(&mut self) {
        self.entries.shrink_to_fit();
    }

    pub fn map<U>(self, mut f: impl FnMut(V) -> U) -> IndexMap<K, U> {
        IndexMap {
            lookup: self.lookup,
            entries: self
                .entries
                .into_iter()
                .map(|(key, value)| (key, f(value)))
                .collect(),
        }
    }
}

impl<K, V> IntoIterator for IndexMap<K, V> {
    type Item = (K, V);
    type IntoIter = std::vec::IntoIter<(K, V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl<K, V> std::fmt::Debug for IndexMap<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V> PartialEq for IndexMap<K, V>
where
    K: Hash + Eq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.entries.len() != other.entries.len() {
            return false;
        }

        for (key, value) in self.iter() {
            if other.get(key) != Some(value) {
                return false;
            }
        }

        // the maps had the same number of items, and they all were equal.
        true
    }
}

impl<K, V> Eq for IndexMap<K, V>
where
    K: Hash + Eq,
    V: Eq,
{
}

impl<K, V> Hash for IndexMap<K, V>
where
    K: Hash,
    V: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.entries.hash(state)
    }
}

impl<K, V> FromIterator<(K, V)> for IndexMap<K, V>
where
    K: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut this = Self::new();
        for (key, value) in iter {
            this.insert(key, value);
        }
        this
    }
}

impl<K, V, Q> std::ops::Index<&Q> for IndexMap<K, V>
where
    Q: Borrow<K>,
    K: Hash + Eq,
{
    type Output = V;

    fn index(&self, index: &Q) -> &Self::Output {
        self.get(index).unwrap()
    }
}
