use parking_lot::RwLockUpgradableReadGuard;

use crate::{
    arena::Arena,
    non_max::NonMaxU32,
    shard_map::{Entry, ShardMap},
};

use std::hash::Hash;

pub struct ArenaInterner<T> {
    values: Arena<T>,
    entries: ShardMap<NonMaxU32, ()>,
}

impl<T> Default for ArenaInterner<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> ArenaInterner<T> {
    pub fn new() -> Self {
        Self {
            values: Arena::new(),
            entries: ShardMap::new(),
        }
    }

    fn eq_fn<'a>(&'a self, value: &'a T) -> impl Fn(&Entry<NonMaxU32, ()>) -> bool + 'a
    where
        T: Eq,
    {
        move |entry| &self.values[entry.key.get() as usize] == value
    }

    fn hash_fn(&self) -> impl Fn(&Entry<NonMaxU32, ()>) -> u64 + '_
    where
        T: Hash,
    {
        move |entry| self.entries.hash(self.get(entry.key).unwrap())
    }

    /// Get a value in the interner.
    ///
    /// Returns `None` if the index has not previously been returned by [`Self::intern`].
    pub fn get(&self, index: NonMaxU32) -> Option<&T> {
        self.values.get(index.get() as usize)
    }

    /// Insert a new value into the interner, returning its index
    pub fn intern(&self, value: T) -> NonMaxU32
    where
        T: Hash + Eq,
    {
        let hash = self.entries.hash(&value);
        let shard = self.entries.shard(hash);

        // check if the value already exists in the interner
        let table = shard.raw().upgradable_read();
        if let Some(old) = table.get(hash, self.eq_fn(&value)) {
            return old.key;
        }

        // get a write lock on the table, allowing us to insert the new value
        let mut table = RwLockUpgradableReadGuard::upgrade(table);

        // check for race condition, in case another thread managed to insert this value while we
        // upgraded our read lock to a write lock.
        if let Some(old) = table.get(hash, self.eq_fn(&value)) {
            return old.key;
        }

        // add the value into the interner, returing its key
        let index = self.values.push(value);
        let key = NonMaxU32::new(index.try_into().unwrap()).expect("interner memory");
        let entry = Entry { key, value: () };
        table.insert_entry(hash, entry, self.hash_fn());
        key
    }
}

impl<T> crate::Interner<T> for ArenaInterner<T>
where
    T: Eq + Hash,
{
    type Value<'a> = &'a T
    where
        Self: 'a;

    fn intern(&self, value: T) -> crate::Id {
        crate::Id::new(self.intern(value))
    }

    fn get(&self, id: crate::Id) -> Self::Value<'_> {
        self.get(id.raw).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interning() {
        let interner = ArenaInterner::new();

        let a = interner.intern("hello");
        let b = interner.intern("bye");
        let c = interner.intern("hello");

        assert_eq!(a, c);

        assert_ne!(b, a);
        assert_ne!(b, c);

        assert_eq!(interner.get(a), Some(&"hello"));
        assert_eq!(interner.get(b), Some(&"bye"));
        assert_eq!(interner.get(c), Some(&"hello"));
    }
}
