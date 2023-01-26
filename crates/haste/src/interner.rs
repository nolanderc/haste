use crate::{
    arena::Arena,
    non_max::NonMaxU32,
    shard_map::{Entry, ShardMap},
    IngredientPath,
};

use std::hash::Hash;

pub struct ArenaInterner<T> {
    path: IngredientPath,
    values: Arena<T>,
    entries: ShardMap<NonMaxU32, ()>,
}

impl<T> ArenaInterner<T> {
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
        let shard = self.entries.shard(hash).raw();

        {
            // check if the value already exists in the interner
            let table = shard.read().unwrap();
            if let Some(old) = table.get(hash, self.eq_fn(&value)) {
                return old.key;
            }
        }

        let mut table = shard.write().unwrap();
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

impl<T> crate::Container for ArenaInterner<T> {
    fn new(path: IngredientPath) -> Self {
        Self {
            path,
            values: Arena::new(),
            entries: ShardMap::new(),
        }
    }

    fn path(&self) -> IngredientPath {
        self.path
    }
}

impl<T> crate::ElementContainer for ArenaInterner<T>
where
    T: Eq + Hash,
{
    type Value = T;

    type Ref<'a> = &'a T
    where
        Self: 'a;

    fn insert(&self, value: T) -> crate::Id {
        crate::Id::new(self.intern(value))
    }

    fn get_untracked(&self, id: crate::Id) -> Self::Ref<'_> {
        self.get(id.raw).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::Container;

    use super::*;

    #[test]
    fn interning() {
        let mut router = crate::StorageRouter::new(1);
        let interner = ArenaInterner::new(router.next_ingredient());

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
