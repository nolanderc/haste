use non_max::NonMaxU32;

mod arena;
pub mod interner;
pub mod query_cache;
mod shard_map;

pub use haste_macros::*;

pub mod non_max;

#[derive(Default)]
pub struct Runtime {}

/// A generic value that uniquely identifies a resource within some ingredient.
///
/// Note that misuse of this value (such as using the same ID for different ingredients) may have
/// adverse affects, such as inconsistent results and crashes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id {
    pub(crate) raw: NonMaxU32,
}

impl Id {
    pub(crate) fn new(raw: NonMaxU32) -> Self {
        Self { raw }
    }

    pub(crate) fn try_from_usize(index: usize) -> Option<Self> {
        Some(Self::new(NonMaxU32::new(u32::try_from(index).ok()?)?))
    }
}

/// A database contains storage for all the ingredients in the query system, and provides a handle
/// to the runtime.
pub trait Database {
    fn runtime(&self) -> &Runtime;
}

/// Stores the containers for all ingredients in a database.
pub trait Storage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized;
}

/// Implemented by databases which contain a specific type of storage.
pub trait HasStorage<S: Storage>: Database {
    fn storage(&self) -> &S;
    fn as_dyn(&self) -> &S::DynDatabase;
}

pub trait Ingredient {
    /// Type which contains all information required by the ingredient.
    type Container;

    /// The storage within which this ingredient exists.
    type Storage: Storage<DynDatabase = Self::Database> + HasIngredient<Self>;

    /// The database object used by this ingredient (eg. `dyn crate::Db`).
    type Database: Database + HasStorage<Self::Storage> + ?Sized;
}

/// Implemented by storages which has a contoiner for the given ingredient.
pub trait HasIngredient<T: Ingredient + ?Sized>: Storage {
    fn container(&self) -> &T::Container;
}

pub trait Query: Ingredient {
    type Input;
    type Output;

    fn execute(db: &Self::Database, input: Self::Input) -> Self::Output;
}

pub trait QueryCache<Q: Query> {
    fn get_or_execute<'a>(&'a self, db: &Q::Database, input: Q::Input) -> &'a Q::Output;
}

pub trait Intern: Ingredient {
    type Value: Eq + std::hash::Hash;

    fn from_id(id: Id) -> Self;
    fn id(self) -> Id;
}

pub trait Interner<T> {
    type Value<'a>: std::ops::Deref<Target = T>
    where
        Self: 'a;

    fn intern(&self, value: T) -> Id;
    fn get(&self, id: Id) -> Self::Value<'_>;
}

/// Extends databases with methods for working with [`Ingredient`]s
pub trait DatabaseExt: Database {
    fn intern<T>(&self, value: T::Value) -> T
    where
        T: Intern,
        T::Container: Interner<T::Value>,
        Self: HasStorage<T::Storage>,
    {
        let storage = self.storage();
        let interner = storage.container();
        let id = interner.intern(value);
        T::from_id(id)
    }

    fn intern_lookup<'db, T>(
        &'db self,
        interned: T,
    ) -> <T::Container as Interner<T::Value>>::Value<'db>
    where
        T: Intern,
        T::Storage: 'db,
        T::Container: Interner<T::Value> + 'db,
        Self: HasStorage<T::Storage>,
    {
        let id = interned.id();
        let storage = self.storage();
        let interner = storage.container();
        interner.get(id)
    }

    fn execute_cached<'db, Q>(&'db self, input: Q::Input) -> &'db Q::Output
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Q> + 'db,
        Self: HasStorage<Q::Storage>,
    {
        let db = self.as_dyn();
        let storage = self.storage();
        let cache = storage.container();
        cache.get_or_execute(db, input)
    }
}

impl<DB> DatabaseExt for DB where DB: Database + ?Sized {}
