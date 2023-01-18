#![feature(type_alias_impl_trait)]
#![feature(async_fn_in_trait)]

mod arena;
mod input;
pub mod interner;
pub mod query_cache;
mod runtime;
mod shard_map;
mod storage;

pub use haste_macros::*;
pub use query_cache::*;
pub use runtime::*;
pub use storage::*;

pub mod non_max;

use non_max::NonMaxU32;

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

/// Implemented by databases which contain a specific type of storage.
pub trait WithStorage<S: Storage + ?Sized>: Database {
    fn as_dyn(&self) -> &S::DynDatabase;
    fn storage(&self) -> &S;
    fn storage_mut(&mut self) -> &mut S;
}

pub trait Ingredient {
    /// The storage within which this ingredient exists.
    type Storage: Storage + HasIngredient<Self>;

    /// Type which contains all information required by the ingredient.
    type Container: Container;
}

/// The database required by some database
type IngredientDatabase<T> = <<T as Ingredient>::Storage as Storage>::DynDatabase;

pub trait TrackedReference {
    fn from_id(id: Id) -> Self;
    fn id(self) -> Id;
}

/// Implemented by storages which has a contoiner for the given ingredient.
pub trait HasIngredient<T: Ingredient + ?Sized>: Storage {
    fn container(&self) -> &T::Container;
    fn container_mut(&mut self) -> &mut T::Container;
}

pub trait Query: Ingredient {
    type Input;
    type Output;
    type Future<'db>: std::future::Future<Output = Self::Output>;

    fn execute(db: &IngredientDatabase<Self>, input: Self::Input) -> Self::Future<'_>;
}

pub trait Intern: Ingredient + TrackedReference
where
    Self::Container: ElementContainer,
    <Self::Container as ElementContainer>::Value: Eq + std::hash::Hash,
{
}

pub trait Input: Ingredient + TrackedReference
where
    Self::Container: InputContainer,
{
}

/// A container that stores values (elements) which are accessed by an ID.
pub trait ElementContainer: Container {
    type Value;

    type Ref<'a>: std::ops::Deref<Target = Self::Value>
    where
        Self: 'a;

    /// Add a new element to the container, returning its ID for future access
    fn insert(&self, value: Self::Value) -> Id;

    /// Get the element associated with the given ID without tracking any dependencies.
    fn get_untracked(&self, id: Id) -> Self::Ref<'_>;

    /// Get the element associated with the given ID and also add it as a dependency for the
    /// current query.
    fn get(&self, id: crate::Id, runtime: &Runtime) -> Self::Ref<'_> {
        let value = self.get_untracked(id);
        runtime.register_dependency(Dependency {
            ingredient: self.path(),
            resource: id,
            extra: 0,
        });
        value
    }
}

/// A container which can store the inputs to the database. This requires the ability to modify
/// elements stored within and some degree of change detection.
pub trait InputContainer: ElementContainer {
    type RefMut<'a>: std::ops::DerefMut<Target = Self::Value>
    where
        Self: 'a;

    /// Get mutable access to some element.
    fn get_mut(&mut self, id: crate::Id) -> Self::RefMut<'_>;
}

/// Represents a query that has been spawned in a runtime.
pub struct Spawned<'db, Q: Query> {
    /// This is just a dummy implementation that evaluates the result straight away.
    output: &'db Q::Output,
}

impl<'db, Q: Query> Spawned<'db, Q> {
    /// Wait for the result of the query to become available.
    pub fn join(self) -> &'db Q::Output {
        self.output
    }
}

/// Extends databases with generic methods for working with [`Ingredient`]s.
///
/// These cannot be included directly in [`Database`] as these methods are not object safe.
pub trait DatabaseExt: Database {
    /// Execute a query with some input, reusing previous results if possible.
    async fn execute_cached<'db, Q>(&'db self, input: Q::Input) -> &'db Q::Output
    where
        Q: Query,
        Q::Output: 'db,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let db = self.as_dyn();
        let storage = self.storage();
        let cache = storage.container();
        let id = cache.evaluate(db, input).await;

        // SAFETY: we just executed this query, so the `id` will be valid.
        unsafe { cache.get_output(id, db.runtime()) }
    }

    /// Signals to the runtime that we might eventually need the output of the given query.
    ///
    /// This is intended to be used as an optimization, and is the core primitive for scheduling
    /// parallel work.
    fn prefetch<'db, Q>(&'db self, input: Q::Input)
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        // let runtime = self.runtime();
        // let storage = self.storage();
        // let cache = storage.container();
        // cache.path();
        //
        // // TODO: perform this work on another thread/node
        // let db = self.as_dyn();
        // cache.evaluate(db, input);
    }

    fn insert<'db, T>(&'db self, value: <T::Container as ElementContainer>::Value) -> T
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainer + 'db,
        Self: WithStorage<T::Storage>,
    {
        let storage = self.storage();
        let container = storage.container();
        let id = container.insert(value);
        T::from_id(id)
    }

    fn lookup<'db, T>(&'db self, handle: T) -> <T::Container as ElementContainer>::Ref<'db>
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainer + 'db,
        Self: WithStorage<T::Storage>,
    {
        let id = handle.id();
        let storage = self.storage();
        let container = storage.container();
        container.get(id, self.runtime())
    }

    fn input_mut_untracked<'db, T>(
        &'db mut self,
        input: T,
    ) -> <T::Container as InputContainer>::RefMut<'db>
    where
        T: Input,
        T::Storage: 'db,
        T::Container: InputContainer + 'db,
        Self: WithStorage<T::Storage>,
    {
        let id = input.id();
        let storage = self.storage_mut();
        let contanier = storage.container_mut();
        contanier.get_mut(id)
    }
}

impl<DB> DatabaseExt for DB where DB: Database + ?Sized {}
