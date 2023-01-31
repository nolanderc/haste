#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]

mod arena;
mod input;
pub mod interner;
pub mod query_cache;
mod runtime;
mod shard_map;
mod storage;
pub mod util;

use std::future::Future;

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
///
/// # Safety
///
/// This trait is `unsafe` to implement because it requires the guarantee that the same runtime
/// will always be returned, and that the lifetime of the runtime is the lifetime of the database
/// storage. That is: the inner runtime and storage will only ever be accessed together.
pub unsafe trait Database: Sync {
    fn runtime(&self) -> &Runtime;
    fn runtime_mut(&mut self) -> &mut Runtime;
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
    type Input: 'static + Send;
    type Output: 'static + Send;
    type Future<'db>: std::future::Future<Output = Self::Output> + Send;

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
    type Value: ?Sized;

    type Ref<'a>: std::ops::Deref<Target = Self::Value>
    where
        Self: 'a;

    /// Add a new element to the container, returning its ID for future access
    fn insert(&self, value: Self::Value) -> Id
    where
        Self::Value: Sized;

    /// Get the element associated with the given ID without tracking any dependencies.
    fn get_untracked(&self, id: Id) -> Self::Ref<'_>;
}

/// Extends `ElementContainer` with methods for inserting references
pub trait ElementContainerRef: ElementContainer {
    /// Add a new element to the container, returning its ID for future access
    fn insert_ref(&self, value: &Self::Value) -> Id;
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

type ExecuteFuture<'db, DB: ?Sized, Q: Query>
where
    Q: Query,
    Q::Storage: 'db,
    Q::Container: QueryCache<Query = Q> + 'db,
    DB: WithStorage<Q::Storage>,
= impl Future<Output = &'db <Q as Query>::Output> + 'db;

type SpawnFuture<'db, DB: ?Sized, Q: Query>
where
    Q: Query,
    Q::Storage: 'db,
    Q::Container: QueryCache<Query = Q> + 'db,
    DB: WithStorage<Q::Storage>,
= impl Future<Output = &'db <Q as Query>::Output> + 'db;

/// Extends databases with generic methods for working with [`Ingredient`]s.
///
/// These cannot be included directly in [`Database`] as these methods are not object safe.
pub trait DatabaseExt: Database {
    /// Execute a query with some input, reusing previous results if possible.
    fn execute_cached<'db, Q>(&'db self, input: Q::Input) -> ExecuteFuture<'db, Self, Q>
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let db = self.as_dyn();
        let runtime = self.runtime();
        let storage = self.storage();
        let cache = storage.container();
        let result = cache.get_or_evaluate(db, input);

        async move {
            let id = match result {
                EvalResult::Cached(id) => id,
                EvalResult::Eval(eval) => eval.await,
                EvalResult::Pending(pending) => pending.await,
            };

            runtime.register_dependency(Dependency {
                ingredient: cache.path(),
                resource: id,
                extra: 0,
            });

            // SAFETY: we just executed this query, so the `id` will be valid.
            unsafe { cache.output(id) }
        }
    }

    /// Signals to the runtime that we might eventually need the output of the given query.
    ///
    /// This is intended to be used as an optimization, and is the core primitive for scheduling
    /// parallel work.
    fn spawn<'db, Q>(&'db self, input: Q::Input) -> SpawnFuture<'db, Self, Q>
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let db = self.as_dyn();
        let runtime = self.runtime();
        let storage = self.storage();
        let cache = storage.container();

        let result = match cache.get_or_evaluate(db, input) {
            EvalResult::Cached(id) => EvalResult::Cached(id),
            EvalResult::Eval(eval) => EvalResult::Eval(runtime.spawn_query(eval)),
            EvalResult::Pending(pending) => EvalResult::Pending(pending),
        };

        async move {
            let id = match result {
                EvalResult::Cached(id) => id,
                EvalResult::Eval(eval) => eval.await,
                EvalResult::Pending(pending) => pending.await,
            };

            runtime.register_dependency(Dependency {
                ingredient: cache.path(),
                resource: id,
                extra: 0,
            });

            // SAFETY: we just executed this query, so the `id` will be valid.
            unsafe { cache.output(id) }
        }
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
        let db = self.as_dyn();
        let storage = self.storage();
        let cache = storage.container();
        let result = cache.get_or_evaluate(db, input);

        match result {
            // the query is already computed/pending, so we are done here
            EvalResult::Cached(_) | EvalResult::Pending(_) => {}

            // the query must be evaluated, so spawn it in the runtime for concurrent processing
            EvalResult::Eval(eval) => {
                drop(db.runtime().spawn_query(eval));
            }
        }
    }

    fn insert<'db, T>(&'db self, value: <T::Container as ElementContainer>::Value) -> T
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainer + 'db,
        <T::Container as ElementContainer>::Value: Sized,
        Self: WithStorage<T::Storage>,
    {
        let storage = self.storage();
        let container = storage.container();
        let id = container.insert(value);
        T::from_id(id)
    }

    fn insert_ref<'db, T>(&'db self, value: &<T::Container as ElementContainer>::Value) -> T
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainerRef + 'db,
        Self: WithStorage<T::Storage>,
    {
        let storage = self.storage();
        let container = storage.container();
        let id = container.insert_ref(value);
        T::from_id(id)
    }

    fn lookup<'db, T>(&'db self, handle: T) -> <T::Container as ElementContainer>::Ref<'db>
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainer + 'db,
        Self: WithStorage<T::Storage>,
    {
        let runtime = self.runtime();
        let storage = self.storage();
        let container = storage.container();

        let id = handle.id();
        let value = container.get_untracked(id);
        runtime.register_dependency(Dependency {
            ingredient: container.path(),
            resource: id,
            extra: 0,
        });
        value
    }
}

impl<DB> DatabaseExt for DB where DB: Database + ?Sized {}

/// Enters a scope within which it is possible to execute queries on other threads.
pub fn scope<DB, F, T>(db: &mut DB, f: F) -> T
where
    F: FnOnce(Scope<'_>, &DB) -> T,
    DB: Database + ?Sized,
{
    let entered = unsafe { db.runtime_mut().enter() };

    let scope = Scope {
        runtime: db.runtime(),
    };

    let output = f(scope, db);

    if entered {
        // we were the ones responsible for calling `enter`, so we must also `exit`
        db.runtime_mut().exit();
    }

    output
}

pub struct Scope<'a> {
    runtime: &'a Runtime,
}

impl<'a> Scope<'a> {
    pub fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.runtime.block_on(f)
    }
}
