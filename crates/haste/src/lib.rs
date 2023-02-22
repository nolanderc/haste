#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![allow(clippy::uninlined_format_args)]

mod arena;
pub mod fmt;
mod input;
pub mod interner;
pub mod query_cache;
mod runtime;
mod shard_map;
mod storage;
pub mod util;

use std::{any::TypeId, future::Future};

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
pub trait Database: Sync {
    fn as_dyn(&self) -> &dyn Database;

    fn runtime(&self) -> &Runtime;

    fn storage_list(&self) -> &dyn DynStorageList;

    /// Gets the storage of the given type.
    fn dyn_storage(&self, typ: TypeId) -> Option<&dyn DynStorage> {
        self.storage_list().get(typ)
    }

    /// Gets the storage for the given ingredient.
    fn dyn_storage_path(&self, path: ContainerPath) -> Option<&dyn DynStorage> {
        self.storage_list().get_path(path)
    }

    /// Gets the container for the given ingredient.
    fn dyn_container_path(&self, path: ContainerPath) -> Option<&dyn DynContainer> {
        self.dyn_storage_path(path)?.dyn_container_path(path)
    }
}

pub trait StaticDatabase: Database {
    /// A type containing all the storages used by a database.
    type StorageList: StorageList;

    fn storage(&self) -> &DatabaseStorage<Self>;

    fn storage_mut(&mut self) -> &mut DatabaseStorage<Self>;
}

/// Implemented by databases which contain a specific type of storage.
pub trait WithStorage<S: Storage + ?Sized>: Database {
    fn cast_dyn(&self) -> &S::DynDatabase;
    fn storage(&self) -> &S;
}

pub trait Ingredient: 'static {
    /// The storage within which this ingredient exists.
    type Storage: Storage + HasIngredient<Self>;

    /// Type which contains all information required by the ingredient.
    type Container: Container;
}

/// The database required by some database
type DatabaseFor<T> = <<T as Ingredient>::Storage as Storage>::DynDatabase;

/// Implemented by storages which has a contoiner for the given ingredient.
pub trait HasIngredient<T: Ingredient + ?Sized>: Storage {
    fn container(&self) -> &T::Container;
    fn container_mut(&mut self) -> &mut T::Container;
}

pub trait TrackedReference {
    fn from_id(id: Id) -> Self;
    fn id(self) -> Id;
}

pub trait Intern: Ingredient + TrackedReference
where
    Self::Container: ElementContainer,
    <Self::Container as ElementContainer>::Value: Eq + std::hash::Hash,
{
}

pub trait Query: Ingredient {
    type Input: Clone + Send + 'static;
    type Output: Send + Sync + 'static;
    type Future<'db>: std::future::Future<Output = Self::Output> + Send;
    type RecoverFuture<'db>: std::future::Future<Output = Self::Output> + Send;

    fn fmt(input: &Self::Input, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn execute(db: &DatabaseFor<Self>, input: Self::Input) -> Self::Future<'_>;

    const CYCLE_STRATEGY: CycleStrategy;

    fn recover_cycle(
        db: &DatabaseFor<Self>,
        cycle: Cycle,
        input: Self::Input,
    ) -> Self::RecoverFuture<'_> {
        _ = input;
        panic!(
            "encountered a dependency cycle: {:#}",
            cycle.fmt(db.as_dyn())
        )
    }
}

/// A query whose input depends on some side-effect (eg. file or network IO).
pub trait Input: Query {}

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
    fn execute_inline<'db, Q>(&'db self, input: Q::Input) -> ExecuteFuture<'db, Self, Q>
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let db = self.cast_dyn();
        let runtime = self.runtime();
        let storage = self.storage();
        let cache = storage.container();
        let result = cache.get_or_evaluate(db, input);

        async move {
            let (id, output) = match result {
                EvalResult::Cached(id) => id,
                EvalResult::Eval(eval) => eval.await,
                EvalResult::Pending(pending) => pending.await,
            };

            runtime.register_dependency(Dependency {
                container: cache.path(),
                resource: id,
                extra: 0,
            });

            output
        }
    }

    /// Spawn the query in the runtime, and possibly await its result in the background
    fn spawn<'db, Q>(&'db self, input: Q::Input) -> SpawnFuture<'db, Self, Q>
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let db = self.cast_dyn();
        let runtime = self.runtime();
        let storage = self.storage();
        let cache = storage.container();

        enum SpawnResult<Cached, Pending> {
            Cached(Cached),
            Pending(Pending),
            Spawned(Id),
        }

        let spawn_result = match cache.get_or_evaluate(db, input) {
            EvalResult::Cached(id) => SpawnResult::Cached(id),
            EvalResult::Pending(pending) => SpawnResult::Pending(pending),
            EvalResult::Eval(eval) => {
                // spawn the query, but postpone checking it for completion until the returned
                // future is polled. That way the spawned task has a chance of completing first.
                let id = eval.path().resource;
                runtime.spawn_query(eval);
                SpawnResult::Spawned(id)
            }
        };

        async move {
            let result = match spawn_result {
                SpawnResult::Cached(cached) => Ok(cached),
                SpawnResult::Pending(pending) => Err(pending),
                // the query was spawned in the runtime, so try getting its result again:
                SpawnResult::Spawned(id) => cache.get(db, id),
            };

            let (id, output) = match result {
                Ok(id) => id,
                Err(pending) => pending.await,
            };

            runtime.register_dependency(Dependency {
                container: cache.path(),
                resource: id,
                extra: 0,
            });

            output
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
        let db = self.cast_dyn();
        let storage = self.storage();
        let cache = storage.container();
        let result = cache.get_or_evaluate(db, input);

        match result {
            // the query is already computed/pending, so we are done here
            EvalResult::Cached(_) | EvalResult::Pending(_) => {}

            // the query must be evaluated, so spawn it in the runtime for concurrent processing
            EvalResult::Eval(eval) => db.runtime().spawn_query(eval),
        }
    }

    /// Set the value of an input
    fn set_input<'db, Q>(&'db mut self, input: Q::Input, output: Q::Output)
    where
        Q: Input,
        Q::Storage: 'static,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: StaticDatabase + WithStorage<Q::Storage>,
    {
        let storage = self.storage_mut();
        let cache = storage
            .list
            .get_mut::<Q::Storage>()
            .unwrap()
            .container_mut();
        cache.set(&mut storage.runtime, input, output);
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
            container: container.path(),
            resource: id,
            extra: 0,
        });
        value
    }

    /// Returns a wrapper which allows the value to be formatted using this database.
    ///
    /// The returned adapter makes `self` available through `fmt::with_storage` for the inner
    /// value's `Debug` and `Display` impls.
    fn fmt<T>(&self, value: T) -> fmt::Adapter<'_, T> {
        fmt::Adapter::new(self.as_dyn(), value)
    }
}

impl<DB> DatabaseExt for DB where DB: Database + ?Sized {}

/// Enters a scope within which it is possible to execute queries on other threads.
pub fn scope<DB, F, T>(db: &mut DB, f: F) -> T
where
    F: FnOnce(Scope<'_>, &DB) -> T,
    DB: StaticDatabase + Sized,
{
    let entered = unsafe { db.storage_mut().runtime.enter() };

    let scope = Scope {
        runtime: db.runtime(),
    };

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(scope, db)));

    if entered {
        // we were the ones responsible for calling `enter`, so we must also `exit`
        db.storage_mut().runtime.exit();
    }

    match result {
        Ok(output) => output,
        Err(panic) => std::panic::resume_unwind(panic),
    }
}

pub struct Scope<'a> {
    runtime: &'a Runtime,
}

impl<'a> Scope<'a> {
    /// Drives the runtime using the current thread until the given future completes.
    pub fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.runtime.block_on(f)
    }
}
