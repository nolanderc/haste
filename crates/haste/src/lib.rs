#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![feature(waker_getters)]
#![feature(const_collections_with_hasher)]
#![allow(clippy::uninlined_format_args)]

mod arena;
mod durability;
pub mod fmt;
mod input;
pub mod integer;
pub mod interner;
pub mod query_cache;
mod revision;
mod runtime;
mod shard_map;
mod storage;
pub mod util;

use std::{
    borrow::Cow, cell::RefCell, collections::HashMap, future::Future, marker::PhantomData,
    sync::{Mutex, atomic::AtomicBool}, time::Duration,
};

pub use durability::Durability;
use futures_lite::FutureExt;
pub use haste_macros::*;
pub use query_cache::*;
pub use revision::Revision;
use runtime::QueryMetrics;
pub use runtime::{Cycle, CycleStrategy, Dependency, Runtime};
pub use storage::*;

use integer::NonMaxU32;
use util::CallOnDrop;

/// A generic value that uniquely identifies a resource within some ingredient.
///
/// Note that misuse of this value (such as using the same ID for different ingredients) may have
/// adverse affects, such as inconsistent results and crashes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Id {
    pub(crate) raw: NonMaxU32,
}

impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id({})", self.raw)
    }
}

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.raw)
    }
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

    /// Determine how an ingredient handles dependency cycles.
    fn cycle_strategy(&self, path: ContainerPath) -> CycleStrategy;

    /// The ingredient is part of a cycle.
    fn set_cycle(&self, path: IngredientPath, cycle: Cycle);

    /// Given an ingredient, return the revision in which its value was last changed.
    fn last_change(&self, dep: Dependency) -> LastChangeFuture;

    /// Format an ingredient
    fn fmt_index(&self, path: IngredientPath, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    /// Get a type-erased pointer to a storage of the given type.
    fn get_storage_any(&self, id: std::any::TypeId) -> Option<&dyn std::any::Any>;

    /// Called when a query finishes executing. Allows the database to instrument how long
    /// different queries take to execute.
    fn register_metrics(&self, path: IngredientPath, metrics: QueryMetrics) {
        _ = path;
        _ = metrics;
    }
}

impl dyn Database {
    fn get_storage<S: Storage + 'static>(&self) -> Option<&S> {
        self.get_storage_any(std::any::TypeId::of::<S>())?
            .downcast_ref()
    }
}

pub trait StaticDatabase: Database + Sized {
    /// A type containing all the storages used by a database.
    type StorageList: StorageList<Self>;

    fn database_storage(&self) -> &DatabaseStorage<Self>;

    fn database_storage_mut(&mut self) -> &mut DatabaseStorage<Self>;
}

/// Implemented by databases which contain a specific type of storage.
pub trait WithStorage<S: Storage + ?Sized>: Database {
    fn cast_dyn(&self) -> &S::DynDatabase;
    fn storage(&self) -> (&S, &Runtime);
    fn storage_with_db(&self) -> (&S, &Runtime, &S::DynDatabase);
    fn storage_mut(&mut self) -> (&mut S, &mut Runtime);
}

pub trait Ingredient: 'static {
    /// The storage within which this ingredient exists.
    type Storage: Storage + HasIngredient<Self>;

    /// Type which contains all information required by the ingredient.
    type Container: StaticContainer;
}

/// The database required by some database
type DatabaseFor<T> = <<T as Ingredient>::Storage as Storage>::DynDatabase;

/// Implemented by storages which has a contoiner for the given ingredient.
pub trait HasIngredient<T: Ingredient + ?Sized>: Storage {
    fn container(&self) -> &T::Container;
    fn container_mut(&mut self) -> &mut T::Container;
}

pub trait TrackedReference {
    /// Is the value pointed to by this reference mutable? (eg. an input)
    const MIGHT_CHANGE: bool;

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
    type Input: Eq + Clone + Send + Sync + 'static;
    type Output: Eq + Send + Sync + 'static;
    type Future<'db>: Future<Output = Self::Output> + Send + 'db;
    type RecoverFuture<'db>: Future<Output = Self::Output> + Send + 'db;

    /// Determines if this is an input query.
    ///
    /// Input queries may not invoke other queries, but can be set from outside the database.
    const IS_INPUT: bool = false;

    /// Emit a human-readable version of the query.
    fn fmt(input: &Self::Input, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    /// Execute the query with the given input.
    fn execute(db: &DatabaseFor<Self>, input: Self::Input) -> Self::Future<'_>;

    /// Determines how the query should handle dependency cycles.
    const CYCLE_STRATEGY: CycleStrategy = CycleStrategy::Panic;

    /// If the query can recover from cycles, this is called when a cycle is discovered, and makes
    /// it possible to handle them gracefully without panicking.
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
///
/// Can also be set using `DatabaseExt::set_input`
pub trait Input: Query {}

/// A container that stores values (elements) which are accessed by an ID.
pub trait ElementContainer: StaticContainer {
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
    Q::Container: QueryCache<Query = Q> + Container<DB> + 'db,
    DB: WithStorage<Q::Storage>,
= impl Future<Output = &'db <Q as Query>::Output> + 'db;

type SpawnFuture<'db, DB: ?Sized, Q: Query>
where
    Q: Query,
    Q::Storage: 'db,
    Q::Container: QueryCache<Query = Q> + Container<DB> + 'db,
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
        Q::Container: QueryCache<Query = Q> + Container<Self> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let (storage, runtime, db) = self.storage_with_db();
        let cache = storage.container();
        let path = cache.path();

        let future = cache.get_or_evaluate(db, input);

        crate::util::future::poll_fn_pin(future, move |future, cx| {
            let result = std::task::ready!(future.poll(cx));
            runtime.register_query_dependency(path, &result);
            std::task::Poll::Ready(&result.slot.output)
        })
    }

    /// Spawn the query in the runtime, and possibly await its result in the background
    fn spawn<'db, Q>(&'db self, input: Q::Input) -> SpawnFuture<'db, Self, Q>
    where
        Q: Query,
        Q::Storage: 'db,
        Q::Container: QueryCache<Query = Q> + Container<Self> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        let (storage, runtime, db) = self.storage_with_db();
        let cache = storage.container();

        enum SpawnResult<Cached, Pending> {
            Cached(Cached),
            Pending(Pending),
            Spawned(Id),
        }

        let mut spawn = match cache.get_or_evaluate(db, input) {
            EvalResult::Cached(cached) => SpawnResult::Cached(cached),
            EvalResult::Pending(pending) => SpawnResult::Pending(pending),
            EvalResult::Eval(eval) => {
                // spawn the query, but postpone checking it for completion until the returned
                // future is polled. That way the spawned task has a chance of completing first.
                let id = runtime::QueryTask::path(&eval).resource;
                runtime.spawn_query(eval);
                SpawnResult::Spawned(id)
            }
        };

        std::future::poll_fn(move |cx| {
            let result = loop {
                match &mut spawn {
                    SpawnResult::Cached(cached) => break *cached,
                    SpawnResult::Pending(pending) => break std::task::ready!(pending.poll(cx)),
                    SpawnResult::Spawned(id) => match cache.get(db, *id) {
                        Ok(output) => break output,
                        Err(pending) => spawn = SpawnResult::Pending(pending),
                    },
                }
            };

            runtime.register_query_dependency(cache.path(), &result);

            std::task::Poll::Ready(&result.slot.output)
        })
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
        let (storage, runtime, db) = self.storage_with_db();
        let cache = storage.container();
        let result = cache.get_or_evaluate(db, input);

        match result {
            // the query is pending, so we are done here
            EvalResult::Cached(_) | EvalResult::Pending(_) => {}

            // the query must be evaluated, so spawn it in the runtime for concurrent processing
            EvalResult::Eval(eval) => runtime.spawn_query(eval),
        }
    }

    /// Set the value of an input
    fn set<'db, Q>(&'db mut self, input: Q::Input, output: Q::Output, durability: Durability)
    where
        Q: Input,
        Q::Storage: 'static,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        assert!(Q::IS_INPUT, "input queries must have `IS_INPUT == true`");

        let (storage, runtime) = self.storage_mut();
        let cache = storage.container_mut();
        cache.set(runtime, input, output, durability);
    }

    /// Clear the value of an input.
    fn remove<'db, Q>(&'db mut self, input: Q::Input)
    where
        Q: Input,
        Q::Storage: 'static,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        assert!(Q::IS_INPUT, "input queries must have `IS_INPUT == true`");

        let (storage, runtime) = self.storage_mut();
        let cache = storage.container_mut();
        cache.remove(runtime, &input);
    }

    /// Mark the query as invalid, forcing it to be re-evaluated in the next revision.
    fn invalidate<'db, Q>(&'db mut self, input: Q::Input)
    where
        Q: Input,
        Q::Storage: 'static,
        Q::Container: QueryCache<Query = Q> + 'db,
        Self: WithStorage<Q::Storage>,
    {
        assert!(Q::IS_INPUT, "input queries must have `IS_INPUT == true`");

        let _guard = tracing::debug_span!(
            "invalidate",
            query = %crate::util::fmt::from_fn(|f| {
                crate::fmt::wrap(self.as_dyn(), f, |f| Q::fmt(&input, f))
            }),
        )
        .entered();

        let (storage, runtime) = self.storage_mut();
        let cache = storage.container_mut();
        cache.invalidate(runtime, &input);
    }

    fn insert<'db, T>(&'db self, value: <T::Container as ElementContainer>::Value) -> T
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainer + 'db,
        <T::Container as ElementContainer>::Value: Sized,
        Self: WithStorage<T::Storage>,
    {
        let _guard = crate::enter_span(format!("insert {}", std::any::type_name::<T>()));

        let (storage, _runtime) = self.storage();
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
        let _guard = crate::enter_span(format!("insert_ref {}", std::any::type_name::<T>()));

        let (storage, _runtime) = self.storage();
        let container = storage.container();
        let id = container.insert_ref(value);
        T::from_id(id)
    }

    fn lookup<'db, T>(&'db self, handle: T) -> <T::Container as ElementContainer>::Ref<'db>
    where
        T: Ingredient + TrackedReference,
        T::Storage: 'db,
        T::Container: ElementContainer + Container<Self> + 'db,
        Self: WithStorage<T::Storage>,
    {
        let _guard = crate::enter_span(format!("lookup {}", std::any::type_name::<T>()));

        let (storage, runtime) = self.storage();
        let container = storage.container();

        let id = handle.id();
        let value = container.get_untracked(id);

        if T::MIGHT_CHANGE {
            runtime.register_dependency(
                Dependency {
                    container: container.path(),
                    resource: id,
                    extra: 0,
                },
                TransitiveDependencies::CONSTANT,
            );
        }

        value
    }

    /// Returns a wrapper which allows the value to be formatted using this database.
    ///
    /// The returned adapter makes `self` available through `fmt::with_storage` for the inner
    /// value's `Debug` and `Display` impls.
    fn fmt<T>(&self, value: T) -> fmt::Adapter<'_, T> {
        fmt::Adapter::new(self.as_dyn(), value)
    }

    fn scope<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(Scope<'_>, &Self) -> T,
        Self: StaticDatabase + 'static,
    {
        scope(self, f)
    }
}

impl<DB> DatabaseExt for DB where DB: Database + ?Sized {}

/// Enters a scope within which it is possible to execute queries on other threads.
pub fn scope<DB, F, T>(db: &mut DB, f: F) -> T
where
    F: FnOnce(Scope<'_>, &DB) -> T,
    DB: StaticDatabase + Sized + 'static,
{
    let storage = db.database_storage_mut();

    unsafe { storage.runtime.enter() };

    let current = storage.runtime.current_revision();

    storage.list_mut().0.begin(current);

    let runtime = db.runtime();

    let result = crate::fmt::scope(db, || {
        let _guard = CallOnDrop(|| runtime.exit());
        let scope = Scope {
            runtime,
            _phantom: PhantomData,
        };
        f(scope, db)
    });

    db.database_storage_mut().list_mut().0.end();

    result
}

pub struct Scope<'a> {
    runtime: &'a Runtime,

    // The scope needs to be `!Sync` so that only one thread blocks on the runtime at a time.
    _phantom: PhantomData<*mut ()>,
}

impl<'a> Scope<'a> {
    /// Drives the runtime using the current thread until the given future completes.
    pub fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.runtime.block_on(f)
    }
}

struct Metrics {
    /// For each span, its name, duration and count.
    spans: HashMap<SpanName, Span, ConstHasher>,

    /// For each active span, the time it was started and its name.
    stack: Vec<(SpanName, std::time::Instant)>,
}

struct ConstHasher;

impl std::hash::BuildHasher for ConstHasher {
    type Hasher = ahash::AHasher;

    fn build_hasher(&self) -> Self::Hasher {
        ahash::AHasher::default()
    }
}

impl Metrics {
    const fn new() -> Self {
        Self {
            spans: HashMap::with_hasher(ConstHasher),
            stack: Vec::new(),
        }
    }
}

#[derive(Default)]
struct Span {
    duration: Duration,
    max_duration: Duration,
    count: usize,
}

type SpanName = Cow<'static, str>;

thread_local! {
    static METRICS: RefCell<Metrics> = RefCell::new(Metrics::new());
}

static GLOBAL_METRICS: Mutex<Metrics> = Mutex::new(Metrics::new());

static METRICS_ENABLED: AtomicBool = AtomicBool::new(false);

pub fn enable_metrics(enable: bool) {
    METRICS_ENABLED.store(enable, std::sync::atomic::Ordering::Relaxed);
}

macro_rules! metrics_enabled {
    () => {
        if cfg!(feature = "metrics") {
            METRICS_ENABLED.load(std::sync::atomic::Ordering::Relaxed)
        } else {
            false
        }
    }
}

#[inline]
pub fn enter_span(name: impl Into<SpanName>) -> SpanGuard {
    if metrics_enabled!() {
        METRICS.with(|metrics| {
            let mut metrics = metrics.borrow_mut();
            metrics.stack.push((name.into(), std::time::Instant::now()));
        })
    }

    SpanGuard { _private: () }
}

#[must_use]
pub struct SpanGuard {
    _private: (),
}

impl Drop for SpanGuard {
    #[inline]
    fn drop(&mut self) {
        if metrics_enabled!() {
            METRICS.with(|metrics| {
                let mut metrics = metrics.borrow_mut();
                let (name, start) = metrics.stack.pop().expect("unbalanced number of spans");
                let duration = start.elapsed();
                let span = metrics.spans.entry(name).or_default();
                span.duration += duration;
                span.max_duration = duration.max(span.max_duration);
                span.count += 1;
            })
        }
    }
}

fn publish_metrics() {
    if metrics_enabled!() {
        METRICS.with(|metrics| {
            let mut metrics = metrics.borrow_mut();
            let mut global = GLOBAL_METRICS.lock().unwrap();
            for (name, span) in metrics.spans.drain() {
                let global_span = global.spans.entry(name).or_default();
                global_span.duration += span.duration;
                global_span.max_duration = span.max_duration.max(global_span.max_duration);
                global_span.count += span.count;
            }
        });
    }
}

fn print_global_metrics() {
    if metrics_enabled!() {
        let mut global = GLOBAL_METRICS.lock().unwrap();
        print_metrics_impl(&global).unwrap();
        global.spans.clear();
    }
}

fn print_metrics_impl(metrics: &Metrics) -> std::io::Result<()> {
    if metrics.spans.is_empty() {
        return Ok(());
    }

    use std::io::Write;

    let mut spans = metrics.spans.iter().collect::<Vec<_>>();

    spans.sort_by(|(a_name, a_span), (b_name, b_span)| {
        (a_span.duration, a_name)
            .cmp(&(b_span.duration, b_name))
            .reverse()
    });

    let stderr = std::io::stderr().lock();
    let mut writer = std::io::BufWriter::new(stderr);

    let name_header = "name";

    writeln!(
        writer,
        " {:>7}  {:>7}  {:>7}  {:>7}  {:<7}",
        "total", "max", "average", "count", name_header
    )?;

    let mut longest_name = name_header.len();
    for (name, _) in spans.iter() {
        longest_name = name.len().max(longest_name);
    }

    writeln!(
        writer,
        " -------  -------  -------  -------  {}",
        "-".repeat(longest_name),
    )?;

    for (name, span) in spans {
        let rate = span.duration / span.count as u32;
        writeln!(
            writer,
            " {:>7}  {:>7}  {:>7}  {:>7}  {}",
            PrettyDuration(span.duration),
            PrettyDuration(span.max_duration),
            PrettyDuration(rate),
            span.count,
            name,
        )?;
    }
    writeln!(writer)?;

    Ok(())
}

struct PrettyDuration(Duration);

impl std::fmt::Display for PrettyDuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut count = self.0.as_nanos();
        let mut unit = "ns";

        if count >= 10000 {
            count /= 1000;
            unit = "µs";
        }

        if count >= 10000 {
            count /= 1000;
            unit = "ms";
        }

        if count >= 10000 {
            count /= 1000;
            unit = "s";
        }

        let mut buffer = [0u8; 32];
        let mut writer = std::io::Cursor::new(&mut buffer[..]);

        use std::io::Write;
        write!(writer, "{count}{unit}").unwrap();

        let written = writer.position() as usize;
        let text = std::str::from_utf8(&buffer[..written]).unwrap();

        f.pad(text)
    }
}
