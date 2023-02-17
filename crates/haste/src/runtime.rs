mod cycle;
mod task;

use std::{
    cell::Cell,
    future::Future,
    pin::Pin,
    sync::{
        atomic::{AtomicPtr, AtomicU64, Ordering},
        Arc, Mutex,
    },
};

use crate::{
    non_max::NonMaxU32, ContainerPath, Database, IngredientDatabase, IngredientPath, Query,
};

pub use self::cycle::{Cycle, CycleStrategy};
pub use self::task::QueryTask;
use self::{cycle::CycleGraph, task::Scheduler};

pub struct Runtime {
    tokio: Option<tokio::runtime::Runtime>,
    scheduler: Arc<Scheduler>,
    graph: Mutex<CycleGraph>,
}

impl Default for Runtime {
    fn default() -> Self {
        Self {
            tokio: None,
            scheduler: Arc::new(Scheduler::new()),
            graph: Default::default(),
        }
    }
}

pub struct ExecutionResult<O> {
    pub output: O,
    pub dependencies: Vec<Dependency>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Dependency {
    pub(crate) container: ContainerPath,
    pub(crate) resource: crate::Id,
    /// Extra information carried by the dependency (such as the active field)
    pub(crate) extra: u16,
}

const _: () = assert!(
    std::mem::size_of::<Dependency>() == 8,
    "the size of Dependencies should be kept small to be nice to the cache"
);

impl std::fmt::Debug for Dependency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}.{}",
            self.container.encode_u16(),
            self.resource.raw,
            self.extra
        )
    }
}

impl Dependency {
    /// A 64-bit value representing a missing dependency.
    pub(crate) const NONE: u64 = u64::MAX;

    /// Encode the dependency in 64-bits
    pub(crate) fn encode_u64(self) -> u64 {
        let ingredient = self.container.encode_u16() as u64;
        let resource = self.resource.raw.get() as u64;
        let extra = self.extra as u64;
        (ingredient << 48) | (resource << 16) | extra
    }

    /// Decode the dependency from a 64-bit value
    pub(crate) fn decode_u64(x: u64) -> Option<Self> {
        Some(Self {
            container: ContainerPath::decode_u16((x >> 48) as u16),
            resource: crate::Id::new(NonMaxU32::new((x >> 16) as u32)?),
            extra: x as u16,
        })
    }
}

#[derive(Debug)]
pub struct AtomicDependency {
    bits: AtomicU64,
}

impl AtomicDependency {
    pub fn new(dep: Option<Dependency>) -> Self {
        Self {
            bits: AtomicU64::new(Self::encode(dep)),
        }
    }

    fn encode(dep: Option<Dependency>) -> u64 {
        dep.map(|dep| dep.encode_u64()).unwrap_or(Dependency::NONE)
    }

    pub fn load(&self, ordering: Ordering) -> Option<Dependency> {
        Dependency::decode_u64(self.bits.load(ordering))
    }

    pub fn store(&self, value: Option<Dependency>, ordering: Ordering) {
        self.bits.store(Self::encode(value), ordering)
    }
}

/// All data required to execute a task
#[derive(Debug)]
struct TaskData {
    /// An ingredient representing the query of this task
    this: IngredientPath,

    /// List of all direct dependencies of this task
    dependencies: Vec<Dependency>,
}

impl TaskData {
    fn new(this: IngredientPath) -> Self {
        Self {
            this,
            dependencies: Vec::new(),
        }
    }
}

struct ActiveData {
    /// The currently active task
    task: Cell<Option<TaskData>>,
}

impl ActiveData {
    fn new() -> Self {
        Self {
            task: Cell::new(None),
        }
    }

    fn current_task(&self) -> Option<IngredientPath> {
        let task = self.task.replace(None)?;
        let current = task.this;
        self.task.set(Some(task));
        Some(current)
    }
}

thread_local! {
    /// The currently active task for the current thread.
    static ACTIVE: ActiveData = ActiveData::new();
}

pub(crate) struct QueryFuture<'db, Q: Query> {
    /// The future which drives the query progress.
    inner: Q::Future<'db>,
    /// Data associated with the executing task.
    task: Option<TaskData>,
}

impl<'db, Q: Query> Future for QueryFuture<'db, Q> {
    type Output = ExecutionResult<Q::Output>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        ctx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        ACTIVE.with(|active| unsafe {
            // project the inner fields
            let this = self.get_unchecked_mut();
            let inner = Pin::new_unchecked(&mut this.inner);

            if this.task.is_none() {
                panic!("polled query after it has already completed");
            }

            // set the current task as active when polling the query
            let old_task = active.task.replace(this.task.take());
            let poll_inner = inner.poll(ctx);

            // restore the previous task
            this.task = active.task.replace(old_task);

            // if the query completed, we can return it
            let output = std::task::ready!(poll_inner);

            let dependencies = this.task.take().unwrap().dependencies;

            std::task::Poll::Ready(ExecutionResult {
                output,
                dependencies,
            })
        })
    }
}

impl Runtime {
    pub(crate) fn execute_query<'db, Q: Query>(
        &self,
        db: &'db IngredientDatabase<Q>,
        input: Q::Input,
        this: IngredientPath,
    ) -> QueryFuture<'db, Q> {
        QueryFuture {
            inner: Q::execute(db, input),
            task: Some(TaskData::new(this)),
        }
    }

    /// Register a dependency under the currently running query
    pub(crate) fn register_dependency(&self, dependency: Dependency) {
        ACTIVE.with(|active| {
            let Some(mut task) = active.task.take() else { return };
            task.dependencies.push(dependency);
            active.task.set(Some(task));
        })
    }

    /// Called when the execution of a query would block on another
    #[must_use]
    pub(crate) fn would_block_on(&self, other: IngredientPath, db: &dyn Database) -> Option<Cycle> {
        ACTIVE.with(|active| {
            let Some(this) = active.current_task() else { return None };
            use crate::util::fmt::query;
            eprintln!("{} is blocked on {}", query(db, this), query(db, other));
            self.graph.lock().unwrap().insert(this, other, db)
        })
    }

    pub(crate) fn unblock(&self, other: IngredientPath, _db: &dyn Database) {
        ACTIVE.with(|active| {
            let Some(this) = active.current_task() else { return };
            eprintln!("{:?} is no longer blocked on {:?}", this, other);
            self.graph.lock().unwrap().remove(this, other);
        })
    }

    pub(crate) fn spawn_query<'a, T>(&'a self, task: T)
    where
        T: QueryTask + Send + 'a,
    {
        let _tokio = self.executor();

        unsafe {
            // extend the lifetime of the task to allow it to be stored in the runtime
            // SAFETY: `in_scope` was set, so `enter` has been called previously on this runtime.
            // Thus the lifetime of this task is ensured to outlive that.
            let task = std::mem::transmute::<
                Box<dyn QueryTask + Send + 'a>,
                Box<dyn QueryTask + Send + 'static>,
            >(Box::new(task));

            self.scheduler.spawn(task);
        }
    }

    pub(crate) fn block_on<F>(&self, f: F) -> F::Output
    where
        F: Future,
    {
        let executor = self.executor();
        let forever = async { self.run().await };
        executor.block_on(futures_lite::future::or(f, forever))
    }

    pub(crate) async fn run(&self) -> ! {
        self.scheduler.run().await
    }
}

/// There may only be one active runtime. This keeps track of what runtime that is.
///
/// # Safety
///
/// This pointer should only be used for identity comparisons. Dereferincing is forbidden.
static ACTIVE_RUNTIME: AtomicPtr<Runtime> = AtomicPtr::new(std::ptr::null_mut());

impl Runtime {
    /// Enter a new scope, allowing tasks to be spawned into it. If the return value is `true`,
    /// the caller is responsible for exiting the scope.
    ///
    /// # Safety
    ///
    /// The caller must ensure that a successful call to `enter` is followed by a matching call to
    /// `exit` before any further use of the associated database.
    pub(crate) unsafe fn enter(&mut self) -> bool {
        use Ordering::Relaxed;

        match ACTIVE_RUNTIME.compare_exchange(std::ptr::null_mut(), self, Relaxed, Relaxed) {
            Ok(_) => {
                self.tokio = Some(tokio::runtime::Runtime::new().unwrap());
                self.scheduler.start();
                true
            }

            // this runtime was already active, so we are done:
            Err(old) if old == self => false,

            Err(_) => panic!("only one runtime can be in scope at once"),
        }
    }

    pub(crate) fn exit(&mut self) {
        // cancel all running tasks and wait for shutdown
        let active = ACTIVE_RUNTIME.load(Ordering::Relaxed);
        assert!(active == self, "can only exit the currently active runtime");

        self.scheduler.shutdown();
        drop(self.tokio.take());

        ACTIVE_RUNTIME.store(std::ptr::null_mut(), Ordering::Relaxed);
    }

    /// Get the current executor
    fn executor(&self) -> &tokio::runtime::Runtime {
        match &self.tokio {
            None => panic!("call `haste::scope` to enter a scope before spawning new tasks"),
            Some(executor) => executor,
        }
    }
}
