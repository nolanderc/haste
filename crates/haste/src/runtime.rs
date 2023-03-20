mod cycle;
mod executor;
mod history;
// mod task;

use std::{
    cell::Cell,
    future::Future,
    pin::Pin,
    task::{Poll, Waker}, time::Duration,
};

use crate::{
    revision::Revision,
    util::{future::UnitFuture, CallOnDrop},
    ContainerPath, Database, DatabaseFor, Durability, IngredientPath, Query, QueryResult,
    RevisionRange, TransitiveDependencies,
};

pub use self::cycle::{Cycle, CycleStrategy};

use self::{
    cycle::CycleGraph,
    executor::{Executor, RawTask},
    history::ChangeHistory,
};

pub struct Runtime {
    /// Our custom executor is used for compute-bound tasks.
    executor: Executor,

    /// The tokio runtime is used to handle any IO-bound tasks.
    #[allow(dead_code)]
    tokio_runtime: tokio::runtime::Runtime,

    /// For each blocked task: the task it is blocked on.
    ///
    /// This is used to detect and resolve dependency cycles.
    graph: CycleGraph,

    /// A detailed history of all changes ever made to the query inputs.
    revisions: ChangeHistory,
}

impl Runtime {
    pub(crate) fn new() -> Self {
        let tokio_runtime = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()
            .unwrap();
        let scheduler = Executor::new(tokio_runtime.handle().clone());
        Self {
            tokio_runtime,
            executor: scheduler,
            graph: Default::default(),
            revisions: ChangeHistory::new(),
        }
    }

    pub fn current_revision(&self) -> Revision {
        self.revisions.current()
    }

    pub fn update_input(
        &mut self,
        changed_at: Option<Revision>,
        durability: Durability,
    ) -> Revision {
        self.revisions.push_update(changed_at, durability)
    }

    pub(crate) fn any_changed_since(
        &self,
        range: RevisionRange,
        last_verified: Revision,
        durability: Durability,
    ) -> bool {
        self.revisions
            .any_changed_since(range, last_verified, durability)
    }
}

pub struct ExecutionResult<O> {
    pub output: O,
    pub dependencies: Vec<Dependency>,
    pub transitive: TransitiveDependencies,
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
            self.container.index, self.resource.raw, self.extra
        )
    }
}

impl Dependency {
    pub(crate) fn new(ingredient: IngredientPath) -> Self {
        Self {
            container: ingredient.container,
            resource: ingredient.resource,
            extra: 0,
        }
    }

    pub fn container(self) -> ContainerPath {
        self.container
    }

    pub fn ingredient(self) -> IngredientPath {
        IngredientPath {
            container: self.container,
            resource: self.resource,
        }
    }
}

/// All data required to execute a task
#[derive(Debug)]
struct TaskData {
    /// Determines if the current query is an input.
    is_input: bool,

    /// An ingredient representing the query of this task
    this: IngredientPath,

    /// List of all direct dependencies of this task
    dependencies: Vec<Dependency>,

    /// Details about the transitive dependencies of the task.
    transitive: TransitiveDependencies,
}

impl TaskData {
    fn new<Q: Query>(this: IngredientPath, transitive: TransitiveDependencies) -> Self {
        Self {
            is_input: Q::IS_INPUT,
            this,
            dependencies: Vec::new(),
            transitive,
        }
    }
}

struct ActiveData {
    /// The currently active task
    task: Cell<Option<TaskData>>,
}

pub(crate) struct QueryInfo {
    pub path: IngredientPath,
    pub is_input: bool,
}

impl ActiveData {
    fn new() -> Self {
        Self {
            task: Cell::new(None),
        }
    }

    fn current_task(&self) -> Option<QueryInfo> {
        let task = self.task.replace(None)?;
        let info = QueryInfo {
            path: task.this,
            is_input: task.is_input,
        };
        self.task.set(Some(task));
        Some(info)
    }
}

thread_local! {
    /// The currently active task for the current thread.
    static ACTIVE: ActiveData = ActiveData::new();
}

#[pin_project::pin_project(PinnedDrop)]
pub(crate) struct ExecFuture<'db, Q: Query> {
    db: &'db DatabaseFor<Q>,
    /// Data associated with the running task.
    task: Option<TaskData>,
    /// The future which drives the query progress.
    #[pin]
    inner: ExecFutureInner<'db, Q>,
    /// The query is currently blocking this query.
    blocks: Option<IngredientPath>,

    /// Amount of time spent polling the query.
    duration: std::time::Duration,
    /// When the task was first polled.
    start: Option<std::time::Instant>,
}

#[pin_project::pin_project(project = ExecFutureInnerProj)]
enum ExecFutureInner<'a, Q: Query> {
    Eval(#[pin] Q::Future<'a>),
    Recover(#[pin] Q::RecoverFuture<'a>),
}

impl<'db, Q: Query> ExecFuture<'db, Q> {
    pub fn recover(self: Pin<&mut Self>, cycle: Cycle, input: &Q::Input) {
        let recovery = Q::recover_cycle(self.db, cycle, input.clone());
        let mut this = self.project();
        this.inner.set(ExecFutureInner::Recover(recovery));
    }

    pub fn query(&self) -> IngredientPath {
        self.task.as_ref().unwrap().this
    }
}

#[pin_project::pinned_drop]
impl<Q: Query> PinnedDrop for ExecFuture<'_, Q> {
    fn drop(self: Pin<&mut Self>) {
        if let Some(parent) = self.blocks {
            self.db.runtime().unblock(parent);
        }
    }
}

impl<'db, Q: Query> Future for ExecFuture<'db, Q> {
    type Output = ExecutionResult<Q::Output>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        ACTIVE.with(|active| {
            let this = self.project();

            if this.task.is_none() {
                panic!("polled query after it has already completed");
            }

            // set the current task as active when polling the query
            let mut old_task = active.task.replace(this.task.take());
            let parent = old_task.as_ref().map(|old| old.this);

            let restore_guard = CallOnDrop(|| *this.task = active.task.replace(old_task.take()));

            let start = std::time::Instant::now();
            if this.start.is_none() {
                *this.start = Some(start);
            }

            // poll the query for completion
            let poll_inner = match this.inner.project() {
                ExecFutureInnerProj::Eval(eval) => eval.poll(cx),
                ExecFutureInnerProj::Recover(recover) => recover.poll(cx),
            };

            *this.duration += start.elapsed();

            // restore the previous task
            drop(restore_guard);

            let me = this.task.as_ref().unwrap().this;

            // if this query is polled from another query, block that parent on this task
            if let Some(parent) = parent {
                match (&poll_inner, *this.blocks) {
                    (Poll::Pending, None) => {
                        let db = this.db.as_dyn();
                        this.db.runtime().would_block_on(parent, me, cx.waker(), db);
                        *this.blocks = Some(parent);
                    }
                    (Poll::Ready(_), Some(parent)) => {
                        this.db.runtime().unblock(parent);
                        *this.blocks = None;
                    }
                    _ => {}
                }
            }

            // if the query completed, we can return it
            let output = std::task::ready!(poll_inner);
            let data = this.task.take().unwrap();

            let metrics = QueryMetrics {
                poll_duration: *this.duration,
                total_duration: this.start.unwrap().elapsed(),
            };
            this.db.register_metrics(data.this, metrics);

            Poll::Ready(ExecutionResult {
                output,
                dependencies: data.dependencies,
                transitive: data.transitive,
            })
        })
    }
}

impl Runtime {
    pub(crate) fn execute_query<'db, Q: Query>(
        &self,
        db: &'db DatabaseFor<Q>,
        input: Q::Input,
        this: IngredientPath,
    ) -> ExecFuture<'db, Q> {
        let transitive = if Q::IS_INPUT {
            let current = self.current_revision();
            TransitiveDependencies {
                inputs: Some(RevisionRange {
                    earliest: current,
                    latest: current,
                }),
                durability: Durability::DEFAULT,
            }
        } else {
            // initially derived queries don't depend on anything, so can be considered constants
            TransitiveDependencies::CONSTANT
        };

        ExecFuture {
            db,
            inner: ExecFutureInner::Eval(Q::execute(db, input)),
            task: Some(TaskData::new::<Q>(this, transitive)),
            blocks: None,
            duration: std::time::Duration::ZERO,
            start: None,
        }
    }

    /// Sets the durability of the currently running query.
    ///
    /// # Panics
    ///
    /// Must only be called from within an `#[input]` query.
    pub fn set_durability(&self, durability: Durability) {
        ACTIVE.with(|active| {
            let Some(mut task) = active.task.take() else { return };
            assert!(task.is_input, "can only set durability of input queries");
            task.transitive.durability = durability;
            active.task.set(Some(task));
        })
    }

    /// Register a dependency under the currently running query
    pub(crate) fn register_dependency(
        &self,
        dependency: Dependency,
        transitive: TransitiveDependencies,
    ) {
        ACTIVE.with(|active| {
            let Some(mut task) = active.task.take() else { return };
            task.dependencies.push(dependency);
            task.transitive.extend(transitive);
            active.task.set(Some(task));
        })
    }

    /// Register a dependency under the currently running query
    pub(crate) fn register_query_dependency<Q: Query>(
        &self,
        container: ContainerPath,
        result: &QueryResult<Q>,
    ) {
        let ingredient = IngredientPath {
            container,
            resource: result.id,
        };

        let transitive = result
            .slot
            .transitive
            .expect("query did not specify transitive dependencies");

        self.register_dependency(Dependency::new(ingredient), transitive)
    }

    pub(crate) fn current_query(&self) -> Option<QueryInfo> {
        ACTIVE.with(|active| active.current_task())
    }

    pub(crate) fn would_block_on(
        &self,
        parent: IngredientPath,
        child: IngredientPath,
        waker: &Waker,
        db: &dyn Database,
    ) {
        tracing::trace!(
            child = %crate::util::fmt::ingredient(db, child),
            ?parent,
            "would block on",
        );
        self.graph.insert(parent, child, waker, db);
    }

    pub(crate) fn unblock(&self, parent: IngredientPath) {
        tracing::trace!(?parent, "unblocked");
        self.graph.remove(parent);
    }

    pub(crate) fn spawn_query<'a, T>(&'a self, task: BoxedQueryTask<T>)
    where
        T: QueryTask + Future + Send + 'a,
    {
        // SAFETY: This extends the lifetime of the task to `'static`, but we ensure that the
        // executor is stopped before the lifetime of the runtime is over.
        unsafe { self.executor.spawn(task.raw) }
    }

    pub(crate) fn block_on<F>(&self, f: F) -> F::Output
    where
        F: Future,
    {
        self.executor.run(f)
    }
}

pub trait QueryTask {
    /// Poll the task for completion.
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<()>;

    /// Get a unique identifier for the query.
    fn path(&self) -> IngredientPath;
}

pub struct BoxedQueryTask<T> {
    raw: Box<RawTask<UnitFuture<T>>>,
}

impl<T> QueryTask for BoxedQueryTask<T>
where
    T: QueryTask,
{
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<()> {
        unsafe {
            let inner: &mut T = &mut self.get_unchecked_mut().raw;
            T::poll(Pin::new_unchecked(inner), cx)
        }
    }

    fn path(&self) -> IngredientPath {
        T::path(&self.raw)
    }
}

impl<T> Future for BoxedQueryTask<T>
where
    T: Future,
{
    type Output = T::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        unsafe {
            let inner: &mut T = &mut self.get_unchecked_mut().raw;
            Pin::new_unchecked(inner).poll(cx)
        }
    }
}

impl<T> BoxedQueryTask<T> {
    pub fn new(runtime: &Runtime, create: impl FnOnce() -> T) -> Self
    where
        T: Future,
    {
        let raw = runtime
            .executor
            .create_task(move || UnitFuture::new(create()));
        Self { raw }
    }
}

impl Runtime {
    /// Enter a new scope, allowing tasks to be spawned into it. If the return value is `true`,
    /// the caller is responsible for exiting the scope.
    ///
    /// # Safety
    ///
    /// The caller must ensure that a successful call to `enter` is followed by a matching call to
    /// `exit` before any further use of the associated database.
    pub(crate) unsafe fn enter(&mut self) {
        assert!(self.executor.start(), "could not start runtime scheduler");
    }

    pub(crate) fn exit(&self) {
        // cancel all running tasks and wait for shutdown
        assert!(self.executor.stop(), "could not stop runtime scheduler");
    }
}

#[derive(Debug, Clone, Copy)]
pub struct QueryMetrics {
    /// Amount of spent polling the query for completion.
    pub poll_duration: Duration,

    /// Total amonut of time from when the query was first polled and when it was completed.
    pub total_duration: Duration,
}
