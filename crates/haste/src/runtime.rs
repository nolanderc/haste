mod cycle;
mod revision;
mod task;

use std::{
    cell::Cell,
    future::Future,
    pin::Pin,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc, Mutex,
    },
    task::{Poll, Waker},
};

use crate::{
    non_max::NonMaxU32, util::CallOnDrop, ContainerPath, Database, DatabaseFor, Durability,
    IngredientPath, Query, TransitiveDependencies,
};

pub use self::cycle::{Cycle, CycleStrategy};
pub use self::revision::{AtomicRevision, Revision};
pub use self::task::QueryTask;

use self::{cycle::CycleGraph, revision::RevisionHistory, task::Scheduler};

pub struct Runtime {
    scheduler: Arc<Scheduler>,
    graph: Mutex<CycleGraph>,
    revisions: RevisionHistory,
}

impl Runtime {
    pub(crate) fn new() -> Self {
        Self {
            scheduler: Arc::new(Scheduler::new()),
            graph: Default::default(),
            revisions: RevisionHistory::new(),
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

    pub fn earliest_change_since(&self, revision: Revision, durability: Durability) -> Revision {
        self.revisions.earliest_change_since(revision, durability)
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
    /// A 64-bit value representing a missing dependency.
    pub(crate) const NONE: u64 = u64::MAX;

    /// Encode the dependency in 64-bits
    pub(crate) fn encode_u64(self) -> u64 {
        let ingredient = self.container.index as u64;
        let resource = self.resource.raw.get() as u64;
        let extra = self.extra as u64;
        (ingredient << 48) | (resource << 16) | extra
    }

    /// Decode the dependency from a 64-bit value
    pub(crate) fn decode_u64(x: u64) -> Option<Self> {
        Some(Self {
            container: ContainerPath {
                index: (x >> 48) as u16,
            },
            resource: crate::Id::new(NonMaxU32::new((x >> 16) as u32)?),
            extra: x as u16,
        })
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

    /// Details about the transitive dependencies of the task.
    transitive: TransitiveDependencies,
}

impl TaskData {
    fn new(this: IngredientPath, transitive: TransitiveDependencies) -> Self {
        Self {
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
    /// A span representing the duration of the query.
    span: tracing::Span,
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

    pub fn database(&self) -> &DatabaseFor<Q> {
        self.db
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
            let _guard = this.span.enter();

            if this.task.is_none() {
                panic!("polled query after it has already completed");
            }

            // set the current task as active when polling the query
            let mut old_task = active.task.replace(this.task.take());
            let parent = old_task.as_ref().map(|old| old.this);

            let restore_guard = CallOnDrop(|| *this.task = active.task.replace(old_task.take()));

            // poll the query for completion
            let poll_inner = match this.inner.project() {
                ExecFutureInnerProj::Eval(eval) => eval.poll(cx),
                ExecFutureInnerProj::Recover(recover) => recover.poll(cx),
            };

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
            TransitiveDependencies {
                latest_input: Some(self.current_revision()),
                durability: Durability::MEDIUM,
            }
        } else {
            // initially derived queries don't depend on anything, so can be considered constants
            TransitiveDependencies::CONSTANT
        };

        ExecFuture {
            db,
            inner: ExecFutureInner::Eval(Q::execute(db, input)),
            task: Some(TaskData::new(this, transitive)),
            blocks: None,
            span: tracing::error_span!(
                "execute",
                query = %crate::util::fmt::ingredient(db.as_dyn(), this),
            ),
        }
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

    pub(crate) fn current_query(&self) -> Option<IngredientPath> {
        ACTIVE.with(|active| active.current_task())
    }

    pub(crate) fn would_block_on(
        &self,
        parent: IngredientPath,
        child: IngredientPath,
        waker: &Waker,
        db: &dyn Database,
    ) {
        tracing::debug!(
            child = %crate::util::fmt::ingredient(db, child),
            "would block on",
        );
        self.graph.lock().unwrap().insert(parent, child, waker, db);
    }

    pub(crate) fn unblock(&self, parent: IngredientPath) {
        tracing::debug!("unblocked");

        if let Ok(mut graph) = self.graph.lock() {
            graph.remove(parent);
        }
    }

    pub(crate) fn spawn_query<'a, T>(&'a self, task: T)
    where
        T: QueryTask + Send + 'a,
    {
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
        let forever = async { self.scheduler.run().await };
        pollster::block_on(futures_lite::future::or(f, forever))
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
        assert!(self.scheduler.start(), "could not start runtime scheduler");
    }

    pub(crate) fn exit(&self) {
        // cancel all running tasks and wait for shutdown
        self.scheduler.shutdown();
    }
}
