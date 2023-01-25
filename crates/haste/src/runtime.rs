mod task;

use std::{
    cell::Cell,
    future::Future,
    pin::Pin,
    sync::atomic::{AtomicPtr, Ordering},
};

use crate::{IngredientDatabase, IngredientPath, Query};

pub use self::task::QueryTask;
use self::task::RawTask;

pub struct Runtime {
    tokio: Option<tokio::runtime::Runtime>,
}

impl Default for Runtime {
    fn default() -> Self {
        Self { tokio: None }
    }
}

pub struct ExecutionResult<O> {
    pub output: O,
    pub dependencies: Vec<Dependency>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Dependency {
    pub ingredient: IngredientPath,
    pub resource: crate::Id,
    /// Extra information carried by the dependency
    pub extra: u16,
}

const _: () = assert!(
    std::mem::size_of::<Dependency>() == 8,
    "the size of Dependencies should be kept small to be nice to the cache"
);

/// All data required to execute a task
struct TaskData {
    /// List of all task dependencies
    dependencies: Vec<Dependency>,
}

impl TaskData {
    fn new() -> Self {
        Self {
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

            // set the current task as active when polling the query
            let old_task = active.task.replace(this.task.take());

            let poll_inner = inner.poll(ctx);

            // we then restore the previous task (if any)
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
    ) -> QueryFuture<'db, Q> {
        QueryFuture {
            inner: Q::execute(db, input),
            task: Some(TaskData::new()),
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

    fn executor(&self) -> &tokio::runtime::Runtime {
        match &self.tokio {
            None => panic!("call `haste::scope` to enter a scope before spawning new tasks"),
            Some(executor) => executor,
        }
    }

    pub(crate) fn spawn_query<'a, T>(&'a self, task: T) -> impl Future<Output = crate::Id>
    where
        T: QueryTask + Send + 'a,
    {
        unsafe {
            let tokio = self.executor();

            // extend the lifetime of the task to allow it to be stored in the runtime
            // SAFETY: `in_scope` was set, so `enter` has been called previously on this runtime.
            // Thus the lifetime of this task is ensured to outlive that.
            let task = std::mem::transmute::<
                Pin<Box<dyn QueryTask + Send + 'a>>,
                Pin<Box<dyn QueryTask + Send + 'static>>,
            >(Box::pin(task));

            let handle = tokio.spawn(task);
            async move { handle.await.unwrap() }
        }
    }

    pub fn block_on<F>(&self, f: F) -> F::Output
    where
        F: Future,
    {
        self.executor().block_on(f)
    }
}

/// There may only be one active runtime. This keeps track of what runtime that is.
///
/// # Safety
///
/// This pointer should only be used for identity comparisons. Dereferincing is forbidden.
static ACTIVE_RUNTIME: AtomicPtr<Runtime> = AtomicPtr::new(std::ptr::null_mut());

impl Runtime {
    /// Enter a new scope, allowing tasks to be spawned into it. If the return value is `true`, the
    /// caller is responsible for exiting the scope.
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
                true
            }

            // this runtime was already active, so we are done:
            Err(old) if old == self => return false,

            Err(_) => panic!("only one runtime can be in scope at once"),
        }
    }

    pub(crate) fn exit(&mut self) {
        // cancel all running tasks and wait for shutdown
        drop(self.tokio.take());
        ACTIVE_RUNTIME.store(std::ptr::null_mut(), Ordering::Relaxed);
    }
}
