mod task;

use std::{cell::Cell, future::Future, pin::Pin};

use crate::{Id, IngredientDatabase, IngredientPath, Query};

pub use self::task::QueryTask;
use self::task::RawTask;

pub struct Runtime {
    in_scope: bool,
    tokio: tokio::runtime::Runtime,
}

impl Default for Runtime {
    fn default() -> Self {
        Self {
            in_scope: false,
            tokio: tokio::runtime::Runtime::new().unwrap(),
        }
    }
}

struct Scheduler {
    sender: flume::Sender<RawTask>,
    receiver: flume::Receiver<RawTask>,
}

impl Default for Scheduler {
    fn default() -> Self {
        let (sender, receiver) = flume::unbounded();
        Self { sender, receiver }
    }
}

impl Scheduler {
    pub fn schedule(&self, task: RawTask) {
        let _ = self.sender.send(task);
    }

    pub async fn take(&self) -> Option<RawTask> {
        self.receiver.recv_async().await.ok()
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

thread_local! {
    /// The currently active task for the current thread
    static ACTIVE_TASK: Cell<Option<TaskData>> = Cell::new(None);
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
        ACTIVE_TASK.with(|task| unsafe {
            // project the inner fields
            let this = self.get_unchecked_mut();
            let inner = Pin::new_unchecked(&mut this.inner);

            // set the current task as active when polling the query
            let old_task = task.replace(this.task.take());

            let poll_inner = inner.poll(ctx);

            // we then restore the previous task (if any)
            this.task = task.replace(old_task);

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
        ACTIVE_TASK.with(|active| {
            let Some(mut task) = active.take() else { return };
            task.dependencies.push(dependency);
            active.set(Some(task));
        })
    }

    pub(crate) fn spawn<'a, T>(&'a self, task: T)
    where
        T: QueryTask + Send + 'a,
    {
        assert!(
            self.in_scope,
            "call `haste::scope` to enter a scope before spawning new tasks"
        );

        unsafe {
            // extend the lifetime of the task to allow it to be stored in the runtime
            // SAFETY: `in_scope` was set, so `enter` has been called previously on this runtime.
            // Thus the lifetime of this task is ensured to outlive that.
            let task = std::mem::transmute::<
                Pin<Box<dyn QueryTask + Send + 'a>>,
                Pin<Box<dyn QueryTask + Send + 'static>>,
            >(Box::pin(task));
            self.tokio.spawn(task);
        }
    }

    pub fn block_on<F>(&self, f: F) -> F::Output
    where
        F: Future,
    {
        self.tokio.block_on(f)
    }

    /// Enter a new scope, allowing tasks to be spawned into it. If the return value is `true`, the
    /// caller is responsible for exiting the scope.
    ///
    /// # Safety
    ///
    /// The caller must ensure that a successful call to `enter` is followed by a matching call to
    /// `exit` before any further use of the associated database.
    pub(crate) unsafe fn enter(&mut self) -> bool {
        let previous = std::mem::replace(&mut self.in_scope, true);
        previous == false
    }

    pub(crate) fn exit(&mut self) {
        self.in_scope = false;
        drop(std::mem::replace(
            &mut self.tokio,
            tokio::runtime::Runtime::new().unwrap(),
        ));
    }
}
