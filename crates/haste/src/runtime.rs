mod task;

use std::{
    cell::Cell,
    future::Future,
    pin::Pin,
    sync::{atomic::AtomicU32, Arc},
};

use crate::{non_max::NonMaxU32, IngredientDatabase, IngredientPath, Query};

pub use self::task::QueryTask;
use self::task::RawTask;

#[derive(Default)]
pub struct Runtime {
    scheduler: Arc<Scheduler>,
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

    pub(crate) unsafe fn spawn<'a, T>(&'a self, task: T)
    where
        T: QueryTask + Send + 'a,
    {
        // extend the lifetime of the task to allow it to be stored in the runtime
        let task = std::mem::transmute::<
            Box<dyn QueryTask + Send + 'a>,
            Box<dyn QueryTask + Send + 'static>,
        >(Box::new(task));

        let task = RawTask::new(task, Arc::downgrade(&self.scheduler));
        self.scheduler.schedule(task);
    }

    pub fn block_on<F>(&self, f: F) -> F::Output
    where
        F: Future,
    {
        pollster::block_on(self.run(f))
    }

    /// Drive the runtime until the future completes
    pub async fn run<F>(&self, f: F) -> F::Output
    where
        F: Future,
    {
        let forever = async move {
            let mut i = 0u8;
            loop {
                if let Some(task) = self.scheduler.take().await {
                    task.poll();
                } else {
                    break;
                }

                i = i.wrapping_add(1);
                if i == 0 {
                    futures_lite::future::yield_now().await;
                }
            }

            std::future::pending().await
        };

        futures_lite::future::race(f, forever).await
    }
}
