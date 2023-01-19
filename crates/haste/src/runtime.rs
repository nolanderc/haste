use std::{cell::Cell, future::Future, pin::Pin, sync::atomic::AtomicU32};

use crate::{non_max::NonMaxU32, Id, IngredientDatabase, IngredientPath, Query};

#[derive(Default)]
pub struct Runtime {
    id_allocator: TaskIdAllocator,
}

pub struct ExecutionResult<O> {
    pub output: O,
    pub dependencies: Vec<Dependency>,
}

pub trait QueryTask: Future<Output = crate::Id> {
    /// Emit a human-readable description of the query.
    fn description(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<unimplemented>")
    }
}

pub struct TaskHandle<'a> {
    runtime: &'a Runtime,
}

impl Future for TaskHandle<'_> {
    type Output = Id;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        todo!("poll task handle")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct TaskId(NonMaxU32);

struct TaskIdAllocator {
    next: AtomicU32,
}

impl Default for TaskIdAllocator {
    fn default() -> Self {
        Self {
            next: AtomicU32::new(0),
        }
    }
}

impl TaskIdAllocator {
    pub fn next(&self) -> TaskId {
        let raw = self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        TaskId(NonMaxU32::new(raw).expect("exhausted task IDs"))
    }
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
    /// A unique identifier for this task (note: task IDs might be recycled once they have finished
    /// running)
    #[allow(unused)]
    id: TaskId,

    /// List of all task dependencies
    dependencies: Vec<Dependency>,
}

impl TaskData {
    fn new(id: TaskId) -> Self {
        Self {
            id,
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
            task: Some(TaskData::new(self.id_allocator.next())),
        }
    }

    /// Register a dependency under the currently running query
    pub(crate) fn register_dependency(&self, dependency: Dependency) {
        ACTIVE_TASK.with(|task| {
            let Some(mut data) = task.take() else { return };
            data.dependencies.push(dependency);
            task.set(Some(data));
        })
    }

    pub(crate) fn spawn<'a, T>(&'a self, task: T) -> TaskHandle
    where
        T: QueryTask + 'a,
    {
        todo!("spawn task")
    }
}
