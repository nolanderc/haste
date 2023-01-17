use std::{cell::Cell, sync::atomic::AtomicU32};

use crate::{non_max::NonMaxU32, IngredientDatabase, IngredientPath, Query};

#[derive(Default)]
pub struct Runtime {
    id_allocator: TaskIdAllocator,
}

pub struct ExecutionResult<O> {
    pub output: O,
    pub dependencies: Vec<Dependency>,
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

impl Runtime {
    pub(crate) fn execute_query<Q: Query>(
        &self,
        db: &IngredientDatabase<Q>,
        input: Q::Input,
    ) -> ExecutionResult<Q::Output> {
        ACTIVE_TASK.with(|task| {
            let id = self.id_allocator.next();

            let old_task = task.replace(Some(TaskData::new(id)));
            let output = Q::execute(db, input);
            let task_result = task.replace(old_task).unwrap();

            ExecutionResult {
                output,
                dependencies: task_result.dependencies,
            }
        })
    }

    /// Register a dependency under the currently running query
    pub(crate) fn register_dependency(&self, dependency: Dependency) {
        ACTIVE_TASK.with(|task| {
            let Some(mut data) = task.take() else { return };
            data.dependencies.push(dependency);
            task.set(Some(data));
        })
    }
}
