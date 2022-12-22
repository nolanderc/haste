use std::{cell::Cell, sync::atomic::AtomicU32};

use crate::{non_max::NonMaxU32, IngredientId, Query};

#[derive(Default)]
pub struct Runtime {
    id_allocator: TaskIdAllocator,
}

pub struct ExecutionResult<Q: Query> {
    pub output: Q::Output,
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

pub struct Dependency {
    pub ingredient: IngredientId,
    pub resource: crate::Id,
}

struct TaskData {
    dependencies: Vec<Dependency>,
    id: TaskId,
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
        db: &Q::Database,
        input: Q::Input,
    ) -> ExecutionResult<Q> {
        ACTIVE_TASK.with(|task| {
            let id = self.id_allocator.next();
            let old_task = task.replace(Some(TaskData::new(id)));

            let output = Q::execute(db, input);

            let task_result = task
                .replace(old_task)
                .expect("no active task for the current thread");

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
