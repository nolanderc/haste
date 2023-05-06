use std::{
    cell::RefCell,
    num::NonZeroU32,
    sync::{
        atomic::{AtomicU64, Ordering::Relaxed},
        Condvar, Mutex,
    },
};

use crate::{cache::SlotState, Database, ElementDb, Query, QueryPath};

pub struct Runtime {
    stack_ids: StackIdAllocator,

    tasks: Mutex<Option<Vec<Task>>>,
    task_condition: Condvar,
}

impl Runtime {
    const MIN_STACK: usize = 32 * 1024 * 1024;

    #[inline]
    pub(crate) fn enter(&mut self) {
        let tasks = self.tasks.get_mut().unwrap();
        assert!(tasks.is_none(), "cannot nest scopes");
        *tasks = Some(Vec::new());
    }

    #[inline]
    pub(crate) fn exit(&mut self) {
        let tasks = self.tasks.get_mut().unwrap();
        assert!(tasks.take().is_some(), "scope was not entered");
    }

    pub(crate) fn new() -> Self {
        Self {
            stack_ids: StackIdAllocator::new(),
            tasks: Default::default(),
            task_condition: Default::default(),
        }
    }

    #[inline]
    pub(crate) fn allocate_stack(&self) -> StackId {
        self.stack_ids.allocate()
    }

    #[inline]
    pub(crate) fn free_stack(&self, stack: StackId) {
        self.stack_ids.free(stack)
    }

    pub(crate) fn current_stack(&self) -> StackId {
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let stack = active.get_or_insert_with(|| ActiveStack::new(self.stack_ids.allocate()));
            stack.id
        })
    }

    pub(crate) fn begin_query(&self, path: QueryPath) -> StackId {
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let stack = active.get_or_insert_with(|| ActiveStack::new(self.stack_ids.allocate()));
            stack.queries.push(QueryData::new(path));
            stack.id
        })
    }

    pub(crate) fn end_query(&self) -> ExecutionInfo {
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let stack = active.as_mut().expect("no active stack");

            let Some(query) = stack.queries.pop() else { panic!("no active query") };
            let dependencies = stack.dependencies.split_off(query.dependency_count);

            ExecutionInfo { dependencies }
        })
    }

    fn with_stack<R>(&self, stack: StackId, f: impl FnOnce() -> R) -> R {
        ACTIVE.with(|active| {
            let old = active.borrow_mut().replace(ActiveStack::new(stack));
            let result = f();
            *active.borrow_mut() = old;
            self.free_stack(stack);
            result
        })
    }

    #[inline]
    pub(crate) unsafe fn execute<Q: Query>(
        &self,
        db: &ElementDb<Q>,
        slot: &crate::cache::Slot<Q>,
        path: QueryPath,
    ) {
        self.begin_query(path);

        let input = slot.input_unchecked().clone();

        let output = stacker::maybe_grow(
            usize::max(Q::REQUIRED_STACK, 32 * 1024),
            usize::max(Q::REQUIRED_STACK, Self::MIN_STACK),
            || Q::execute(db, input),
        );

        let execution = self.end_query();

        let result = slot.write_output(output, execution);
        if result.has_blocking {
            db.runtime().wake_blocked();
        }
    }

    #[inline]
    pub(crate) unsafe fn spawn<'a, Q: Query>(
        &'a self,
        db: &'a ElementDb<Q>,
        slot: &'a crate::cache::Slot<Q>,
        path: QueryPath,
        stack: StackId,
    ) {
        let func = move || self.execute(db, slot, path);
        let func: Box<dyn FnOnce()> = Box::new(func);
        let func: Box<dyn FnOnce() + 'static> = std::mem::transmute(func);

        let task = Task { stack, func };
        if let Some(tasks) = self.tasks.lock().unwrap().as_mut() {
            tasks.push(task)
        } else {
            panic!("cannot spawn tasks outside thread scope")
        }
        self.task_condition.notify_one();
    }

    pub(crate) fn block_until_ready(&self, claimant: StackId, state: &SlotState) {
        let current = self.current_stack();

        // TODO: check for dependency cycles across stacks
        if current == claimant {
            panic!("dependency cycle");
        }

        let mut task_guard = self.tasks.lock().unwrap();
        while !state.is_ready() {
            if let Some(tasks) = task_guard.as_mut() {
                if let Some(task) = tasks.pop() {
                    drop(task_guard);

                    self.run_task(task);

                    task_guard = self.tasks.lock().unwrap();
                    continue;
                }
            }

            task_guard = self.task_condition.wait(task_guard).unwrap();
        }
    }

    pub(crate) fn wake_blocked(&self) {
        let _guard = self.tasks.lock().unwrap();
        self.task_condition.notify_all();
    }

    fn run_task(&self, task: Task) {
        self.with_stack(task.stack, task.func)
    }
}

thread_local! {
    static ACTIVE: RefCell<Option<ActiveStack>> = RefCell::new(None);
}

struct ActiveStack {
    id: StackId,
    queries: Vec<QueryData>,
    dependencies: Vec<QueryPath>,
}

impl ActiveStack {
    pub fn new(id: StackId) -> Self {
        Self {
            id,
            queries: Vec::new(),
            dependencies: Vec::new(),
        }
    }
}

struct QueryData {
    path: QueryPath,
    /// Number of dependencies registered for this query. Corresponds to the last dependenies in
    /// the active stack.
    dependency_count: usize,
}

impl QueryData {
    fn new(path: QueryPath) -> Self {
        Self {
            path,
            dependency_count: 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct StackId(pub NonZeroU32);

struct StackIdAllocator {
    next: AtomicU64,
    recycled: Mutex<Vec<StackId>>,
}

impl StackIdAllocator {
    fn new() -> StackIdAllocator {
        StackIdAllocator {
            next: AtomicU64::new(1),
            recycled: Mutex::new(Vec::new()),
        }
    }

    #[inline]
    pub fn allocate(&self) -> StackId {
        // check if we can recycle an old ID
        if let Some(id) = self.recycled.lock().unwrap().pop() {
            return id;
        }

        // otherwise generate a new ID
        let id = self.next.fetch_add(1, Relaxed);
        if let Ok(id) = u32::try_from(id) {
            return StackId(NonZeroU32::new(id).unwrap());
        }

        panic!("exhausted stack ID's")
    }

    #[inline]
    pub fn free(&self, id: StackId) {
        self.recycled.lock().unwrap().push(id);
    }
}

pub struct ExecutionInfo {
    pub dependencies: Vec<QueryPath>,
}

struct Task {
    stack: StackId,
    func: Box<dyn FnOnce() + 'static>,
}
