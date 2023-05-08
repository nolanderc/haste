mod cycle;
mod history;

use std::{
    cell::RefCell,
    num::{NonZeroU16, NonZeroU32},
    sync::{
        atomic::{
            AtomicU64,
            Ordering::{Acquire, Relaxed},
        },
        Arc, Mutex, Weak,
    },
};

use arc_swap::ArcSwap;
use crossbeam_deque::{Stealer, Worker};
use dashmap::DashMap;
use smallvec::SmallVec;

use crate::{
    cache::{SlotId, SlotState},
    durability::Durability,
    revision::Revision,
    util::DynPointer,
    Database, ElementDb, ElementId, ElementPath, Query,
};

use self::{cycle::CycleGraph, history::History};

/// Smallest stack size to allocate for queries (in bytes).
const MIN_STACK: usize = 32 * 1024 * 1024;

pub struct Runtime {
    stack_ids: StackIdAllocator,

    cycles: CycleGraph,
    history: History,

    thread_scope: Option<Arc<ThreadScope>>,
    tasks: DashMap<ElementPath, Task>,
    workers: ArcSwap<WorkerState>,
}

impl Runtime {
    pub(crate) fn new() -> Self {
        Self {
            stack_ids: StackIdAllocator::new(),
            cycles: CycleGraph::default(),
            history: History::new(),
            thread_scope: None,
            tasks: DashMap::with_capacity(1024),
            workers: Default::default(),
        }
    }

    #[inline]
    pub(crate) unsafe fn enter(&mut self) {
        assert!(self.thread_scope.is_none(), "cannot nest scopes");
        self.thread_scope = Some(Arc::new(ThreadScope));
    }

    #[inline]
    pub(crate) unsafe fn exit(&mut self) {
        assert!(self.thread_scope.take().is_some(), "scope was not entered");

        // drop all pending tasks
        self.drain_tasks();
    }

    fn drain_tasks(&mut self) {
        self.tasks.clear();
        std::mem::take(&mut self.workers);
    }

    #[inline]
    pub(crate) fn current_revision(&self) -> Revision {
        self.history.current()
    }

    pub(crate) fn update_input(&mut self, durability: Durability) {
        self.history.update(durability);
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

    pub(crate) fn begin_query(
        &self,
        path: ElementPath,
        durability: Durability,
        is_input: bool,
    ) -> StackId {
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let stack = active.get_or_insert_with(|| ActiveStack::new(self.stack_ids.allocate()));
            stack.queries.push(QueryData {
                path,
                durability,
                is_input,
                dependency_count: 0,
            });
            stack.id
        })
    }

    pub(crate) fn end_query<R>(&self, with_info: impl FnOnce(ExecutionInfo) -> R) -> R {
        ACTIVE.with(|active| {
            let mut active = active.borrow_mut();
            let stack = active.as_mut().expect("no active stack");

            let Some(query) = stack.queries.pop() else { panic!("no active query") };

            let dependencies_start = stack.dependencies.len() - query.dependency_count;
            let dependencies = &stack.dependencies[dependencies_start..];

            with_info(ExecutionInfo {
                durability: query.durability,
                dependencies,
            })
        })
    }

    pub(crate) fn current_spawn_group(&self) -> Option<SpawnGroup> {
        ACTIVE.with(|cell| {
            let active = cell.borrow_mut();
            let query = active.as_ref()?.queries.last()?;
            SpawnGroup::new(query.dependency_count)
        })
    }

    #[inline]
    pub(crate) fn register_dependency(&self, dependency: Dependency) {
        ACTIVE.with(|active| {
            if let Some(active) = active.borrow_mut().as_mut() {
                let Some(query) = active.queries.last_mut() else { return };

                assert!(!query.is_input, "queries may not invoke other queries");

                query.dependency_count += 1;
                active.dependencies.push(dependency);
            }
        })
    }

    #[inline]
    pub fn set_input_durability(&self, durability: Durability) {
        ACTIVE.with(|active| {
            if let Some(active) = active.borrow_mut().as_mut() {
                let Some(query) = active.queries.last_mut() else { return };
                query.durability = std::cmp::min(query.durability, durability);
            }
        })
    }

    #[inline]
    pub(crate) unsafe fn execute<Q: Query>(
        &self,
        db: &ElementDb<Q>,
        slot: &crate::cache::Slot<Q>,
        path: ElementPath,
        last_verified: Option<Revision>,
    ) {
        let result = if let Some(durability) = self.is_valid(db, slot, last_verified) {
            slot.backdate(self.current_revision(), durability)
        } else {
            self.execute_with_info(db, path, slot, |output, info| {
                slot.write_output(output, info, self.current_revision())
            })
        };

        if result.has_blocking {
            self.wake_query(slot.state());
        }
    }

    #[inline]
    fn is_valid<Q: Query>(
        &self,
        db: &ElementDb<Q>,
        slot: &crate::cache::Slot<Q>,
        last_verified: Option<Revision>,
    ) -> Option<Durability> {
        let last_verified = last_verified?;

        let output = unsafe { slot.output_unchecked() };

        let revision = output.revision;
        let durability = output.durability;
        if !self.history.maybe_changed_since(revision, durability) {
            // the query cannot possibly have changed
            return Some(durability);
        }

        let mut new_durability = Durability::Constant;

        for dependency in output.dependencies.iter() {
            let change = db.last_change(dependency.query())?;
            if change.revision > last_verified {
                return None;
            }
            new_durability = std::cmp::min(new_durability, change.durability);
        }

        Some(new_durability)
    }

    pub(crate) unsafe fn execute_with_info<Q: Query, R>(
        &self,
        db: &ElementDb<Q>,
        path: ElementPath,
        slot: &crate::cache::Slot<Q>,
        callback: impl FnOnce(Q::Output, ExecutionInfo) -> R,
    ) -> R {
        self.begin_query(path, Durability::Constant, Q::IS_INPUT);

        let args = slot.arguments_unchecked();

        let output = stacker::maybe_grow(
            usize::max(Q::REQUIRED_STACK, 32 * 1024),
            usize::max(Q::REQUIRED_STACK, MIN_STACK),
            || Q::execute(db, args.clone()),
        );

        self.end_query(|info| callback(output, info))
    }

    #[inline]
    pub(crate) unsafe fn spawn<'a, Q: Query>(
        &'a self,
        db: &'a ElementDb<Q>,
        slot: &'a crate::cache::Slot<Q>,
        path: ElementPath,
        last_verified: Option<Revision>,
        stack: StackId,
    ) {
        let state = TaskState {
            db: DynPointer::erase(db as *const _),
            slot: slot as *const _ as *const (),
            path,
            last_verified,
            stack,
        };

        let task = Task {
            state,
            execute: |runtime, state| {
                let db = unsafe { &*state.db.unerase::<ElementDb<Q>>() };
                let slot = unsafe { &*state.slot.cast::<crate::cache::Slot<Q>>() };

                ACTIVE.with(|active| {
                    let old = active.borrow_mut().replace(ActiveStack::new(state.stack));
                    runtime.execute(db, slot, state.path, state.last_verified);
                    *active.borrow_mut() = old;
                    runtime.free_stack(state.stack);
                })
            },
        };

        self.spawn_task(path, task);
    }

    fn spawn_task(&self, query: ElementPath, task: Task) {
        self.with_local(|local| local.worker.push(query))
            .expect("spawned query outside thread scope");
        self.tasks.insert(query, task);
        self.wake_one();
    }

    fn next_query(&self) -> Option<ElementPath> {
        self.with_local(|local| local.worker.pop().or_else(|| self.try_steal_task(local)))?
    }

    fn try_steal_task(&self, local: &LocalQueue) -> Option<ElementPath> {
        let workers = self.workers.load();
        let stealers = workers.stealers.as_slice();

        let first = fastrand::usize(0..stealers.len());
        let (before, after) = stealers.split_at(first);

        loop {
            let mut retry = false;

            for stealer in before.iter().chain(after) {
                use crossbeam_deque::Steal;
                match stealer.steal_batch_and_pop(&local.worker) {
                    Steal::Empty => continue,
                    Steal::Success(task) => return Some(task),
                    Steal::Retry => retry = true,
                }
            }

            if !retry {
                return None;
            }
        }
    }

    fn with_local<R>(&self, callback: impl FnOnce(&LocalQueue) -> R) -> Option<R> {
        LOCAL_QUEUE.with(|local| Some(callback(self.init_local(&mut local.borrow_mut())?)))
    }

    fn init_local<'a>(&self, local: &'a mut Option<LocalQueue>) -> Option<&'a LocalQueue> {
        let scope = self.thread_scope.as_ref()?;

        let recreate = match local.as_ref() {
            None => true,
            Some(local) => local.thread_scope.as_ptr() != Arc::as_ptr(scope),
        };

        if recreate {
            let worker = Worker::new_lifo();
            let stealer = worker.stealer();

            self.workers.rcu(|workers| workers.add(stealer.clone()));

            *local = Some(LocalQueue {
                thread_scope: Arc::downgrade(scope),
                worker,
            });
        }

        local.as_ref()
    }

    pub(crate) fn block_until_ready(
        &self,
        path: ElementPath,
        claimant: StackId,
        state: &SlotState,
    ) {
        // if the query has been spawned in the runtime, try executing it immediately
        if let Some((_, task)) = self.tasks.remove(&path) {
            task.run(self);
            if state.is_ready(self.current_revision(), Acquire) {
                return;
            }
        }

        let current = self.current_stack();

        // check for dependency cycles
        {
            let mut blocker = cycle::Block {
                blocked_on: claimant,
                stack: ACTIVE.with(|active| active.borrow_mut().take()).unwrap(),
            };

            // Add a dependency on the query (used to collect precise cycle traces).
            // This is undone at the end of this function.
            blocker.stack.dependencies.push(Dependency {
                element: path.element,
                slot: path.slot,
                spawn_group: None,
            });

            if let Some(cycle) = self.cycles.insert(blocker) {
                panic!("dependency cycle: {cycle:?}");
            }
        }

        // keep running other tasks until the query completes
        {
            let mut next_query = None;
            while !state.is_ready(self.current_revision(), Relaxed) {
                if let Some(query) = next_query.take().or_else(|| self.next_query()) {
                    if let Some((_, task)) = self.tasks.remove(&query) {
                        task.run(self);
                    }
                    continue;
                }

                let validate = || {
                    next_query = self.next_query();
                    next_query.is_none()
                };
                self.wait_on_query(state, validate);
            }
        }

        let mut stack = self
            .cycles
            .remove(current)
            .expect("query stack has been deleted");

        stack.dependencies.pop();

        ACTIVE.with(|active| active.borrow_mut().replace(stack));

        assert!(state.is_ready(self.current_revision(), Acquire));
    }

    fn wait_on_query(&self, state: &SlotState, validate: impl FnOnce() -> bool) {
        let key = self as *const _ as usize;
        let validate = || !state.is_ready(self.current_revision(), Relaxed) && validate();
        unsafe { parking_lot_core::park(key, validate, || {}, |_, _| {}, park_token(state), None) };
    }

    fn wake_query(&self, state: &SlotState) {
        let key = self as *const _ as usize;
        let wake_token = park_token(state);
        let filter = |token| {
            if token == wake_token {
                parking_lot_core::FilterOp::Unpark
            } else {
                parking_lot_core::FilterOp::Skip
            }
        };
        let callback = |_| parking_lot_core::DEFAULT_UNPARK_TOKEN;
        unsafe { parking_lot_core::unpark_filter(key, filter, callback) };
    }

    fn wake_one(&self) {
        let key = self as *const _ as usize;
        let callback = |_| parking_lot_core::DEFAULT_UNPARK_TOKEN;
        unsafe { parking_lot_core::unpark_one(key, callback) };
    }
}

fn park_token(state: &SlotState) -> parking_lot_core::ParkToken {
    parking_lot_core::ParkToken(state as *const _ as usize)
}

thread_local! {
    static LOCAL_QUEUE: RefCell<Option<LocalQueue>> = RefCell::new(None);
}

struct LocalQueue {
    thread_scope: Weak<ThreadScope>,
    worker: Worker<ElementPath>,
}

thread_local! {
    static ACTIVE: RefCell<Option<ActiveStack>> = RefCell::new(None);
}

struct ActiveStack {
    id: StackId,
    queries: Vec<QueryData>,
    dependencies: Vec<Dependency>,
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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Dependency {
    pub(crate) element: ElementId,
    pub(crate) slot: SlotId,
    pub(crate) spawn_group: Option<SpawnGroup>,
}

const _: () = assert!(
    std::mem::size_of::<Dependency>() == 8,
    "dependencies should be kept small"
);

impl Dependency {
    pub(crate) fn query(self) -> ElementPath {
        ElementPath {
            element: self.element,
            slot: self.slot,
        }
    }
}

impl std::fmt::Debug for Dependency {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.query().fmt(f)
    }
}

/// Queries spawned at the same time -- without having awaited another query in-between -- will
/// belong to the same spawn group. This indicates that the queries may have executed in parallel.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct SpawnGroup {
    id: NonZeroU16,
}

impl SpawnGroup {
    fn new(dependency_count: usize) -> Option<Self> {
        if dependency_count >= usize::from(u16::MAX) {
            return None;
        }

        let index = dependency_count as u16;
        let id = unsafe { NonZeroU16::new_unchecked(index + 1) };
        Some(SpawnGroup { id })
    }
}

pub struct LastChange {
    pub(crate) revision: Revision,
    pub(crate) durability: Durability,
}

struct QueryData {
    path: ElementPath,
    /// Number of dependencies registered for this query. Corresponds to the last dependencies in
    /// the active stack.
    dependency_count: usize,
    durability: Durability,
    is_input: bool,
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

pub struct ExecutionInfo<'a> {
    pub durability: Durability,
    pub dependencies: &'a [Dependency],
}

struct Task {
    state: TaskState,
    execute: ExecuteFn,
}

impl Task {
    fn run(self, runtime: &Runtime) {
        (self.execute)(runtime, self.state)
    }
}

type ExecuteFn = fn(&Runtime, TaskState);

struct TaskState {
    /// Type-erased database
    db: DynPointer,
    /// Type-erased pointer to the query's [`crate::cache::Slot`]
    slot: *const (),
    /// Path to the query.
    path: ElementPath,
    /// Revision when the query was last verified.
    last_verified: Option<Revision>,
    /// Stack which should be used when executing the query.
    stack: StackId,
}

#[derive(Default)]
struct WorkerState {
    stealers: SmallVec<[Stealer<ElementPath>; 32]>,
}

impl WorkerState {
    pub fn add(&self, stealer: Stealer<ElementPath>) -> Self {
        let mut stealers = SmallVec::with_capacity(self.stealers.len());
        stealers.extend(self.stealers.iter().cloned());
        stealers.push(stealer);
        Self { stealers }
    }
}

struct ThreadScope;
