mod coro;
mod cycle;
mod history;

use std::{
    cell::{Cell, RefCell},
    num::{NonZeroU16, NonZeroU32},
    ptr::NonNull,
    sync::{
        atomic::{
            AtomicBool, AtomicU64, AtomicUsize,
            Ordering::{Acquire, Relaxed},
        },
        Arc, Mutex,
    },
};

use arc_swap::ArcSwap;
use crossbeam_channel::Sender;
use crossbeam_deque::{Injector, Stealer, Worker};
use dashmap::DashMap;
use hashbrown::HashMap;
use smallvec::{smallvec, SmallVec};

use crate::{
    cache::{SlotId, SlotState},
    durability::Durability,
    revision::Revision,
    util::{CallOnDrop, DynPointer},
    Database, Element, ElementDb, ElementId, ElementPath, Query,
};

use self::{
    coro::{Coroutine, Yielder},
    cycle::CycleGraph,
    history::History,
};

/// Smallest stack size to allocate for queries (in bytes).
const MIN_STACK: usize = 512 * 1024;

pub struct Runtime {
    stack_ids: StackIdAllocator,

    cycles: CycleGraph,
    history: History,

    running: AtomicBool,

    thread_scope: Option<Arc<ThreadScope>>,
    injector: Injector<ElementPath>,
    tasks: DashMap<ElementPath, Task>,
    workers: ArcSwap<WorkerState>,
    suspended: DashMap<ElementPath, SuspendState>,
    suspended_count: AtomicUsize,
}

unsafe impl Send for Runtime {}
unsafe impl Sync for Runtime {}

impl Runtime {
    pub(crate) fn new() -> Self {
        Self {
            stack_ids: StackIdAllocator::new(),
            cycles: CycleGraph::new(),
            history: History::new(),
            running: AtomicBool::new(false),
            thread_scope: None,
            injector: Injector::new(),
            tasks: DashMap::with_capacity(1024),
            workers: Default::default(),
            suspended: DashMap::with_capacity(1024),
            suspended_count: AtomicUsize::new(0),
        }
    }

    #[inline]
    pub(crate) unsafe fn enter(&mut self) {
        assert!(self.thread_scope.is_none(), "cannot nest scopes");
        self.thread_scope = Some(Arc::new(ThreadScope));
        *self.running.get_mut() = true;
    }

    #[inline]
    pub(crate) unsafe fn exit(&mut self) {
        assert!(self.thread_scope.is_some(), "scope was not entered");
        *self.running.get_mut() = false;
        self.tasks.clear();
        self.cycles.clear();
        std::mem::take(&mut self.workers);
        self.suspended.clear();
        self.thread_scope = None;
        self.stack_ids = StackIdAllocator::new();
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
    pub(crate) unsafe fn free_stack(&self, stack: StackId) {
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

                assert!(
                    !query.is_input,
                    "input queries may not invoke other queries"
                );

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
            if let Some((_, suspended)) = self.suspended.remove(&path) {
                let workers = self.workers.load();

                let mut parked = false;
                let mut blocked = SmallBitSet::with_capacity(workers.len());

                for stack in suspended.stacks {
                    if stack.worker == u32::MAX {
                        parked = true;
                        continue;
                    }

                    let worker = workers.get(stack.worker);

                    _ = worker.sender.send(stack.id);

                    if worker.blocked.load(Relaxed) {
                        blocked.set(stack.worker as usize);
                    }
                }

                if parked {
                    self.wake_query(slot.state());
                }

                self.wake_blocked(&blocked);
            }
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

        let min_stack_size = (2 * coro::current_stack_size().unwrap_or(0)).max(MIN_STACK);

        let output = coro::maybe_grow(
            usize::max(Q::REQUIRED_STACK, 8 * 1024),
            usize::max(Q::REQUIRED_STACK, min_stack_size),
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
            min_stack_size: usize::max(MIN_STACK, Q::REQUIRED_STACK),
        };

        let task = Task {
            state,
            execute: |state| {
                let db = unsafe { state.database::<Q>() };
                let slot = unsafe { state.slot::<Q>() };

                let runtime = db.runtime();

                ACTIVE.with(|active| {
                    let old = active.borrow_mut().replace(ActiveStack::new(state.stack));
                    runtime.execute(db, slot, state.path, state.last_verified);
                    *active.borrow_mut() = old;
                    runtime.free_stack(state.stack)
                })
            },
            drop: |state| unsafe { state.slot::<Q>().release_claim() },
        };

        self.spawn_task(path, task);
    }

    fn spawn_task(&self, query: ElementPath, task: Task) {
        assert!(
            self.thread_scope.is_some(),
            "cannot spawn tasks outside a thread scope"
        );
        self.tasks.insert(query, task);
        self.injector.push(query);
        self.wake_task();
    }

    fn next_query(&self, local: &Worker<ElementPath>) -> Option<ElementPath> {
        local.pop().or_else(|| self.try_steal_task(local))
    }

    fn try_steal_task(&self, local: &Worker<ElementPath>) -> Option<ElementPath> {
        loop {
            let mut retry = false;

            match self.injector.steal_batch_and_pop(local) {
                crossbeam_deque::Steal::Empty => {}
                crossbeam_deque::Steal::Success(query) => return Some(query),
                crossbeam_deque::Steal::Retry => retry = true,
            }

            let workers = self.workers.load();
            let workers = workers.data.as_slice();

            let first = fastrand::usize(0..workers.len());
            let (before, after) = workers.split_at(first);

            let order = after.iter().chain(before);

            for worker in order {
                use crossbeam_deque::Steal;

                match worker.stealer.steal_batch_and_pop(local) {
                    Steal::Empty => {}
                    Steal::Success(query) => return Some(query),
                    Steal::Retry => retry = true,
                }
            }

            if !retry {
                return None;
            }
        }
    }

    fn init_worker(&self, data: WorkerData) -> u32 {
        let mut index = 0;

        self.workers.rcu(|workers| {
            let state;
            (state, index) = workers.add(data.clone());
            state
        });

        index
    }

    pub fn drive(&self, thread_count: usize) {
        assert!(self.thread_scope.is_some(), "not within a thread scope");
        YIELDER.with(|y| {
            assert!(y.get().is_none(), "cannot nest thread scope");
        });

        let blocked = Arc::new(AtomicBool::new(false));
        let (sender, receiver) = crossbeam_channel::unbounded();
        let worker = Worker::new_lifo();

        let index = self.init_worker(WorkerData {
            blocked: blocked.clone(),
            sender,
            stealer: worker.stealer(),
        });

        let mut suspended = HashMap::new();

        let mut next_suspended = None;

        while self.running.load(Relaxed) {
            if let Some(stack) = next_suspended.take().or_else(|| receiver.try_recv().ok()) {
                if let Some(task) = suspended.remove(&stack) {
                    self.suspended_count.fetch_sub(1, Relaxed);
                    self.poll_task(task, &mut suspended);
                }
                continue;
            }

            let total_suspended = self.suspended_count.load(Relaxed);
            if total_suspended < 4096
                && (suspended.len() < 32
                    || suspended.len() <= 2 * (total_suspended + thread_count - 1) / thread_count)
            {
                if let Some(query) = self.next_query(&worker) {
                    if let Some((_, task)) = self.tasks.remove(&query) {
                        let task = self.create_task(task, index);
                        self.poll_task(task, &mut suspended);
                    }
                    continue;
                }
            }

            blocked.store(true, Relaxed);
            self.wait_on_task(index, || {
                next_suspended = receiver.try_recv().ok();
                next_suspended.is_none() && self.running.load(Relaxed)
            });
            blocked.store(false, Relaxed);
        }
    }

    fn create_task(&self, task: Task, worker: u32) -> SuspendedTask {
        let coro = Coroutine::new(task.state.min_stack_size, move |yielder| {
            YIELDER.with(|y| {
                y.set(Some(StaticYielder {
                    raw: NonNull::new(yielder).unwrap(),
                    worker,
                }))
            });

            let _guard = CallOnDrop::new(move || YIELDER.with(|y| y.set(None)));

            task.run();
        })
        .expect("could not allocate stack space for query");

        SuspendedTask { coro }
    }

    fn poll_task(&self, mut task: SuspendedTask, suspended: &mut HashMap<StackId, SuspendedTask>) {
        match task.coro.resume() {
            std::ops::ControlFlow::Break(()) => {}
            std::ops::ControlFlow::Continue(stack) => {
                suspended.insert(stack, task);
                self.suspended_count.fetch_add(1, Relaxed);
            }
        }
    }

    pub fn stop(&self) {
        self.running.store(false, Relaxed);
        self.wake_all_workers();
    }

    pub(crate) fn block_until_ready(
        &self,
        path: ElementPath,
        claimant: StackId,
        state: &SlotState,
    ) {
        // if the query has been spawned in the runtime, try executing it immediately
        if let Some((_, task)) = self.tasks.remove(&path) {
            task.run();
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

        self.wait_on_query(path, state, current);

        // restore the current stack
        let mut stack = self
            .cycles
            .remove(current)
            .expect("query stack has been deleted");

        stack.dependencies.pop();

        ACTIVE.with(|active| active.borrow_mut().replace(stack));

        assert!(state.is_ready(self.current_revision(), Acquire));
    }

    fn wait_on_query(&self, path: ElementPath, state: &SlotState, stack: StackId) {
        let (worker, yielder) = YIELDER.with(|y| match y.take() {
            None => (u32::MAX, None),
            Some(yielder) => (yielder.worker, Some(yielder.raw)),
        });
        let _guard = CallOnDrop::new(|| {
            if let Some(raw) = yielder {
                YIELDER.with(|y| y.set(Some(StaticYielder { raw, worker })))
            }
        });

        let entry = self.suspended.entry(path);

        if !state.set_blocking(Relaxed) && state.is_ready(self.current_revision(), Relaxed) {
            return;
        }

        let suspend = SuspendedStack { id: stack, worker };
        entry.or_default().stacks.push(suspend);

        // yield back to the scheduler if we are a child task
        if let Some(yielder) = yielder {
            loop {
                unsafe { (*yielder.as_ptr()).yield_(stack) };
                if state.is_ready(self.current_revision(), Relaxed) {
                    break;
                }
            }
            return;
        }

        // block until the query is completed otherwise
        loop {
            let validate = || !state.is_ready(self.current_revision(), Relaxed);
            unsafe {
                parking_lot_core::park(
                    self.query_key(),
                    validate,
                    || {},
                    |_, _| {},
                    park_token(state),
                    None,
                )
            };

            if state.is_ready(self.current_revision(), Relaxed) {
                break;
            }
        }
    }

    fn wake_query(&self, state: &SlotState) {
        let wake_token = park_token(state);
        let filter = |token| {
            if token == wake_token {
                parking_lot_core::FilterOp::Unpark
            } else {
                parking_lot_core::FilterOp::Skip
            }
        };
        let callback = |_| parking_lot_core::DEFAULT_UNPARK_TOKEN;
        unsafe { parking_lot_core::unpark_filter(self.query_key(), filter, callback) };
    }

    fn wait_on_task(&self, worker: u32, validate: impl FnOnce() -> bool) {
        unsafe {
            parking_lot_core::park(
                self.task_key(),
                validate,
                || {},
                |_, _| {},
                parking_lot_core::ParkToken(worker as usize),
                None,
            )
        };
    }

    fn wake_task(&self) {
        let callback = |_| parking_lot_core::DEFAULT_UNPARK_TOKEN;
        unsafe { parking_lot_core::unpark_one(self.task_key(), callback) };
    }

    fn wake_blocked(&self, workers: &SmallBitSet) {
        let callback = |_| parking_lot_core::DEFAULT_UNPARK_TOKEN;
        unsafe {
            parking_lot_core::unpark_filter(
                self.task_key(),
                |token| {
                    if workers.get(token.0) {
                        parking_lot_core::FilterOp::Unpark
                    } else {
                        parking_lot_core::FilterOp::Skip
                    }
                },
                callback,
            )
        };
    }

    fn wake_all_workers(&self) {
        unsafe {
            parking_lot_core::unpark_all(self.task_key(), parking_lot_core::DEFAULT_UNPARK_TOKEN);
        }
    }

    fn query_key(&self) -> usize {
        self as *const _ as usize + 1
    }

    fn task_key(&self) -> usize {
        self as *const _ as usize + 2
    }
}

fn park_token(state: &SlotState) -> parking_lot_core::ParkToken {
    parking_lot_core::ParkToken(state as *const _ as usize)
}

thread_local! {
    static WORKER: Cell<Option<u32>> = Cell::new(None);
}

thread_local! {
    static YIELDER: Cell<Option<StaticYielder>> = Cell::new(None);
}

#[derive(Clone, Copy)]
struct StaticYielder {
    raw: NonNull<Yielder<(), StackId>>,
    worker: u32,
}

struct SuspendedTask {
    coro: Coroutine<(), StackId>,
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
    drop: DropFn,
}

impl Task {
    fn run(self) {
        (self.execute)(&self.state);
        std::mem::forget(self);
    }
}

impl Drop for Task {
    fn drop(&mut self) {
        (self.drop)(&self.state)
    }
}

type ExecuteFn = fn(&TaskState);
type DropFn = fn(&TaskState);

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
    /// Requested stack size.
    min_stack_size: usize,
}

impl TaskState {
    unsafe fn database<E: Element>(&self) -> &ElementDb<E> {
        &*self.db.unerase()
    }

    unsafe fn slot<Q: Query>(&self) -> &crate::cache::Slot<Q> {
        &*self.slot.cast()
    }
}

#[derive(Default)]
struct WorkerState {
    data: SmallVec<[WorkerData; 32]>,
}

impl WorkerState {
    pub fn add(&self, new: WorkerData) -> (Self, u32) {
        let index = u32::try_from(self.data.len()).expect("exhausted number of workers");

        let mut data = SmallVec::with_capacity(self.data.len());
        data.extend(self.data.iter().cloned());
        data.push(new);

        (Self { data }, index)
    }

    pub fn get(&self, index: u32) -> &WorkerData {
        &self.data[index as usize]
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

#[derive(Clone)]
struct WorkerData {
    stealer: Stealer<ElementPath>,
    sender: Sender<StackId>,
    blocked: Arc<AtomicBool>,
}

struct ThreadScope;

#[derive(Default)]
struct SuspendState {
    stacks: SmallVec<[SuspendedStack; 2]>,
}

struct SuspendedStack {
    id: StackId,
    worker: u32,
}

struct SmallBitSet {
    words: SmallVec<[u64; 4]>,
}

impl SmallBitSet {
    pub fn with_capacity(len: usize) -> Self {
        Self {
            words: smallvec![0; (len + 63) / 64],
        }
    }

    pub fn set(&mut self, index: usize) {
        self.words[index / 64] |= Self::mask(index);
    }

    pub fn get(&self, index: usize) -> bool {
        self.words[index / 64] & Self::mask(index) != 0
    }

    #[allow(dead_code)]
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.words.iter().enumerate().flat_map(|(i, word)| {
            let mut word = *word;
            let mut index = i * 64;
            std::iter::from_fn(move || {
                if word == 0 {
                    return None;
                }

                let offset = word.trailing_zeros();
                word >>= offset;
                word >>= 1;
                index += offset as usize;
                let next = index;
                index += 1;

                Some(next)
            })
        })
    }

    fn mask(index: usize) -> u64 {
        1 << (index % 64)
    }
}

#[test]
fn small_bitset() {
    let mut bits = SmallBitSet::with_capacity(128);
    bits.set(1);
    bits.set(64);
    bits.set(127);
    bits.set(13);
    bits.set(78);

    assert_eq!(bits.iter().collect::<Vec<_>>(), [1, 13, 64, 78, 127]);
}
