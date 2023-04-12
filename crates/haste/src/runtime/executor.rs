mod injector;
mod task;

use std::{
    cell::{Cell, RefCell},
    future::Future,
    mem::{ManuallyDrop, MaybeUninit},
    pin::Pin,
    sync::{
        atomic::{
            AtomicU32,
            Ordering::{self, Acquire, Relaxed, Release},
        },
        Arc, Condvar, Mutex, Weak,
    },
    task::{Poll, RawWaker, RawWakerVTable, Waker},
    thread::JoinHandle,
};

use crossbeam_utils::CachePadded;

use crate::util::CallOnDrop;

use self::task::Task;

pub use self::task::RawTask;

const WORKERS_ENV: &str = "HASTE_WORKERS";

pub struct Executor {
    /// State shared between all worker threads.
    shared: Arc<Shared>,

    /// List of all worker threads.
    threads: Vec<JoinHandle<()>>,

    /// The "main" thread also has a scheduler to which it can spawn and run tasks.
    local: Mutex<Option<LocalScheduler>>,
}

struct Shared {
    injector: Injector,
    workers: Vec<WorkerState>,
    state: SharedState,

    /// Aprroximate number of threads that are currently suspended and waiting for work.
    idle_workers_approx: AtomicU32,
    /// Suspended tasks which are waiting for more work hold this lock.
    idle_mutex: Mutex<usize>,
    /// Notified when a suspended worker has more work available.
    wake_condition: Condvar,

    /// Number of threads that are suspended after a shutdown.
    suspended_workers: Mutex<usize>,
    /// Approximate number of threads that are suspended after a shutdown.
    suspended_workers_approx: AtomicU32,
    /// Notified when an suspended worker should be started after a shutdown.
    start_condition: Condvar,
    /// Notified when a worker is put into an suspended state (during shutdown).
    suspended_condition: Condvar,
}

struct SharedState {
    // We expect this to be loaded by multiple threads continuously and rarely be written to. In
    // order to avoid accidental cache invalidation by neighbouring writes (false sharing) we make
    // sure it is padded to the length of a cache line.
    variant: CachePadded<AtomicU32>,
}

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Shutdown = 0,
    Running = 1,
    Terminated = 2,
    Panicked = 3,
}

impl SharedState {
    fn new(variant: State) -> Self {
        Self {
            variant: AtomicU32::new(variant as u32).into(),
        }
    }

    unsafe fn decode(x: u32) -> State {
        std::mem::transmute(x)
    }

    fn load(&self, order: Ordering) -> State {
        unsafe { Self::decode(self.variant.load(order)) }
    }

    fn store(&self, state: State, order: Ordering) {
        self.variant.store(state as u32, order)
    }

    fn compare_exchange(
        &self,
        current: State,
        new: State,
        success: Ordering,
        failure: Ordering,
    ) -> Result<State, State> {
        unsafe {
            self.variant
                .compare_exchange(current as u32, new as u32, success, failure)
                .map(|x| Self::decode(x))
                .map_err(|x| Self::decode(x))
        }
    }
}

struct WorkerState {
    stealer: Stealer,
}

type LocalQueue = crossbeam_deque::Worker<Task>;
type Stealer = crossbeam_deque::Stealer<Task>;
type Injector = injector::Injector;

pub fn worker_threads() -> usize {
    if let Ok(var) = std::env::var(WORKERS_ENV) {
        match var.parse::<usize>() {
            Ok(count) => return count,
            Err(error) => {
                tracing::warn!(
                    value = var,
                    %error,
                    "could not parse the value of {WORKERS_ENV}"
                );
            }
        }
    }

    num_cpus::get_physical().saturating_sub(1)
}

impl Executor {
    pub fn new() -> Self {
        let worker_count = worker_threads();

        let workers = (0..worker_count + 1)
            .map(|_| LocalQueue::new_lifo())
            .collect::<Vec<_>>();

        let shared = Arc::new(Shared {
            injector: Injector::new(),
            workers: workers
                .iter()
                .map(|worker| WorkerState {
                    stealer: worker.stealer(),
                })
                .collect(),

            state: SharedState::new(State::Shutdown),

            idle_workers_approx: AtomicU32::new(0),
            idle_mutex: Mutex::new(0),
            wake_condition: Condvar::new(),

            suspended_workers: Mutex::new(0),
            suspended_workers_approx: AtomicU32::new(0),
            start_condition: Condvar::new(),
            suspended_condition: Condvar::new(),
        });

        let mut locals = workers
            .into_iter()
            .map(|worker| LocalScheduler::new(shared.clone(), worker));

        let mut threads = Vec::with_capacity(worker_count);
        for (index, local) in locals.by_ref().take(worker_count).enumerate() {
            let result = std::thread::Builder::new()
                .name(format!("haste-worker-{index}"))
                .spawn(move || {
                    local.run(index);
                });

            match result {
                Ok(handle) => threads.push(handle),
                Err(error) => tracing::error!(%error, "could not spawn worker thread"),
            }
        }

        let local = locals.next();

        Self {
            shared,
            threads,
            local: Mutex::new(local),
        }
    }

    /// Drive the executor until the future completes.
    pub fn run<F>(&self, future: F) -> F::Output
    where
        F: Future,
    {
        let mut local_slot = self
            .local
            .try_lock()
            .expect("cannot run two tasks on the executor simultaneously");

        let local = local_slot.take().unwrap();

        let (local, output) = local.run_future(future);

        *local_slot = Some(local);
        output
    }

    pub fn create_task<F>(&self, create: impl FnOnce() -> F) -> Box<RawTask<F>>
    where
        F: Future<Output = ()>,
    {
        let executor = Arc::downgrade(&self.shared);
        RawTask::new_with(executor, create)
    }

    pub unsafe fn spawn<F>(&self, task: Box<RawTask<F>>)
    where
        F: Future<Output = ()> + Send,
    {
        let task = Task::from_raw(task);

        if self.shared.state.load(Relaxed) != State::Running {
            return;
        }

        self.shared.schedule(task);
    }

    /// Returns `true` if the executor is shutdown and does not accept new tasks.
    pub fn stopped(&self) -> bool {
        self.shared.state.load(Relaxed) != State::Running
    }

    pub fn start(&self) -> bool {
        let shared: &Shared = &self.shared;

        let result = shared.state.compare_exchange(
            State::Shutdown,
            State::Running,
            Ordering::Relaxed,
            Ordering::Relaxed,
        );
        result.is_ok()
    }

    pub fn stop(&self) -> bool {
        let result = self.shared.state.compare_exchange(
            State::Running,
            State::Shutdown,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );

        if matches!(result, Err(State::Shutdown | State::Terminated)) {
            return false;
        }

        self.wait_until_suspended();

        crate::publish_metrics();
        crate::print_global_metrics();

        true
    }

    fn wait_until_suspended(&self) {
        let shared: &Shared = &self.shared;

        // notify the workers that we are now in shutdown
        {
            let _guard = shared.idle_mutex.lock().unwrap();
            shared.wake_condition.notify_all();
        }

        {
            // if the local scheduler has any pending tasks we need to drop them:
            let guard = match self.local.try_lock() {
                Ok(guard) => Some(guard),
                Err(std::sync::TryLockError::Poisoned(poisoned)) => Some(poisoned.into_inner()),
                Err(std::sync::TryLockError::WouldBlock) => {
                    panic!("main scheduler still running when shutting down")
                }
            };
            if let Some(guard) = guard {
                if let Some(local) = guard.as_ref() {
                    local.drain();
                }
            }
        }

        // wait until all workers are suspended:
        {
            let worker_count = shared.workers.len();
            let mut suspended_workers = shared.suspended_workers.lock().unwrap();

            // we hold one of the workers, which we need to account for
            *suspended_workers += 1;

            while *suspended_workers != worker_count {
                suspended_workers = shared.suspended_condition.wait(suspended_workers).unwrap();
            }

            *suspended_workers -= 1;
        }
    }

    fn terminate(&mut self) {
        self.shared.state.store(State::Terminated, Ordering::SeqCst);
        self.shared.start_condition.notify_all();
        self.shared.wake_condition.notify_all();

        for thread in self.threads.drain(..) {
            _ = thread.join();
        }

        crate::print_global_metrics();
    }
}

impl Drop for Executor {
    fn drop(&mut self) {
        self.terminate();
    }
}

impl Shared {
    fn schedule(&self, task: Task) {
        LocalScheduler::try_with(move |local| {
            if let Some(local) = local {
                local.schedule(task);
            } else {
                self.schedule_global(task);
            }
        })
    }

    fn schedule_global(&self, task: Task) {
        self.injector.push(task);
        self.try_wake_suspended();
    }

    fn try_wake_suspended(&self) {
        let idle_count = self.idle_workers_approx.load(Relaxed) as usize;
        let suspended_count = self.suspended_workers_approx.load(Relaxed) as usize;

        if idle_count != 0 {
            self.wake_condition.notify_one();
        } else if suspended_count != 0 {
            self.start_condition.notify_one();
        }
    }
}

struct LocalScheduler {
    shared: Arc<Shared>,

    /// A queue of tasks that may be stolen by other workers.
    queue: LocalQueue,

    /// Each worker reserves the most recent task which was spawned on it.
    ///
    /// This optimizes for the common case where one query spawns another query, and then
    /// immediately awaits it. This way other threads don't immediately try to steal it, which in
    /// turn leads to better thread and cache locality and less contention on the stealers.
    reserved_next: Cell<Option<Task>>,
}

thread_local! {
    static LOCAL: RefCell<Option<LocalScheduler>> = RefCell::new(None);
}

impl LocalScheduler {
    fn new(shared: Arc<Shared>, queue: LocalQueue) -> Self {
        Self {
            shared,
            queue,
            reserved_next: Cell::new(None),
        }
    }

    fn run(mut self, _index: usize) -> Self {
        (self, _) = self.enter(|local| {
            let _suspend_guard = CallOnDrop(|| {
                // When the worker exits, mark it as suspended so that the executor can terminate
                // gracefully without waiting endlessly for this thread to complete:
                if let Ok(mut suspended) = local.shared.suspended_workers.lock() {
                    *suspended += 1;
                    local.shared.suspended_condition.notify_one();
                }
            });

            if local.shared.state.load(Relaxed) == State::Shutdown {
                local.suspend_shutdown();
            }

            while let Some(task) = local.next_task() {
                local.poll_task(task);
            }
        });
        self
    }

    fn run_future<F>(self, future: F) -> (Self, F::Output)
    where
        F: Future,
    {
        struct TaskState {
            ready: AtomicU32,
        }

        impl std::task::Wake for TaskState {
            fn wake(self: Arc<Self>) {
                self.wake_by_ref();
            }

            fn wake_by_ref(self: &Arc<Self>) {
                self.ready.store(1, Relaxed);
            }
        }

        let (this, output) = self.enter(move |local| {
            let task_state = Arc::new(TaskState {
                ready: AtomicU32::new(1),
            });

            let waker = Waker::from(task_state.clone());
            let mut cx = std::task::Context::from_waker(&waker);

            let mut future = std::pin::pin!(future);

            // number of times we have attempted to grab a task from the queue, but failed.
            let mut stalled_count: u32 = 0;
            let max_stalled_count: u32 = 100;

            let shared: &Shared = &local.shared;
            let mut in_deadlock = false;

            loop {
                if task_state.ready.swap(0, Relaxed) != 0 {
                    // the future may have made some progress, try polling it again.
                    if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
                        break output;
                    }
                }

                if shared.state.load(Relaxed) == State::Panicked {
                    panic!("worker thread panicked");
                }

                if let Some(task) = local.try_next_task() {
                    stalled_count = 0;
                    local.poll_task(task);
                } else {
                    stalled_count = stalled_count.saturating_add(1);

                    if stalled_count <= max_stalled_count {
                        std::hint::spin_loop();
                    } else {
                        if !in_deadlock {
                            // check for deadlock
                            let idle = shared.idle_mutex.lock().unwrap();
                            let suspended = shared.suspended_workers.lock().unwrap();

                            let not_running = 1 + *idle + *suspended;

                            if not_running >= shared.workers.len()
                                && task_state.ready.load(Relaxed) == 0
                            {
                                eprintln!("warn: stuck in deadlock");
                                in_deadlock = true;
                            }
                        }

                        std::thread::yield_now();
                    }
                }
            }
        });

        this.publish_reserved_tasks();

        (this, output)
    }

    fn poll_task(&self, task: Task) {
        task.poll();
    }

    fn try_with<T>(f: impl FnOnce(Option<&LocalScheduler>) -> T) -> T {
        LOCAL.with(|cell| {
            let local = cell.borrow();
            f(local.as_ref())
        })
    }

    fn enter<T>(mut self, f: impl FnOnce(&LocalScheduler) -> T) -> (LocalScheduler, T) {
        LOCAL.with(|cell| {
            let old = cell
                .try_borrow_mut()
                .expect("a single thread cannot have two active schedulers")
                .replace(self);

            let output = {
                let _guard = CallOnDrop(|| {
                    let mut local_ref = cell.borrow_mut();

                    if let Some(local) = local_ref.as_mut() {
                        // make sure we don't hold on to any dead state.
                        local.publish_reserved_tasks();

                        if std::thread::panicking() {
                            _ = local.shared.state.compare_exchange(
                                State::Running,
                                State::Panicked,
                                Ordering::SeqCst,
                                Ordering::SeqCst,
                            );

                            // make sure we don't leak the scheduler.
                            local_ref.take();
                        }
                    }
                });

                let local_ref = cell.borrow();
                let local = local_ref.as_ref().unwrap();

                f(local)
            };

            self = std::mem::replace(&mut *cell.borrow_mut(), old).unwrap();

            (self, output)
        })
    }

    fn try_next_task(&self) -> Option<Task> {
        self.try_next_local()
            .or_else(|| self.try_next_global())
            .or_else(|| self.try_next_steal())
    }

    fn drain(&self) {
        while self.try_next_task().is_some() {}
    }

    /// Makes any tasks reserved possible to be stolen by other workers.
    fn publish_reserved_tasks(&self) {
        if let Some(reserved) = self.reserved_next.take() {
            self.schedule_stealable(reserved);
        }
    }

    fn try_next_local(&self) -> Option<Task> {
        self.reserved_next.take().or_else(|| self.queue.pop())
    }

    fn try_next_global(&self) -> Option<Task> {
        self.shared.injector.pop()
    }

    fn try_next_steal(&self) -> Option<Task> {
        use crossbeam_deque::Steal;

        let workers = &self.shared.workers;

        loop {
            // pick a random order to steal tasks from the other workers
            let start = fastrand::usize(0..workers.len());
            let (left, right) = workers.split_at(start);
            let order = right.iter().chain(left.iter());

            let mut retry = false;

            for worker in order {
                match worker.stealer.steal_batch_and_pop(&self.queue) {
                    Steal::Empty => continue,
                    Steal::Retry => retry = true,
                    Steal::Success(task) => return Some(task),
                }
            }

            if !retry {
                return None;
            }

            std::hint::spin_loop();
        }
    }

    fn next_task(&self) -> Option<Task> {
        let backoff = crossbeam_utils::Backoff::new();

        for _ in 0..10 {
            if self.shared.state.load(Relaxed) != State::Running {
                break;
            }

            if let Some(task) = self.try_next_task() {
                return Some(task);
            }

            backoff.snooze();
        }

        self.suspend()
    }

    fn suspend(&self) -> Option<Task> {
        let shared: &Shared = &self.shared;

        loop {
            match shared.state.load(Relaxed) {
                State::Terminated => return None,
                State::Shutdown => {
                    self.drain();
                    self.suspend_shutdown();
                }
                State::Running => {
                    if let Some(task) = self.suspend_running() {
                        return Some(task);
                    }
                }
                State::Panicked => return None,
            };
        }
    }

    fn suspend_running(&self) -> Option<Task> {
        let _guard = crate::enter_span("idle");

        let shared: &Shared = &self.shared;

        shared.idle_workers_approx.fetch_add(1, Ordering::SeqCst);
        let _guard = CallOnDrop(|| shared.idle_workers_approx.fetch_sub(1, Ordering::SeqCst));

        let mut guard = shared.idle_mutex.lock().unwrap();
        *guard += 1;

        while shared.state.load(Relaxed) == State::Running {
            if let Some(task) = self.try_next_task() {
                *guard -= 1;
                return Some(task);
            }
            guard = shared.wake_condition.wait(guard).unwrap();
        }

        *guard -= 1;

        None
    }

    fn suspend_shutdown(&self) {
        crate::publish_metrics();

        let shared: &Shared = &self.shared;

        shared
            .suspended_workers_approx
            .fetch_add(1, Ordering::Relaxed);
        let _guard = CallOnDrop(|| {
            shared
                .suspended_workers_approx
                .fetch_sub(1, Ordering::Relaxed)
        });

        let mut suspended = shared.suspended_workers.lock().unwrap();

        *suspended += 1;
        if *suspended == shared.workers.len() {
            shared.suspended_condition.notify_one();
        }

        while shared.state.load(Relaxed) == State::Shutdown {
            suspended = shared.start_condition.wait(suspended).unwrap();
        }

        *suspended -= 1;
    }

    fn schedule(&self, task: Task) {
        if unsafe { (*self.reserved_next.as_ptr()).is_none() } {
            self.reserved_next.set(Some(task));
        } else {
            self.schedule_stealable(task);
        }
    }

    fn schedule_stealable(&self, task: Task) {
        self.queue.push(task);
        self.shared.try_wake_suspended();
    }
}
