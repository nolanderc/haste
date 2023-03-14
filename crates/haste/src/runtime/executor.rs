mod injector;
mod task;

use std::{
    cell::{Cell, UnsafeCell},
    future::Future,
    mem::{ManuallyDrop, MaybeUninit},
    pin::Pin,
    sync::{
        atomic::{
            AtomicU32, AtomicUsize,
            Ordering::{self, Acquire, Relaxed, Release},
        },
        Arc, Condvar, Mutex, Weak,
    },
    task::{Poll, RawWaker, RawWakerVTable, Waker},
    thread::JoinHandle,
};

use crate::util::CallOnDrop;

use self::{injector::Injector, task::Task};

pub use self::task::RawTask;

pub struct Executor {
    /// State shared between all worker threads.
    shared: Arc<Shared>,

    /// List of all worker threads.
    threads: Vec<JoinHandle<()>>,

    /// The "main" thread also has a scheduler to which it can spawn and run tasks.
    local: Mutex<Option<LocalScheduler>>,
}

struct Shared {
    /// Handle to the tokio runtime.
    ///
    /// This is only used so that tasks in our executor can offload IO-bound work if necessary. No
    /// tasks may be spawned in the tokio runtime, as we cannot guarantee that they are dropped
    /// when `stop` is called.
    tokio_handle: tokio::runtime::Handle,

    injector: Injector,
    workers: Vec<WorkerState>,
    state: SharedState,

    /// Aprroximate number of threads that are currently suspended and waiting for work.
    idle_workers_approx: AtomicUsize,
    /// Suspended tasks which are waiting for more work hold this lock.
    idle_mutex: Mutex<()>,
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
    variant: AtomicU32,
}

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum State {
    Shutdown = 0,
    Running = 1,
    Terminated = 2,
}

impl SharedState {
    fn new(variant: State) -> Self {
        Self {
            variant: AtomicU32::new(variant as u32),
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

type LocalQueue = st3::lifo::Worker<Task>;
type Stealer = st3::lifo::Stealer<Task>;

const MAX_LOCAL_TASKS: usize = 256;

impl Executor {
    pub fn new(tokio_handle: tokio::runtime::Handle) -> Self {
        let worker_count = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(8);

        let workers = (0..worker_count + 1)
            .map(|_| LocalQueue::new(MAX_LOCAL_TASKS))
            .collect::<Vec<_>>();

        let shared = Arc::new(Shared {
            tokio_handle,

            injector: Injector::new(),
            workers: workers
                .iter()
                .map(|worker| WorkerState {
                    stealer: worker.stealer(),
                })
                .collect(),

            state: SharedState::new(State::Shutdown),

            idle_workers_approx: AtomicUsize::new(0),
            idle_mutex: Mutex::new(()),
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
        for local in locals.by_ref().take(worker_count) {
            threads.push(std::thread::spawn(move || {
                local.run();
            }));
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
        assert_eq!(
            self.shared.state.load(Relaxed),
            State::Running,
            concat!(
                "can only spawn tasks on a running executor",
                "\nhelp: call `haste::scope` to start the task executor"
            )
        );

        let task = Task::from_raw(task);
        self.shared.schedule(task);
    }

    pub fn start(&self) -> bool {
        let shared = &*self.shared;

        let result = shared.state.compare_exchange(
            State::Shutdown,
            State::Running,
            Ordering::Relaxed,
            Ordering::Relaxed,
        );
        result.is_ok()
    }

    pub fn stop(&self) -> bool {
        let shared = &self.shared;

        let result = shared.state.compare_exchange(
            State::Running,
            State::Shutdown,
            Ordering::Relaxed,
            Ordering::Relaxed,
        );
        if result.is_err() {
            return false;
        }

        // notify the workers that we are now in shutdown
        {
            let _guard = shared.idle_mutex.lock().unwrap();
            shared.wake_condition.notify_all();
        }

        // wait until all workers are suspended:
        {
            let worker_count = shared.workers.len();
            let mut suspended_workers = shared.suspended_workers.lock().unwrap();

            // we might hold one of the workers, which we need to account for
            let local = match self.local.lock() {
                Ok(local) => local,
                Err(poison) => poison.into_inner(),
            };
            *suspended_workers += local.is_some() as usize;

            while *suspended_workers != worker_count {
                suspended_workers = shared.suspended_condition.wait(suspended_workers).unwrap();
            }

            *suspended_workers -= local.is_some() as usize;
        }

        true
    }

    fn terminate(&mut self) {
        self.shared.state.store(State::Terminated, Ordering::SeqCst);
        self.shared.start_condition.notify_all();
        self.shared.wake_condition.notify_all();

        for thread in self.threads.drain(..) {
            thread.join().unwrap();
        }
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
        if self.idle_workers_approx.load(Relaxed) != 0 {
            self.wake_condition.notify_one();
        } else if self.suspended_workers_approx.load(Relaxed) != 0 {
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
    static LOCAL: UnsafeCell<Option<LocalScheduler>> = UnsafeCell::new(None);
}

impl LocalScheduler {
    fn new(shared: Arc<Shared>, queue: LocalQueue) -> Self {
        Self {
            shared,
            queue,
            reserved_next: Cell::new(None),
        }
    }

    fn run(mut self) -> Self {
        (self, _) = self.enter(|local| {
            let _suspend_guard = CallOnDrop(|| {
                // When the worker exits, mark it as suspended so that the executor can terminate
                // gracefully without waiting endlessly for this thread to complete:
                if let Ok(mut suspended) = local.shared.suspended_workers.try_lock() {
                    *suspended += 1;
                }
            });

            while let Some(task) = local.next_task() {
                task.poll();
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
            let max_stalled_count: u32 = 10;

            loop {
                if task_state.ready.load(Relaxed) != 0 {
                    // the future may have made some progress, try polling it again.
                    task_state.ready.store(0, Relaxed);
                    if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
                        break output;
                    }
                }

                if let Some(task) = local.try_next_task() {
                    stalled_count = 0;
                    task.poll();
                } else {
                    stalled_count = stalled_count.saturating_add(1);

                    if stalled_count >= max_stalled_count {
                        std::thread::yield_now();
                    } else {
                        std::hint::spin_loop();
                    }
                }
            }
        });

        this.publish_reserved_tasks();

        (this, output)
    }

    fn try_with<T>(f: impl FnOnce(Option<&LocalScheduler>) -> T) -> T {
        LOCAL.with(|cell| {
            let local = unsafe { (*cell.get()).as_ref() };
            f(local)
        })
    }

    fn enter<T>(mut self, f: impl FnOnce(&LocalScheduler) -> T) -> (LocalScheduler, T) {
        LOCAL.with(|cell| {
            let ptr = cell.get();

            let local = unsafe {
                assert!(
                    (*ptr).is_none(),
                    "a single thread cannot have two active schedulers"
                );
                ptr.write(Some(self));
                (*ptr).as_ref().unwrap_unchecked()
            };

            let tokio_guard = local.shared.tokio_handle.enter();
            let output = f(local);
            drop(tokio_guard);

            self = unsafe { (*ptr).take().unwrap_unchecked() };

            (self, output)
        })
    }

    fn try_next_task(&self) -> Option<Task> {
        self.try_next_local()
            .or_else(|| self.try_next_global())
            .or_else(|| self.try_next_steal())
    }

    fn drain(&self) {
        loop {
            self.reserved_next.take();

            while let Ok(items) = self.queue.drain(|n| n) {
                items.for_each(drop);
            }

            self.shared.injector.drain();

            if self.try_next_local().is_none() && self.try_next_global().is_none() {
                break;
            }
        }
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
        use st3::StealError;

        let workers = &self.shared.workers;

        loop {
            // pick a random order to steal tasks from the other workers
            let start = fastrand::usize(0..workers.len());
            let (left, right) = workers.split_at(start);
            let order = right.iter().chain(left.iter());

            let mut retry = false;

            for worker in order {
                match worker.stealer.steal_and_pop(&self.queue, |n| n / 2) {
                    Err(StealError::Empty) => continue,
                    Err(StealError::Busy) => retry = true,
                    Ok((task, _count)) => return Some(task),
                }
            }

            if !retry {
                return None;
            }

            std::hint::spin_loop();
        }
    }

    fn next_task(&self) -> Option<Task> {
        if self.shared.state.load(Relaxed) == State::Running {
            if let Some(task) = self.try_next_task() {
                return Some(task);
            }
        }

        self.suspend()
    }

    fn suspend(&self) -> Option<Task> {
        let shared = &*self.shared;

        loop {
            match shared.state.load(Relaxed) {
                State::Terminated => return None,
                State::Shutdown => self.suspend_shutdown(),
                State::Running => {
                    if let Some(task) = self.suspend_running() {
                        return Some(task);
                    }
                }
            };
        }
    }

    fn suspend_running(&self) -> Option<Task> {
        let shared = &*self.shared;

        shared.idle_workers_approx.fetch_add(1, Relaxed);
        let _guard = CallOnDrop(|| shared.idle_workers_approx.fetch_sub(1, Relaxed));

        let mut guard = shared.idle_mutex.lock().unwrap();

        while shared.state.load(Relaxed) == State::Running {
            if let Some(task) = self.try_next_task() {
                return Some(task);
            }
            guard = shared.wake_condition.wait(guard).unwrap();
        }

        None
    }

    fn suspend_shutdown(&self) {
        self.drain();

        let shared = &*self.shared;

        shared.suspended_workers_approx.fetch_add(1, Relaxed);
        let _guard = CallOnDrop(|| shared.suspended_workers_approx.fetch_sub(1, Relaxed));

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
        if let Some(old) = self.reserved_next.replace(Some(task)) {
            self.schedule_stealable(old);
        }
    }

    fn schedule_stealable(&self, task: Task) {
        match self.queue.push(task) {
            Ok(()) => self.shared.try_wake_suspended(),

            // too many tasks in the local queue:
            Err(task) => self.shared.schedule_global(task),
        }
    }
}
