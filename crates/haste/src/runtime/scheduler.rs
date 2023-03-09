mod task;

use std::{
    cell::UnsafeCell,
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
};

use self::task::Task;

pub struct Scheduler {
    shared: Arc<Shared>,
}

struct Shared {
    global_queue: GlobalQueue,
    workers: Vec<WorkerState>,
    state: SharedState,

    /// Number of threads currently suspended.
    suspended_workers: Mutex<usize>,

    /// Notified when a worker should be woken.
    wake_condition: Condvar,

    /// Notified when a worker is suspended.
    suspend_condition: Condvar,
}

struct SharedState {
    variant: AtomicU32,
}

#[repr(u32)]
enum State {
    Suspended = 0,
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

type GlobalQueue = crossbeam_deque::Injector<Task>;
type LocalQueue = crossbeam_deque::Worker<Task>;
type Stealer = crossbeam_deque::Stealer<Task>;

impl Scheduler {
    pub fn new() -> Self {
        let worker_count = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(8);

        let workers = (0..worker_count)
            .map(|_| LocalQueue::new_fifo())
            .collect::<Vec<_>>();

        let shared = Arc::new(Shared {
            global_queue: GlobalQueue::new(),
            workers: workers
                .iter()
                .map(|worker| WorkerState {
                    stealer: worker.stealer(),
                })
                .collect(),
            state: SharedState::new(State::Suspended),

            suspended_workers: Mutex::new(0),
            wake_condition: Condvar::new(),
            suspend_condition: Condvar::new(),
        });

        for worker in workers {
            let shared = shared.clone();
            std::thread::spawn(move || run_worker(shared, worker));
        }

        Self { shared }
    }

    pub fn spawn(&self, future: impl Future<Output = ()>) {
        self.shared.spawn(future)
    }

    pub fn start(&self) -> bool {
        let result = self.shared.state.compare_exchange(
            State::Suspended,
            State::Running,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        if result.is_err() {
            return false;
        }

        self.shared.wake_condition.notify_all();

        true
    }

    pub fn stop(&self) -> bool {
        let shared = &self.shared;

        let result = shared.state.compare_exchange(
            State::Running,
            State::Suspended,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        if result.is_err() {
            return false;
        }

        let worker_count = shared.workers.len();
        let mut suspended_workers = shared.suspended_workers.lock().unwrap();

        suspended_workers = shared
            .suspend_condition
            .wait_while(suspended_workers, |suspended| *suspended != worker_count)
            .unwrap();

        assert_eq!(*suspended_workers, worker_count);

        true
    }

    fn terminate(&mut self) {
        self.stop();
        self.shared.state.store(State::Terminated, Ordering::SeqCst);
        self.shared.wake_condition.notify_all();
    }
}

impl Drop for Scheduler {
    fn drop(&mut self) {
        self.terminate()
    }
}

impl Shared {
    fn spawn(self: &Arc<Shared>, future: impl Future<Output = ()>) {
        let task = Task::new(future, Arc::downgrade(self));
        self.schedule(task);
    }

    fn schedule(&self, task: Task) {
        LocalScheduler::try_with(|local| {
            if let Some(local) = local {
                local.queue.push(task);
            } else {
                self.global_queue.push(task);
            }
        })
    }
}

fn run_worker(shared: Arc<Shared>, queue: LocalQueue) {
    LocalScheduler::enter(shared, queue, |local| {
        while let Some(task) = local.next_task() {
            task.poll();
        }
    })
}

struct LocalScheduler {
    shared: Arc<Shared>,
    queue: LocalQueue,
}

thread_local! {
    static LOCAL: UnsafeCell<Option<LocalScheduler>> = UnsafeCell::new(None);
}

impl LocalScheduler {
    fn try_with<T>(f: impl FnOnce(Option<&LocalScheduler>) -> T) -> T {
        LOCAL.with(|cell| {
            let local = unsafe { (*cell.get()).as_ref() };
            f(local)
        })
    }

    fn enter<T>(shared: Arc<Shared>, queue: LocalQueue, f: impl FnOnce(&LocalScheduler) -> T) -> T {
        LOCAL.with(|cell| {
            let ptr = cell.get();

            let local = unsafe {
                assert!(
                    (*ptr).is_none(),
                    "a single thread cannot have two active schedulers"
                );
                ptr.write(Some(LocalScheduler { shared, queue }));
                (*ptr).as_ref().unwrap_unchecked()
            };

            let output = f(local);

            unsafe { ptr.write(None) };

            output
        })
    }

    fn next_task(&self) -> Option<Task> {
        let mut i = 0;

        loop {
            match self.shared.state.load(Relaxed) {
                State::Running => {}
                State::Suspended => {
                    self.suspend();
                    continue;
                }
                State::Terminated => return None,
            }

            if let Some(task) = self.try_next_task() {
                return Some(task);
            }

            std::hint::spin_loop();

            i += 1;
            if i >= 16 {
                i = 0;

                // TODO: wait until task becomes ready
                std::thread::yield_now();
            }
        }
    }

    fn try_next_task(&self) -> Option<Task> {
        if let Some(task) = self.queue.pop() {
            return Some(task);
        }

        loop {
            let steal = self.shared.global_queue.steal_batch_and_pop(&self.queue);

            if steal.is_retry() {
                continue;
            }

            if let Some(task) = steal.success() {
                return Some(task);
            }

            let workers = &self.shared.workers;

            // pick a random order to steal tasks from the other workers
            let start = fastrand::usize(0..workers.len());
            let (left, right) = workers.split_at(start);
            let order = right.iter().chain(left.iter());

            let mut retry = false;

            for worker in order {
                let steal = worker.stealer.steal_batch_and_pop(&self.queue);

                if steal.is_retry() {
                    retry = true;
                    continue;
                }

                if let Some(task) = steal.success() {
                    return Some(task);
                }
            }

            if retry {
                continue;
            } else {
                return None;
            }
        }
    }

    fn drain(&self) {
        while self.try_next_task().is_some() {}
    }

    fn suspend(&self) {
        self.drain();

        let shared = &self.shared;

        let mut suspended_workers = shared.suspended_workers.lock().unwrap();
        *suspended_workers += 1;
        shared.suspend_condition.notify_one();

        suspended_workers = shared
            .wake_condition
            .wait_while(suspended_workers, |_| {
                matches!(shared.state.load(Relaxed), State::Suspended)
            })
            .unwrap();

        *suspended_workers -= 1;
    }
}
