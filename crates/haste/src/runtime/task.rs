use std::{
    cell::UnsafeCell,
    future::Future,
    pin::Pin,
    sync::{
        atomic::{
            AtomicU32, AtomicUsize, Ordering,
            Ordering::{Acquire, Relaxed, Release},
        },
        Arc, Condvar, Mutex, MutexGuard, Weak,
    },
    task::Waker,
};

use crossbeam_deque::{Injector, Worker};

use crate::{util::CallOnDrop, IngredientPath};

pub struct Scheduler {
    injector: Injector<RawTask>,
    state: AtomicU32,
    workers: Mutex<WorkerState>,
    idle_condition: Condvar,
}

struct WorkerState {
    count: usize,
}

const RUNNING: u32 = 0x1;
const IN_SHUTDOWN: u32 = 0x2;

impl Scheduler {
    pub fn new() -> Self {
        Self {
            injector: Injector::new(),
            state: AtomicU32::new(RUNNING),
            workers: Mutex::new(WorkerState { count: 0 }),
            idle_condition: Condvar::new(),
        }
    }

    fn is(state: u32, expected: u32) -> bool {
        (state & expected) != 0
    }

    pub fn start(&self) -> bool {
        let workers = self.workers.lock().unwrap();

        match self.state.compare_exchange(0, RUNNING, Relaxed, Relaxed) {
            Ok(_) => {
                self.resume_workers(workers);
                true
            }
            Err(old) => Self::is(old, RUNNING),
        }
    }

    /// Stop the scheduler, cancelling all running tasks
    pub fn shutdown(&self) {
        let mut guard = self.workers.lock().unwrap();
        self.state.store(IN_SHUTDOWN, Relaxed);
        guard = self.wait_until_idle(guard);
        self.state.store(0, Relaxed);
        drop(guard)
    }

    /// Block the current thread until all workers have suspended
    fn wait_until_idle<'a>(
        &self,
        guard: MutexGuard<'a, WorkerState>,
    ) -> MutexGuard<'a, WorkerState> {
        self.idle_condition
            .wait_while(guard, |workers| workers.count > 0)
            .unwrap()
    }

    fn resume_workers(&self, _guard: MutexGuard<WorkerState>) {
        // TODO: wake any suspended workers
    }

    /// Suspends the current worker until the scheduler is resumed
    async fn suspend_worker(&self, worker: &Worker<RawTask>) {
        // drain the task queue
        while self.next_task(worker).is_some() {}

        self.remove_worker();

        // wait until the scheduler is running again
        while !Self::is(self.state.load(Relaxed), RUNNING) {
            // TODO: suspend the this future until it is woken by `resume_workers`
            futures_lite::future::yield_now().await;
        }

        self.add_worker();
    }

    fn add_worker(&self) {
        let mut workers = self.workers.lock().unwrap();
        workers.count += 1;
    }

    fn remove_worker(&self) {
        let mut workers = self.workers.lock().unwrap();
        workers.count -= 1;
        self.idle_condition.notify_one();
    }

    pub async fn run(&self) -> ! {
        let worker = crossbeam_deque::Worker::new_fifo();

        self.add_worker();

        let _guard = CallOnDrop(|| {
            // schedule all the local tasks on another queue
            while let Some(task) = worker.pop() {
                self.schedule(task);
            }
            self.remove_worker();
        });

        loop {
            for _ in 0..256 {
                while !Self::is(self.state.load(Relaxed), RUNNING) {
                    self.suspend_worker(&worker).await;
                }

                let Some(task) = self.next_task(&worker) else { break };
                task.poll();
            }

            futures_lite::future::yield_now().await;
        }
    }

    #[inline(never)]
    pub fn spawn(
        self: &Arc<Scheduler>,
        task: Box<dyn QueryTask + Send>,
    ) -> impl Future<Output = crate::Id> {
        let task = RawTask::new(task, Arc::downgrade(self));
        let shared = task.0.clone();
        self.schedule(task);

        std::future::poll_fn(move |cx| {
            let mut output = shared.output.lock().unwrap();
            match &mut *output {
                Output::Done(id) => return std::task::Poll::Ready(*id),

                Output::None => *output = Output::Waker(cx.waker().clone()),
                Output::Waker(old) => {
                    if !old.will_wake(cx.waker()) {
                        *old = cx.waker().clone();
                    }
                }
            }

            std::task::Poll::Pending
        })
    }

    fn schedule(&self, task: RawTask) {
        if Self::is(self.state.load(Ordering::Relaxed), RUNNING) {
            self.injector.push(task);
        }
    }

    fn next_task(&self, local: &Worker<RawTask>) -> Option<RawTask> {
        if let Some(task) = local.pop() {
            return Some(task);
        }

        loop {
            let steal = self.injector.steal_batch_and_pop(local);

            if steal.is_retry() {
                continue;
            }

            return steal.success();
        }
    }
}

pub trait QueryTask: Future<Output = crate::Id> {
    /// Get a unique identifier for the query.
    fn query(&self) -> IngredientPath;
}

#[repr(C)]
pub(super) struct RawTask(Arc<Shared>);

impl RawTask {
    pub fn new(task: Box<dyn QueryTask + Send>, scheduler: Weak<Scheduler>) -> Self {
        RawTask(Arc::new(Shared::new(task, scheduler)))
    }

    pub fn poll(self) {
        self.0.try_poll();
    }
}

struct Shared {
    state: State,
    scheduler: Weak<Scheduler>,
    data: UnsafeCell<Pin<Box<dyn QueryTask + Send>>>,
    output: Mutex<Output>,
}

enum Output {
    None,
    Done(crate::Id),
    Waker(Waker),
}

unsafe impl Send for Shared {}
unsafe impl Sync for Shared {}

impl Shared {
    pub fn new(task: Box<dyn QueryTask + Send>, scheduler: Weak<Scheduler>) -> Self {
        Self {
            state: State {
                raw: AtomicUsize::new(0),
            },
            scheduler,
            data: UnsafeCell::new(Pin::from(task)),
            output: Mutex::new(Output::None),
        }
    }

    fn should_reschedule(&self) -> bool {
        let old = self.state.raw.fetch_or(State::WOKEN, Ordering::Relaxed);
        if State::is(old, State::WOKEN | State::RUNNING | State::FINISHED) {
            // already woken/running -> they have the responsibility of rescheduling the task
            return false;
        }
        true
    }

    pub fn try_poll(self: Arc<Self>) -> Option<std::task::Poll<()>> {
        // try to mark the task as running before polling it
        let initial = self.state.raw.fetch_or(State::RUNNING, Ordering::Relaxed);
        if State::is(initial, State::RUNNING | State::FINISHED) {
            // another thread is already polling this task, or it has already finished
            return None;
        }

        // Clear the `WOKEN` bit, to allow wakers to reschedule this task
        let before = self.state.raw.swap(State::RUNNING, Acquire);

        let waker = std::task::Waker::from(self.clone());
        let mut context = std::task::Context::from_waker(&waker);

        // SAFETY: we are the only thread that managed to set the `RUNNING` bit, so no other thread
        // will alias the inner data.
        let poll = unsafe { (*self.data.get()).as_mut().poll(&mut context) };

        if let std::task::Poll::Ready(value) = poll {
            self.state.raw.fetch_or(State::FINISHED, Release);
            let previous =
                std::mem::replace(&mut *self.output.lock().unwrap(), Output::Done(value));
            if let Output::Waker(waker) = previous {
                waker.wake()
            }
            return Some(std::task::Poll::Ready(()));
        }

        // Clear the running bit, and check if the task has been woken while we were running
        let after = self.state.raw.fetch_and(!State::RUNNING, Release);
        if State::is(before | after, State::WOKEN) {
            // the task was woken while we were still running it, so we have responsibility to
            // reschedule it
            self.schedule();
        }

        Some(std::task::Poll::Pending)
    }

    fn schedule(self: Arc<Shared>) {
        if let Some(scheduler) = self.scheduler.upgrade() {
            scheduler.schedule(RawTask(self))
        }
    }
}

impl std::task::Wake for Shared {
    fn wake(self: Arc<Self>) {
        if self.should_reschedule() {
            self.schedule();
        }
    }

    fn wake_by_ref(self: &Arc<Self>) {
        if self.should_reschedule() {
            self.clone().schedule();
        }
    }
}

struct State {
    raw: AtomicUsize,
}

impl State {
    /// The task has been woken.
    const WOKEN: usize = 0x1;
    /// The task is currently running.
    const RUNNING: usize = 0x2;
    /// The task has finished executing.
    const FINISHED: usize = 0x4;

    fn is(raw: usize, expected: usize) -> bool {
        (raw & expected) != 0
    }
}
