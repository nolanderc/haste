use std::{
    cell::UnsafeCell,
    future::Future,
    pin::Pin,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Weak,
    },
};

type Scheduler = ();

pub trait QueryTask: Future<Output = crate::Id> {
    /// Emit a human-readable description of the query.
    ///
    /// TODO: make this also machine-readable
    fn description(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
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
}

unsafe impl Send for Shared {}
unsafe impl Sync for Shared {}

impl std::task::Wake for Shared {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref()
    }

    fn wake_by_ref(self: &Arc<Self>) {
        let old = self.state.raw.fetch_or(State::WOKEN, Ordering::Relaxed);
        if State::is(old, State::WOKEN | State::RUNNING | State::FINISHED) {
            // already woken/running -> they have the responsibility of rescheduling the task
            return;
        }
        self.schedule();
    }
}

impl RawTask {}

impl Shared {
    pub fn new(task: Box<dyn QueryTask + Send>, scheduler: Weak<Scheduler>) -> Self {
        Self {
            state: State {
                raw: AtomicUsize::new(0),
            },
            scheduler,
            data: UnsafeCell::new(Pin::from(task)),
        }
    }

    pub fn try_poll(self: Arc<Self>) -> Option<std::task::Poll<crate::Id>> {
        // try to mark the task as running before polling it
        let old = self.state.raw.fetch_or(State::RUNNING, Ordering::Acquire);
        if State::is(old, State::RUNNING | State::FINISHED) {
            // another thread is already polling this task, or it has already finished
            return None;
        }

        // Clear the `WOKEN` bit, to allow wakers to reschedule this task
        self.state.raw.store(State::RUNNING, Ordering::Relaxed);

        let waker = std::task::Waker::from(self.clone());
        let mut context = std::task::Context::from_waker(&waker);

        // SAFETY: we are the only thread that managed to set the `RUNNING` bit
        let poll = unsafe { (&mut *self.data.get()).as_mut().poll(&mut context) };

        if let std::task::Poll::Ready(_) = poll {
            self.state.raw.fetch_or(State::FINISHED, Ordering::Release);
            return Some(poll);
        }

        // Clear the running bit, and check if the task has been woken while we were running
        let old = self.state.raw.fetch_and(!State::RUNNING, Ordering::Release);
        if State::is(old, State::WOKEN) {
            self.schedule();
        }

        Some(poll)
    }

    fn schedule(self: &Arc<Shared>) {
        if let Some(scheduler) = self.scheduler.upgrade() {
            todo!("schedule task")
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
