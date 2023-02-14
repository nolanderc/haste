use std::{
    cell::UnsafeCell,
    future::Future,
    mem::MaybeUninit,
    sync::{
        atomic::{
            AtomicU32,
            Ordering::{Acquire, Relaxed, Release},
        },
        Mutex,
    },
    task::Waker,
};

use smallvec::SmallVec;

use crate::Query;

pub struct QuerySlot<Q: Query> {
    /// The input value associated with the query.
    pub input: Q::Input,

    /// The current state of the query.
    pub state: QueryState,

    /// The result from executing the query.
    pub output: UnsafeCell<MaybeUninit<OutputSlot<Q::Output>>>,
}

unsafe impl<Q: Query> Sync for QuerySlot<Q> {}

pub struct OutputSlot<T> {
    /// Refers to a list of dependencies collected while executing this query.
    pub dependencies: std::ops::Range<u32>,

    /// The output from a query.
    pub output: T,
}

// TODO: use a tagged pointer to combine `output` and `blocked`.
pub struct QueryState {
    /// - if `0x1` is set, the query has finished executing and the output has been written.
    /// - if `0x2` is set, a thread is currently writing to the output.
    output: AtomicU32,

    blocked: Mutex<Option<Box<BlockedState>>>,
}

const FINISHED: u32 = 0x1;
const WRITE_OUTPUT: u32 = 0x2;

pub(crate) struct BlockedState {
    /// List of wakers blocked on the output from the query.
    wakers: SmallVec<[Waker; 8]>,
}

impl<Q: Query> QuerySlot<Q> {
    pub fn new(input: Q::Input) -> Self {
        Self {
            input,
            state: QueryState::new(),
            output: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    unsafe fn output_assume_init(&self) -> &OutputSlot<Q::Output> {
        (*self.output.get()).assume_init_ref()
    }

    pub fn finish(&self, output: OutputSlot<Q::Output>) -> Option<&OutputSlot<Q::Output>> {
        let ptr = self.state.output.fetch_or(WRITE_OUTPUT, Relaxed);
        if (ptr & FINISHED) != 0 {
            self.state.output.load(Acquire);
            return unsafe { Some(self.output_assume_init()) };
        }
        if (ptr & WRITE_OUTPUT) != 0 {
            // Another thread is writing to the same slot
            return None;
        }

        // initialize the slot
        let value = unsafe { (*self.output.get()).write(output) };
        self.state.output.fetch_or(FINISHED, Release);

        let mut blocked = self.state.blocked.lock().unwrap();
        if let Some(blocked) = blocked.take() {
            for waker in blocked.wakers {
                waker.wake();
            }
        }

        Some(value)
    }

    /// Block on the query until it finishes
    pub fn try_wait(&self) -> Option<impl Future<Output = ()> + '_> {
        self.state.try_wait()
    }
}

impl QueryState {
    fn new() -> Self {
        Self {
            output: AtomicU32::new(0),
            blocked: Mutex::new(None),
        }
    }

    /// Returns a future which completes once the value has been written.
    fn try_wait(&self) -> Option<impl Future<Output = ()> + '_> {
        let mut registered = None;

        // fast path if the query is finished
        if (self.output.load(Acquire) & FINISHED) != 0 {
            return None;
        }

        Some(std::future::poll_fn(move |ctx| {
            if (self.output.load(Relaxed) & FINISHED) != 0 {
                self.output.load(Acquire);
                return std::task::Poll::Ready(());
            }

            // lock the state
            let mut state = self.blocked.lock().unwrap();

            // maybe the query finished while we were waiting for the lock
            if (self.output.load(Relaxed) & FINISHED) != 0 {
                self.output.load(Acquire);
                return std::task::Poll::Ready(());
            }

            let state = state.get_or_insert_with(|| Box::new(BlockedState::new()));
            let wakers = &mut state.wakers;

            // register our waker in the state
            let current_waker = ctx.waker();
            match registered {
                // we need to register our waker to be polled again
                None => {
                    registered = Some(wakers.len());
                    wakers.push(current_waker.clone());
                }
                // we already have a waker installed
                Some(index) => {
                    let old = &mut wakers[index];
                    if !old.will_wake(current_waker) {
                        // we were polled with a new waker, so replace the old
                        *old = current_waker.clone();
                    }
                }
            }

            std::task::Poll::Pending
        }))
    }
}

impl BlockedState {
    fn new() -> Self {
        Self {
            wakers: Default::default(),
        }
    }
}
