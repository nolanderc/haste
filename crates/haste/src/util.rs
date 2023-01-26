use std::{
    future::Future,
    num::NonZeroU32,
    sync::{
        atomic::{
            AtomicPtr, AtomicU32,
            Ordering::{Acquire, Release},
        },
        Arc, Mutex,
    },
    task::Waker,
};

pub struct Signal {
    state: AtomicPtr<SignalState>,
}

pub struct WaitSignal {
    /// Reference to the shared state.
    state: Arc<SignalState>,
    /// The index of this task's waker in the list of wakers.
    registered: Option<u32>,
}

struct SignalState {
    value: AtomicU32,
    wakers: Mutex<Vec<Waker>>,
}

impl SignalState {
    const fn new() -> Self {
        Self {
            value: AtomicU32::new(0),
            wakers: Mutex::new(Vec::new()),
        }
    }

    fn load_value(&self) -> Option<NonZeroU32> {
        NonZeroU32::new(self.value.load(Acquire))
    }
}

impl Signal {
    pub const fn new() -> Self {
        Signal {
            state: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    pub fn wait(&self) -> WaitSignal {
        let mut ptr = self.state.load(Acquire);

        if ptr.is_null() {
            // initialize the state
            let new = Arc::into_raw(Arc::new(SignalState::new())).cast_mut();
            while ptr.is_null() {
                match self.state.compare_exchange_weak(ptr, new, Release, Acquire) {
                    Ok(_) => ptr = new,
                    Err(actual) => {
                        // drop the newly allocated state and use the actual one
                        // SAFETY: we are the only ones holding a reference to `new` so this will
                        // always deallocate
                        unsafe { Arc::from_raw(new.cast_const()) };
                        ptr = actual;
                    }
                }
            }
        }

        // SAFETY: we hold a reference to `self`, so there is at least one owner of the value
        unsafe { Arc::increment_strong_count(ptr) };

        // SAFETY: there are at least two references to `ptr`: one through `self` and one from the
        // `increment_strong_count`
        let state = unsafe { Arc::from_raw(ptr) };

        WaitSignal {
            state,
            registered: None,
        }
    }

    pub fn finish(mut self, value: NonZeroU32) {
        let ptr = *self.state.get_mut();
        if ptr.is_null() {
            // no tasks are waiting on this result
            return;
        }

        // SAFETY: `self` always holds one of the references to the state, so the pointer is valid
        let state = unsafe { &*ptr };

        state.value.store(value.get(), Release);
        if let Ok(mut wakers) = state.wakers.lock() {
            for waker in std::mem::take(&mut *wakers) {
                waker.wake();
            }
        }
    }
}

impl Drop for Signal {
    fn drop(&mut self) {
        let ptr = *self.state.get_mut();

        if ptr.is_null() {
            // nothing more to do
            return;
        }

        // SAFETY: `self` always holds one of the references to the state
        let state = unsafe { Arc::from_raw(ptr) };

        // drop all the wakers so that we don't leak the tasks
        if let Ok(mut wakers) = state.wakers.lock() {
            wakers.clear();
        }

        // discard our reference to the state
        drop(state);
    }
}

impl Future for WaitSignal {
    type Output = NonZeroU32;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        let this = self.get_mut();

        // fast path if the value has been set
        if let Some(value) = this.state.load_value() {
            return std::task::Poll::Ready(value);
        }

        // slow path: take the waker lock and register our waker
        let mut wakers = this.state.wakers.lock().unwrap();

        // it is possible that the value was set while we were waiting for the lock
        if let Some(value) = this.state.load_value() {
            return std::task::Poll::Ready(value);
        }

        let current_waker = cx.waker();
        match this.registered {
            // we need to register our waker to be polled again
            None => {
                this.registered = Some(wakers.len() as u32);
                wakers.push(current_waker.clone());
            }
            // we already have a waker installed
            Some(index) => {
                let old = &mut wakers[index as usize];
                if !old.will_wake(current_waker) {
                    // we were polled with a new waker, so replace the old
                    *old = current_waker.clone();
                }
            }
        }

        // the waker has been registered in the list, and
        std::task::Poll::Pending
    }
}
