use std::{
    future::Future,
    num::NonZeroU32,
    pin::Pin,
    sync::{
        atomic::{
            AtomicPtr, AtomicU32,
            Ordering::{Acquire, Release},
        },
        Arc, Mutex,
    },
    task::Waker,
};

use smallvec::SmallVec;

pub struct Signal {
    /// Either `null` or an `Arc<SignalState>`.
    ///
    /// The `Arc` is only initialized by waiting tasks. This allows us to avoid an allocation if no
    /// one ever waits on the signal.
    state: AtomicPtr<SignalState>,
}

pub struct WaitSignal {
    /// Reference to the shared state.
    state: Arc<SignalState>,

    /// The index of this task's waker in the list of wakers.
    ///
    /// This is used to determine if we should insert a new waker into the list of wakers, or if we
    /// can simply re-use the old waker if polled twice.
    registered: Option<u32>,
}

struct SignalState {
    /// Either `0` or a `NonZeroU32`. If this is `0` the signal has not been triggered yet.
    value: AtomicU32,

    /// List of wakers to wake when the value has been set.
    ///
    /// We use a mutex here with the reasoning that it will be faster to temporarily take an
    /// uncontended lock than to allocate a linked list of nodes.
    wakers: Mutex<SmallVec<[Waker; 4]>>,
}

impl SignalState {
    const fn new() -> Self {
        Self {
            value: AtomicU32::new(0),
            wakers: Mutex::new(SmallVec::new_const()),
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

    /// Wait until the signal is triggered with a value.
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

    /// Send the final value to anyone waiting on this signal.
    pub fn finish(&mut self, value: NonZeroU32) {
        let ptr = std::mem::replace(self.state.get_mut(), std::ptr::null_mut());
        if ptr.is_null() {
            // no tasks are waiting on this result
            return;
        }

        // SAFETY: `self` always holds one of the references to the state, so the pointer is valid
        let state = unsafe { &*ptr };

        state.value.store(value.get(), Release);
        if let Ok(mut wakers) = state.wakers.lock() {
            for waker in std::mem::replace(&mut *wakers, SmallVec::new_const()) {
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
        self: Pin<&mut Self>,
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
                let Some(old) = wakers.get_mut(index as usize) else {
                    drop(wakers);
                    panic!("signal dropped without calling `finish`") 
                };

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

pub struct DropSignal {
    raw: Signal,
}

pub struct DropWaitSignal {
    raw: WaitSignal,
}

impl DropSignal {
    pub const fn new() -> Self {
        Self { raw: Signal::new() }
    }

    pub fn wait(&self) -> DropWaitSignal {
        DropWaitSignal {
            raw: self.raw.wait(),
        }
    }
}

impl Drop for DropSignal {
    fn drop(&mut self) {
        self.raw.finish(NonZeroU32::new(1).unwrap());
    }
}

impl Future for DropWaitSignal {
    type Output = ();

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        Pin::new(&mut self.get_mut().raw).poll(cx).map(drop)
    }
}
