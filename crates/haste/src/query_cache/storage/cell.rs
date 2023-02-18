use std::{
    cell::UnsafeCell,
    future::Future,
    mem::MaybeUninit,
    sync::atomic::{
        AtomicUsize,
        Ordering::{Acquire, Relaxed, Release},
    },
    task::Waker,
};

use bytemuck::Zeroable;
use futures_lite::FutureExt;
use smallvec::SmallVec;

use crate::Cycle;

pub struct QueryCell<I, O> {
    /// The current state of the cell.
    state: State,

    /// A value which can only be written to once.
    input: UnsafeCell<MaybeUninit<I>>,

    /// A value which can only be written to once.
    output: UnsafeCell<MaybeUninit<O>>,
}

unsafe impl<I: Send, O: Send> Send for QueryCell<I, O> {}
unsafe impl<I: Send + Sync, O: Send + Sync> Sync for QueryCell<I, O> {}

impl<I, T> Unpin for QueryCell<I, T> {}

unsafe impl<I, T> Zeroable for QueryCell<I, T> {}

struct State {
    /// A tagged pointer equivalent to `Option<Box<BlockedState>>`.
    /// Contains a list of all tasks which are blocked on this value.
    ///
    /// Additionally, the lowest 3 bits of the address represent the following:
    ///
    /// - if `0x1` is set, the input value has been initialized.
    /// - if `0x2` is set, the output value has been written.
    /// - if `0x4` is set, a thread has locked this cell, gaining exclusive access to the list of
    /// blocked tasks and the inner value.
    /// - if `0x8` is set, a thread is waiting on the lock (ie. it is contended).
    /// - if `0x10` is set, there is a dependency cycle which is stored in the inner state.
    addr: AtomicUsize,
}

struct StateLock<'a> {
    state: &'a State,
    addr: usize,
}

/// The input value has been initialized.
const INITIALIZED: usize = 0x1;

/// The output value in the cell has been written.
const FINISHED: usize = 0x2;

/// The cell structure is locked.
const LOCKED: usize = 0x4;

/// The cell lock is contended. Upon releasing the lock, another thread should be signaled.
const CONTENDED: usize = 0x8;

/// The cell lock is contended. Upon releasing the lock, another thread should be signaled.
const CYCLIC: usize = 0x10;

/// Mask of the bits of the tagged pointer which correspond to the address of the pointer
const ADDR_MASK: usize = usize::MAX << 5;

/// We specify an alignment of 32. This guarantees that the lowest 5 bits of any pointer to this
/// structure will be zeroes, allowing us to use it to encode a tagged pointer.
#[repr(align(32))]
#[derive(Default)]
pub(crate) struct BlockedState {
    /// List of wakers blocked on the cell.
    wakers: SmallVec<[Waker; 8]>,
    /// If there has been a dependency cycle it is stored here.
    cycle: Option<Cycle>,
}

impl<I, T> Default for QueryCell<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I, O> QueryCell<I, O> {
    pub fn new() -> Self {
        Self::zeroed()
    }

    /// Iialize the cell with some value.
    pub fn write_input(&self, value: I) -> Result<&I, &I> {
        // take the lock, ensuring that we are the only thread writing to the value
        let lock = self.state.lock();

        if (lock.addr & INITIALIZED) != 0 {
            // the value has already been initialized
            // SAFETY: since we grabbed the lock, there's no need further need to synchronize
            // with the writer
            return unsafe { Err(self.input_assume_init()) };
        }

        // initialize the slot
        // SAFETY: the `INITIALIZED` bit was not set, so we are the first (and only) to write
        let value = unsafe { (*self.input.get()).write(value) };

        // set the `INITIALIZED` bit, allowing other threads to read the value
        lock.set_initialized();

        Ok(value)
    }

    /// # Safety
    ///
    /// The caller must ensure that the input value has been written.
    pub unsafe fn input_assume_init(&self) -> &I {
        (*self.input.get()).assume_init_ref()
    }

    pub fn get_input(&self) -> Option<&I> {
        if self.has_input() {
            unsafe { Some(self.input_assume_init()) }
        } else {
            None
        }
    }

    pub fn has_input(&self) -> bool {
        (self.state.addr.load(Acquire) & INITIALIZED) != 0
    }

    pub fn write_output(&self, value: O) -> &O {
        // take the lock, ensuring that we are the only thread writing to the value
        let lock = self.state.lock();

        if (lock.addr & FINISHED) != 0 {
            // the value has already been written
            // SAFETY: since we grabbed the lock, there's no need further need to synchronize
            // with the writer
            return unsafe { self.output_assume_init() };
        }

        // initialize the slot
        // SAFETY: the `FINISHED` bit was not set, so we are the first (and only) to write
        let value = unsafe { (*self.output.get()).write(value) };

        // set the `FINISHED` bit, allowing tasks to read the value
        let blocked = lock.set_finished();

        // wake any tasks waiting on this result
        if let Some(blocked) = blocked {
            for waker in blocked.wakers {
                waker.wake();
            }
        }

        value
    }

    /// # Safety
    ///
    /// The caller must ensure that the output value has been written.
    pub unsafe fn output_assume_init(&self) -> &O {
        (*self.output.get()).assume_init_ref()
    }

    pub fn get_output(&self) -> Option<&O> {
        if self.has_output() {
            unsafe { Some(self.output_assume_init()) }
        } else {
            None
        }
    }

    pub fn has_output(&self) -> bool {
        (self.state.addr.load(Acquire) & FINISHED) != 0
    }

    /// Either returns `Ok(())` meaning the output value is ready, or `Err(F)`, where `F` is a
    /// future which resolves when the output has been written.
    pub fn wait_until_finished(&self) -> Result<&O, impl Future<Output = &O> + '_> {
        match self.state.wait() {
            Ok(()) => Ok(unsafe { self.output_assume_init() }),
            Err(mut fut) => {
                // we cannot use an `async` block here, since they don't implement `Unpin`
                Err(std::future::poll_fn(move |cx| {
                    fut.poll(cx).map(|()| unsafe { self.output_assume_init() })
                }))
            }
        }
    }

    pub fn set_cycle(&self, cycle: Cycle) -> Result<(), Cycle> {
        let mut lock = self.state.lock();
        if (lock.addr & CYCLIC) != 0 {
            // encountered a new cycle while recovering from previous cycle
            return Err(cycle);
        }

        lock.get_or_init().cycle = Some(cycle);
        lock.unlock_and_set(CYCLIC);

        Ok(())
    }

    pub fn take_cycle(&self) -> Option<Cycle> {
        if (self.state.addr.load(Relaxed) & CYCLIC) == 0 {
            return None;
        }

        let mut lock = self.state.lock();
        lock.get_or_init().cycle.take()
    }
}

impl State {
    /// Returns a future which completes once the value has been written.
    fn wait(&self) -> Result<(), impl Future<Output = ()> + Unpin + '_> {
        // fast path if the value is already written
        if (self.addr.load(Acquire) & FINISHED) != 0 {
            return Ok(());
        }

        // If we have registered the current task, this is the index in the list of wakers this
        // task's waker occupies.
        let mut registered = None;

        Err(std::future::poll_fn(move |ctx| {
            if (self.addr.load(Relaxed) & FINISHED) != 0 {
                // SAFETY: we need to synchronize with the write of the value
                self.addr.load(Acquire);
                return std::task::Poll::Ready(());
            }

            // lock the state
            let mut lock = self.lock();

            // Maybe the value was written while we were waiting for the lock?
            if (lock.addr & FINISHED) != 0 {
                // SAFETY: by taking the lock we have already synchronized with the write
                return std::task::Poll::Ready(());
            }

            let blocked = lock.get_or_init();
            let wakers = &mut blocked.wakers;

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

    fn lock(&self) -> StateLock<'_> {
        let old = self.addr.fetch_or(LOCKED, Acquire);

        let state = if (old & LOCKED) == 0 {
            // we managed to set the `LOCKED` bit
            old
        } else {
            // the `LOCKED` bit was already set
            self.lock_contended()
        };

        StateLock {
            state: self,
            addr: state,
        }
    }

    fn lock_contended(&self) -> usize {
        let mut state = self.spin();

        if (state & LOCKED) == 0 {
            // the lock is free, so attempt to take it without marking it as contended
            state = self.addr.fetch_or(LOCKED, Acquire);
            if (state & LOCKED) == 0 {
                // we changed it to LOCKED
                return state;
            }
        }

        loop {
            // we could not take the lock, so mark it as contended (if it already is marked, we
            // can skip avoid a write)
            if (state & CONTENDED) == 0 {
                state = self.addr.fetch_or(CONTENDED | LOCKED, Acquire);
                if (state & LOCKED) == 0 {
                    // we changed it to LOCKED
                    return state;
                }
            }

            self.wait_on_lock();

            state = self.spin();
        }
    }

    fn spin(&self) -> usize {
        let mut spin = 100;
        loop {
            let state = self.addr.load(Relaxed);

            let is_unlocked = (state & LOCKED) == 0;
            let is_contended = (state & CONTENDED) != 0;

            if is_unlocked || is_contended || spin == 0 {
                break state;
            }

            std::hint::spin_loop();
            spin -= 1;
        }
    }

    unsafe fn unlock(&self) {
        // clear the locked and contended bits to allow other threads to take the lock
        let old = self.addr.fetch_and(!(LOCKED | CONTENDED), Release);

        if (old & CONTENDED) != 0 {
            self.wake_lock();
        }
    }

    /// block the current thread until the lock becomes free
    fn wait_on_lock(&self) {
        let key = self as *const Self as usize;
        let validate = || {
            let state = self.addr.load(Relaxed);
            let is_locked = (state & LOCKED) != 0;
            let is_contended = (state & CONTENDED) != 0;
            is_locked && is_contended
        };
        let before_sleep = || {};
        let timed_out = |_, _| {};
        let park_token = parking_lot_core::DEFAULT_PARK_TOKEN;
        let timeout = None;
        unsafe {
            parking_lot_core::park(key, validate, before_sleep, timed_out, park_token, timeout);
        }
    }

    fn wake_lock(&self) {
        let key = self as *const Self as usize;
        unsafe {
            parking_lot_core::unpark_one(key, |_| parking_lot_core::DEFAULT_UNPARK_TOKEN);
        }
    }
}

impl StateLock<'_> {
    fn get_or_init(&mut self) -> &mut BlockedState {
        let mut addr = self.addr & ADDR_MASK;

        if addr == 0 {
            let ptr: *mut BlockedState = Box::into_raw(Box::default());
            addr = ptr as usize;
            self.addr = addr | self.state.addr.fetch_or(addr, Relaxed);
        }

        // SAFETY: we have `&mut self`, so there is no other locks with access to the inner value
        unsafe { &mut *(addr as *mut BlockedState) }
    }

    fn set_initialized(self) {
        // - set the `INITIALIZED` bit
        // - release the lock (ie. clear the `LOCKED` and `CONTENDED` bits)
        // - keep the old value of `FINISHED`
        // - keep the old value of the address
        self.unlock_set_and_keep(INITIALIZED, FINISHED | CYCLIC | ADDR_MASK);
    }

    /// Set the `FINISHED`-bit and take ownership of the inner pointer by clearing it to `null`.
    fn set_finished(self) -> Option<Box<BlockedState>> {
        // - set the `FINISHED` bit
        // - clear the address to `null`
        // - clear the `CYCLIC` bit
        // - release the lock (ie. clear the `LOCKED` and `CONTENDED` bits)
        // - keep the old value of `INITIALIZED`
        let old = self.unlock_set_and_keep(FINISHED, INITIALIZED);

        let ptr = (old & ADDR_MASK) as *mut BlockedState;
        if ptr.is_null() {
            return None;
        }

        unsafe { Some(Box::from_raw(ptr)) }
    }

    /// Releases the lock and `set`s the given bits, while `keep`ing the others.
    /// Returns the previous state.
    #[inline]
    fn unlock_set_and_keep(self, set: usize, keep: usize) -> usize {
        debug_assert!(((set | keep) & (LOCKED | CONTENDED)) == 0);

        let state = self.state;
        let old_addr = self.addr;

        // SAFETY: we are going to release the lock below, but if we drop here we are going to
        // unlock twice, which could cause race conditions.
        std::mem::forget(self);
        let old = state.addr.swap(set | (keep & old_addr), Release);

        if (old & CONTENDED) != 0 {
            // there was a thread waiting on the lock
            state.wake_lock();
        }

        old
    }

    /// Releases the lock and `set`s the given bits, while `keep`ing the others.
    /// Returns the previous state.
    #[inline]
    fn unlock_and_set(self, set: usize) -> usize {
        self.unlock_set_and_keep(set, !(LOCKED | CONTENDED))
    }
}

impl Drop for StateLock<'_> {
    fn drop(&mut self) {
        unsafe { self.state.unlock() }
    }
}

impl<I, T> Drop for QueryCell<I, T> {
    fn drop(&mut self) {
        let addr = *self.state.addr.get_mut();

        if addr & FINISHED != 0 {
            unsafe { self.output.get_mut().assume_init_drop() }
        }

        let ptr = (addr & ADDR_MASK) as *mut BlockedState;
        if !ptr.is_null() {
            unsafe { drop(Box::from_raw(ptr)) }
        }
    }
}
