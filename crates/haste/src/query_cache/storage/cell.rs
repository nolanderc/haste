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

use crate::{
    non_max::NonMaxU32,
    revision::{AtomicRevision, Revision},
    Change, Cycle, Durability, Runtime,
};

use super::TransitiveDependencies;

pub struct QueryCell<I, O> {
    /// The current state of the cell.
    state: State,

    /// A value which can only be written to once.
    input: SyncCell<I>,

    /// A value which can only be written to once.
    output: SyncCell<O>,
}

struct SyncCell<T>(UnsafeCell<MaybeUninit<T>>);

unsafe impl<T: Send> Send for SyncCell<T> {}
unsafe impl<T: Sync> Sync for SyncCell<T> {}

impl<T> SyncCell<T> {
    fn get_mut(&mut self) -> &mut MaybeUninit<T> {
        self.0.get_mut()
    }

    unsafe fn drop_in_place(&self) {
        (*self.0.get()).assume_init_drop()
    }

    unsafe fn assume_init(&self) -> &T {
        (*self.0.get()).assume_init_ref()
    }

    #[allow(clippy::mut_from_ref)]
    unsafe fn assume_init_mut(&self) -> &mut T {
        (*self.0.get()).assume_init_mut()
    }

    unsafe fn write(&self, value: T) -> &T {
        (*self.0.get()).write(value)
    }
}

impl<I, T> Unpin for QueryCell<I, T> {}

unsafe impl<I, T> Zeroable for QueryCell<I, T> {}

#[derive(bytemuck::Zeroable)]
struct State {
    /// A tagged pointer equivalent to `Option<Box<BlockedState>>`.
    /// Contains a list of all tasks which are blocked on this value.
    ///
    /// Additionally, the lowest 5 bits of the address represent the following:
    ///
    /// - if `0x1` is set, an input value has been written.
    /// - if `0x2` is set, an output value has been written.
    /// - if `0x4` is set, a thread has locked this cell, gaining exclusive access to the list of
    /// blocked tasks and the inner value.
    /// - if `0x8` is set, a thread is waiting on the lock (ie. it is contended).
    /// - if `0x10` is set, there is a dependency cycle which is stored in the inner state.
    /// - if `0x20` is set, the task is being executed
    addr: AtomicUsize,

    /// The revision during which the query slot was last verified to be valid and up-to-date.
    verified_at: AtomicRevision,

    /// The revision during which the output was last changed.
    changed_at: AtomicRevision,
}

struct StateLock<'a> {
    state: &'a State,
    addr: usize,
}

/// The input value has been written.
const HAS_INPUT: usize = 0x1;

/// The output value in the cell has been written.
const HAS_OUTPUT: usize = 0x2;

/// The cell structure is locked.
const LOCKED: usize = 0x4;

/// The cell lock is contended. Upon releasing the lock, another thread should be signaled.
const CONTENDED: usize = 0x8;

/// While executing the query, a cycle was encountered (stored in `BlockedState`).
const CYCLIC: usize = 0x10;

/// A task has claimed the query for execution.
const CLAIMED: usize = 0x20;

/// Mask of the bits of the tagged pointer which correspond to the address of the pointer
const ADDR_MASK: usize = usize::MAX << 6;

/// We specify an alignment of 64 (` == 1 << 6`). This guarantees that the lowest 6 bits of any
/// pointer to this structure will be zeroes, allowing us to use it to encode a tagged pointer.
#[repr(align(64))]
#[derive(Default)]
pub(crate) struct BlockedState {
    /// List of wakers blocked on the cell.
    wakers: SmallVec<[Waker; WAKER_INLINE_CAP]>,
    /// If there has been a dependency cycle it is stored here.
    cycle: Option<Cycle>,
}

const WAKER_INLINE_CAP: usize = {
    const ALIGN: usize = 64;
    const WAKER: usize = std::mem::size_of::<Waker>();
    const CYCLE: usize = std::mem::size_of::<Cycle>();
    const USIZE: usize = std::mem::size_of::<usize>();
    let mut count = (ALIGN - (USIZE + CYCLE)) / WAKER;
    while count < 4 {
        count += ALIGN / WAKER;
    }
    count
};

impl<I, T> Default for QueryCell<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

pub type ChangeFuture<'a> = impl Future<Output = Change> + Send + Unpin + 'a;

impl<I, O> QueryCell<I, O> {
    pub fn new() -> Self {
        Self::zeroed()
    }

    /// Initialize the cell with some input value.
    pub fn write_input(&self, value: I) -> &I {
        // take the lock, ensuring that we are the only thread writing to the value
        let lock = self.state.lock();

        if (lock.addr & HAS_INPUT) != 0 {
            // the value has already been initialized
            // SAFETY: since we grabbed the lock, there's no need further need to synchronize
            // with the writer
            return unsafe { self.input.assume_init() };
        }

        // initialize the slot
        // SAFETY: the `HAS_INPUT` bit was not set, so we are the first (and only) to write
        let value = unsafe { self.input.write(value) };

        // set the `HAS_INPUT` bit, allowing other threads to read the value
        lock.set_initialized();

        value
    }

    /// # Safety
    ///
    /// The caller must ensure that the input value has been written.
    pub unsafe fn input_assume_init(&self) -> &I {
        self.input.assume_init()
    }

    pub fn get_input(&self) -> Option<&I> {
        if self.has_input() {
            unsafe { Some(self.input_assume_init()) }
        } else {
            None
        }
    }

    pub fn has_input(&self) -> bool {
        (self.state.addr.load(Acquire) & HAS_INPUT) != 0
    }

    pub fn set_output<F>(&mut self, runtime: &mut Runtime, durability: Durability, make_output: F)
    where
        F: FnOnce(Revision) -> O,
    {
        let state = self.state.addr.get_mut();
        let output = self.output.get_mut();

        let last_change = self.state.changed_at.get();
        let current = runtime.update_input(last_change, durability);

        let value = make_output(current);

        if (*state & HAS_OUTPUT) != 0 {
            unsafe { output.assume_init_drop() }
        }
        output.write(value);

        *state |= HAS_OUTPUT;

        self.state.verified_at.set(Some(current));
        self.state.changed_at.set(Some(current));
    }

    pub fn remove_output(&mut self, runtime: &mut Runtime, durability: Durability) {
        let state = self.state.addr.get_mut();
        let output = self.output.get_mut();

        let Some(last_change) = self.state.changed_at.get() else { return };
        if (*state & HAS_OUTPUT) == 0 {
            return;
        }

        let current = runtime.update_input(Some(last_change), durability);

        unsafe { output.assume_init_drop() }
        *state &= !HAS_OUTPUT;

        self.state.changed_at.set(Some(current));

        self.state.verified_at.set(None);
        self.state.changed_at.set(None);
    }

    /// # Safety
    ///
    /// The caller must have a claim on the query.
    pub unsafe fn write_output(&self, value: O, revision: Revision) -> &O {
        // take the lock, ensuring that we are the only thread writing to the value
        let lock = self.state.lock();

        if (lock.addr & HAS_OUTPUT) != 0 {
            // there's an old value:
            self.output.drop_in_place();
        }

        // initialize the slot
        let value = self.output.write(value);

        // we changed the slot's value in the current revision:
        self.state.changed_at.store(Some(revision), Relaxed);

        // set the `HAS_OUTPUT` bit, allowing tasks to read the value
        let blocked = lock.set_finished(revision);

        // wake any tasks waiting on this result
        if let Some(blocked) = blocked {
            for waker in blocked.wakers {
                waker.wake();
            }
        }

        value
    }

    /// Assuming there is an existing output in the cell, marks it as valid in the given revision,
    /// waking any blocking tasks.
    ///
    /// # Safety
    ///
    /// The caller must have a claim on the query.
    pub(crate) unsafe fn backdate(&self, revision: Revision) {
        let lock = self.state.lock();

        assert!((lock.addr & HAS_OUTPUT) != 0);

        // mark the slot as valid in the current revision
        if let Some(blocked) = lock.set_finished(revision) {
            for waker in blocked.wakers {
                waker.wake();
            }
        }
    }

    /// # Safety
    ///
    /// The caller must ensure that the output value has been written.
    pub unsafe fn output_assume_init(&self) -> &O {
        self.output.assume_init()
    }

    /// # Safety
    ///
    /// The output must be claimed by the caller.
    pub unsafe fn get_output_claimed(&self) -> Option<&mut O> {
        if (self.state.addr.load(Acquire) & HAS_OUTPUT) != 0 {
            unsafe { Some(self.output.assume_init_mut()) }
        } else {
            None
        }
    }

    pub fn get_output_mut(&mut self) -> Option<&mut O> {
        if (*self.state.addr.get_mut() & HAS_OUTPUT) != 0 {
            unsafe { Some(self.output.get_mut().assume_init_mut()) }
        } else {
            None
        }
    }

    /// # Safety
    ///
    /// Only the current revision of the database must be given.
    pub unsafe fn try_get_output(&self, current: Revision) -> Option<&O> {
        if self.state.verified_at.load(Acquire) == Some(current) {
            Some(self.output_assume_init())
        } else {
            None
        }
    }

    /// Reserve the query for execution in the given revision. If the query is already ready,
    /// returns the previous value.
    ///
    /// # Safety
    ///
    /// Only the current revision of the database must be given.
    pub unsafe fn claim(&self, revision: Revision) -> Result<(), Option<&O>> {
        if self.state.verified_at.load(Acquire) == Some(revision) {
            // the query is already up-to-date
            return Err(Some(self.output_assume_init()));
        }

        let lock = self.state.lock();

        // the query was completed while we waited on the lock
        if self.state.verified_at.load(Relaxed) == Some(revision) {
            // SAFETY: the data in the ouput is already synchronized with the writer due to us
            // holding the lock so we can use `Relaxed` ordering above.
            return Err(Some(self.output_assume_init()));
        }

        if (lock.addr & CLAIMED) != 0 {
            // another thread has already claimed the query
            return Err(None);
        }

        lock.unlock_and_set(CLAIMED);

        Ok(())
    }

    /// Release the claim on the query.
    ///
    /// # Safety
    ///
    /// The caller must have a claim on the query.
    pub unsafe fn release_claim(&self) {
        let lock = self.state.lock();
        debug_assert!((lock.addr & CLAIMED) != 0);
        lock.unlock_set_and_clear(0, CLAIMED);
    }

    /// Waits until the output value has been set
    pub fn wait_until_verified(&self, revision: Revision) -> impl Future<Output = &O> + Unpin + '_ {
        let mut wait = State::wait_any(self, revision);
        std::future::poll_fn(move |cx| {
            std::task::ready!(wait.poll(cx));
            std::task::Poll::Ready(unsafe { wait.state.output_assume_init() })
        })
    }

    /// Waits until the output value has been set
    pub unsafe fn wait_for_change(
        &self,
        revision: Revision,
        get_deps: impl FnOnce(
            *const UnsafeCell<MaybeUninit<O>>,
        ) -> *const UnsafeCell<MaybeUninit<TransitiveDependencies>>,
    ) -> ChangeFuture {
        let deps_ptr = get_deps(&self.output.0);
        self.state.wait_for_change(revision, deps_ptr)
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

    pub fn last_verified(&self) -> Option<Revision> {
        self.state.verified_at.load(Acquire)
    }

    pub fn last_changed(&self) -> Option<Revision> {
        self.state.changed_at.load(Relaxed)
    }

    pub fn set_verified(&mut self, current: Revision) {
        self.state.verified_at.set(Some(current))
    }
}

struct Wait<S> {
    state: S,
    revision: Revision,
    registered: Option<NonMaxU32>,
}

impl<S> Future for Wait<S>
where
    S: AsQueryState + Unpin,
{
    type Output = ();

    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        let mut this = &mut *self;
        let state = this.state.as_state();
        let revision = this.revision;

        if state.verified_at.load(Acquire) == Some(revision) {
            // SAFETY: we used `Acquire` ordering, so we synchronized with the write
            return std::task::Poll::Ready(());
        }

        // lock the state
        let mut lock = state.lock();

        // Maybe the value was written while we were waiting for the lock?
        if state.verified_at.load(Relaxed) == Some(revision) {
            // SAFETY: since we grabbed the lock, we are synchronized with the write
            return std::task::Poll::Ready(());
        }

        let blocked = lock.get_or_init();
        let wakers = &mut blocked.wakers;

        // register our waker in the state
        let current_waker = cx.waker();
        match this.registered {
            // we need to register our waker to be polled again
            None => {
                this.registered = NonMaxU32::new(wakers.len() as u32);
                wakers.push(current_waker.clone());
            }
            // we already have a waker installed
            Some(index) => {
                let old = &mut wakers[index.get() as usize];
                if !old.will_wake(current_waker) {
                    // we were polled with a new waker, so replace the old
                    *old = current_waker.clone();
                }
            }
        }

        std::task::Poll::Pending
    }
}

trait AsQueryState {
    fn as_state(&self) -> &State;
}

impl<T> AsQueryState for &T
where
    T: AsQueryState,
{
    fn as_state(&self) -> &State {
        T::as_state(self)
    }
}

impl<I, O> AsQueryState for QueryCell<I, O> {
    fn as_state(&self) -> &State {
        &self.state
    }
}

impl AsQueryState for State {
    fn as_state(&self) -> &State {
        self
    }
}

impl State {
    fn wait_any<S>(state: S, revision: Revision) -> Wait<S>
    where
        Wait<S>: Future,
    {
        Wait {
            state,
            revision,
            registered: None,
        }
    }

    /// Returns a future which completes once the value has been written.
    fn wait(&self, revision: Revision) -> Wait<&Self> {
        Self::wait_any(self, revision)
    }

    fn wait_for_change(
        &self,
        revision: Revision,
        transitive: *const UnsafeCell<MaybeUninit<TransitiveDependencies>>,
    ) -> ChangeFuture {
        let future = self.wait(revision);
        let transitive = crate::util::SendWrapper(transitive);

        crate::util::future::map(future, move |()| {
            let transitive = unsafe { (*UnsafeCell::raw_get(*transitive)).assume_init_read() };
            let changed_at = self.changed_at.load(Relaxed);

            Change {
                changed_at,
                transitive,
            }
        })
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
        // - set the `HAS_INPUT` bit
        // - release the lock (ie. clear the `LOCKED` and `CONTENDED` bits)
        self.unlock_and_set(HAS_INPUT);
    }

    /// Set the `HAS_OUTPUT`-bit, mark the value as valid in the given revision, and take ownership
    /// of the inner pointer by clearing it to `null`.
    fn set_finished(self, revision: Revision) -> Option<Box<BlockedState>> {
        // SAFETY: we only set `verified_at` while holding the lock.
        self.state.verified_at.store(Some(revision), Release);

        // - set the `HAS_OUTPUT` bit
        // - clear the address to `null`
        // - clear the `CYCLIC` bit
        // - clear the `CLAIMED` bit
        // - release the lock (ie. clear the `LOCKED` and `CONTENDED` bits)
        let old = self.unlock_set_and_clear(HAS_OUTPUT, CLAIMED | CYCLIC | ADDR_MASK);

        let ptr = (old & ADDR_MASK) as *mut BlockedState;
        if ptr.is_null() {
            return None;
        }

        unsafe { Some(Box::from_raw(ptr)) }
    }

    /// Releases the lock and `set`s the given bits.
    /// Returns the previous state.
    #[inline]
    fn unlock_and_set(self, set: usize) -> usize {
        self.unlock_set_and_clear(set, 0)
    }

    /// Releases the lock and `set`s the given bits, while `clear`ing the others.
    /// Returns the previous state.
    #[inline]
    fn unlock_set_and_clear(self, set: usize, clear: usize) -> usize {
        let state = self.state;
        let old_addr = self.addr;
        let new_addr = set | (old_addr & !clear);

        debug_assert_eq!(new_addr & (LOCKED | CONTENDED), 0);

        // SAFETY: we are going to release the lock below, but if we drop here we are going to
        // unlock twice, which could cause race conditions.
        std::mem::forget(self);

        let old = state.addr.swap(new_addr, Release);

        if (old & CONTENDED) != 0 {
            // there was a thread waiting on the lock
            state.wake_lock();
        }

        old
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

        if addr & HAS_INPUT != 0 {
            unsafe { self.input.get_mut().assume_init_drop() }
        }
        if addr & HAS_OUTPUT != 0 {
            unsafe { self.output.get_mut().assume_init_drop() }
        }

        let ptr = (addr & ADDR_MASK) as *mut BlockedState;
        if !ptr.is_null() {
            unsafe { drop(Box::from_raw(ptr)) }
        }
    }
}
