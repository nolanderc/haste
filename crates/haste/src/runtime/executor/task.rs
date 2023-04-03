use super::*;

/// A `Task` is essentially a type-erased version of `Pin<Arc<Mutex<dyn Future<Output = ()>>>>`.
pub struct Task {
    header: *mut Header,
}

impl std::fmt::Debug for Task {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Task({:p})", self.header)
    }
}

unsafe impl Send for Task {}
unsafe impl Sync for Task {}

impl Clone for Task {
    fn clone(&self) -> Self {
        self.header().increase_refcount();
        Self {
            header: self.header,
        }
    }
}

impl Drop for Task {
    fn drop(&mut self) {
        unsafe {
            let needs_drop = self.header().decrease_refcount();
            if !needs_drop {
                return;
            }

            // we have the last reference to the task, so we also need to free it.
            let header = &mut *self.header;

            // drop the inner future
            let ptr = header.future_ptr();
            if header.state.try_drop() {
                (header.vtable.drop)(ptr);
            }

            // drop the header, and free the task's memory
            let layout = header.size_align.layout();
            self.header.drop_in_place();
            std::alloc::dealloc(self.header.cast(), layout);
        }
    }
}

impl Task {
    /// Create a new task which represents the inner future.
    ///
    /// # Safety
    ///
    /// Calling this function erases the future's lifetime. The caller must ensure that the
    /// lifetime of the task does not outlive that of the future.
    pub(super) unsafe fn from_raw<F>(task: Box<RawTask<F>>) -> Self
    where
        F: Future<Output = ()> + Send,
    {
        let ptr = Box::into_raw(task);
        Self { header: ptr.cast() }
    }

    fn header(&self) -> &Header {
        unsafe { &*self.header }
    }

    pub fn poll(self) {
        let _guard = crate::enter_span(|| "poll task");

        let header = self.header();

        while header.state.try_begin_poll() {
            let waker = self.clone().into_waker();
            let mut cx = std::task::Context::from_waker(&waker);

            unsafe {
                let future = header.future_ptr();
                match (header.vtable.poll)(future, &mut cx) {
                    Poll::Ready(()) => {
                        (header.vtable.drop)(future);
                        header.state.end_poll_ready();
                        break;
                    }
                    Poll::Pending => {
                        if header.state.end_poll_pending() {
                            break;
                        }
                    }
                }
            }
        }
    }

    fn into_waker(self) -> Waker {
        unsafe { Waker::from_raw(self.into_raw_waker()) }
    }

    fn into_raw_waker(self) -> RawWaker {
        unsafe fn clone(ptr: *const ()) -> RawWaker {
            let header = ptr.cast::<Header>().cast_mut();
            let task = ManuallyDrop::new(Task { header });
            (*task).clone().into_raw_waker()
        }

        unsafe fn wake(ptr: *const ()) {
            let header = ptr.cast::<Header>().cast_mut();
            let task = Task { header };
            task.wake();
        }

        unsafe fn wake_by_ref(ptr: *const ()) {
            let header = ptr.cast::<Header>().cast_mut();
            let task = ManuallyDrop::new(Task { header });
            (*task).clone().wake();
        }

        unsafe fn drop(ptr: *const ()) {
            let header = ptr.cast::<Header>().cast_mut();
            std::mem::drop(Task { header });
        }

        static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);

        let this = ManuallyDrop::new(self);

        RawWaker::new(this.header.cast(), &VTABLE)
    }

    fn wake(self) {
        if self.header().state.try_wake() {
            self.schedule();
        }
    }

    fn schedule(self) {
        if let Some(executor) = self.header().executor.upgrade() {
            executor.schedule(self);
        }
    }
}

#[repr(C)]
#[pin_project::pin_project]
pub struct RawTask<T> {
    header: Header,
    #[pin]
    future: T,
}

impl<T> Future for RawTask<T>
where
    T: Future,
{
    type Output = T::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        this.future.poll(cx)
    }
}

impl<T> std::ops::Deref for RawTask<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.future
    }
}

impl<T> std::ops::DerefMut for RawTask<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.future
    }
}

impl<T> RawTask<T> {
    pub(super) fn new_with(executor: Weak<Shared>, create: impl FnOnce() -> T) -> Box<Self>
    where
        T: Future<Output = ()>,
    {
        unsafe {
            let layout = std::alloc::Layout::new::<Self>();

            let ptr = std::alloc::alloc(layout).cast::<Self>();
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            ptr.write(Self::new(executor, create()));

            Box::from_raw(ptr)
        }
    }

    pub(super) fn new(executor: Weak<Shared>, future: T) -> Self
    where
        T: Future<Output = ()>,
    {
        RawTask {
            header: Header {
                refcount: AtomicU32::new(1),
                state: TaskState::new(),
                size_align: SizeAlign::of::<Self>(),
                future_offset: Self::future_offset(),
                executor,
                vtable: VTable {
                    drop: VTable::drop::<T>,
                    poll: VTable::poll::<T>,
                },
            },
            future,
        }
    }

    fn future_offset() -> u32 {
        let uninit = MaybeUninit::<Self>::uninit();
        let ptr = uninit.as_ptr();
        let future_ptr = unsafe { std::ptr::addr_of!((*ptr).future) };
        unsafe { future_ptr.cast::<u8>().offset_from(ptr.cast::<u8>()) as u32 }
    }
}

#[repr(C)]
struct Header {
    refcount: AtomicU32,

    /// Controls the behaviour of polling and scheduling.
    state: TaskState,

    /// Size and alignment of the `RawTask`
    size_align: SizeAlign,

    /// Byte offset from the header to the start of the future's data.
    future_offset: u32,

    /// Reference to the executor so that we can schedule this task.
    executor: Weak<Shared>,

    /// Functions for dynamic dispatch.
    vtable: VTable,
}

impl Header {
    fn increase_refcount(&self) {
        let old_refcount = self.refcount.fetch_add(1, Relaxed);
        if old_refcount >= u32::MAX / 2 {
            std::process::abort();
        }
    }

    // Increases the refcount, returning `true` if the task needs to be dropped
    //
    // # Returns
    //
    // `true` if the task needs to be dropped.
    //
    // # Safety
    //
    // The caller ensures that they own one reference and will not use it after this point.
    unsafe fn decrease_refcount(&self) -> bool {
        // SAFETY: use relaese ordering so that all pending operations on the task are completed
        // before it is dropped.
        if self.refcount.fetch_sub(1, Release) != 1 {
            return false;
        }

        // SAFETY: this `Acquire` synchronizes with the above `Release` to ensure that all pending
        // operations are complete before we drop the task.
        self.refcount.load(Acquire);

        true
    }

    fn future_ptr(&self) -> *mut u8 {
        let ptr = (self as *const Self).cast_mut();
        unsafe { ptr.cast::<u8>().offset(self.future_offset as isize) }
    }
}

#[derive(Clone, Copy)]
struct SizeAlign(u32);

impl SizeAlign {
    pub const fn of<T: Sized>() -> Self {
        Self::new(std::mem::size_of::<T>(), std::mem::align_of::<T>())
    }

    pub const fn new(size: usize, align: usize) -> SizeAlign {
        assert!(size < (1 << 24), "future is way too large");
        assert!(align.is_power_of_two(), "alignment must be power of two");

        let align = align.trailing_zeros();

        let size = size as u32;

        SizeAlign((size << 8) | align)
    }

    fn size(self) -> usize {
        (self.0 >> 8) as usize
    }

    fn align(self) -> usize {
        1 << (self.0 & 0xff)
    }

    fn layout(self) -> std::alloc::Layout {
        std::alloc::Layout::from_size_align(self.size(), self.align()).unwrap()
    }
}

struct TaskState {
    bits: AtomicU32,
}

/// The task is waiting to be polled.
/// If this bit is cleared, a thread is currently polling the task.
const IDLE: u32 = 0x1;

/// The task is scheduled for execution.
const SCHEDULED: u32 = 0x2;

/// The task has finished executing.
const FINISHED: u32 = 0x4;

impl TaskState {
    fn new() -> Self {
        Self {
            bits: AtomicU32::new(IDLE | SCHEDULED),
        }
    }

    /// Attempt to start polling the task, return `true` if successful.
    fn try_begin_poll(&self) -> bool {
        // Clear the `IDLE` and `SCHEDULED` flags.
        let old = self.bits.fetch_and(!(IDLE | SCHEDULED), Acquire);

        if old & (IDLE | SCHEDULED) == SCHEDULED {
            // the task is currently running, but we just cleared its scheduled flag.
            // Thus, we try to reschedule it, if we succeed, we can poll it ourselves.
            return self.try_wake();
        }

        // The task must be idle to guarantee only one thread polls the task at once.
        // The task must also be scheduled, otherwise there's no point polling it.
        old & (IDLE | SCHEDULED | FINISHED) == (IDLE | SCHEDULED)
    }

    /// At the end of a poll: the task is still pending.
    ///
    /// Returns `false` if the task needs to be polled again.
    fn end_poll_pending(&self) -> bool {
        // mark the task as idle
        let now = self.bits.fetch_or(IDLE, Release);

        // if the task was scheduled while we polled it we must poll it again
        now & SCHEDULED == 0
    }

    /// At the end of a poll: the task has finished executing.
    fn end_poll_ready(&self) {
        self.bits.fetch_or(IDLE | FINISHED, Release);
    }

    /// Attempt to wake the task, returning `true` if it should be rescheduled.
    fn try_wake(&self) -> bool {
        let old = self.bits.fetch_or(SCHEDULED, Relaxed);

        // Only reschedule if the task is idle. Otherwise:
        // - if it is polling it will be rescheduled later
        // - if it is finished it does not need to be rescheduled
        // - if it is already scheduled we don't have to do it again
        old & (IDLE | SCHEDULED | FINISHED) == IDLE
    }

    /// Attempt to drop the task.
    fn try_drop(&mut self) -> bool {
        let bits = *self.bits.get_mut();
        bits & FINISHED == 0
    }
}

struct VTable {
    drop: unsafe fn(*mut u8),
    poll: unsafe fn(*mut u8, &mut std::task::Context) -> Poll<()>,
}

impl VTable {
    unsafe fn drop<T>(this: *mut u8) {
        this.cast::<T>().drop_in_place();
    }

    unsafe fn poll<T>(this: *mut u8, cx: &mut std::task::Context) -> Poll<()>
    where
        T: Future<Output = ()>,
    {
        let ptr = this.cast::<T>();
        let pinned = Pin::new_unchecked(&mut *ptr);
        pinned.poll(cx)
    }
}
