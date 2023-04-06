use std::{
    future::Future,
    pin::Pin,
    sync::atomic::{
        AtomicPtr,
        Ordering::{Acquire, Relaxed, Release},
    },
};

pub struct BumpArena {
    start: *mut u8,
    end: AtomicPtr<u8>,
    size: usize,
}

unsafe impl Send for BumpArena {}
unsafe impl Sync for BumpArena {}

impl BumpArena {
    const ALIGN: usize = 16;

    pub fn new(size: usize) -> Self {
        unsafe {
            let layout = std::alloc::Layout::from_size_align(size, Self::ALIGN).unwrap();
            let start = std::alloc::alloc(layout);

            if start.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let end = start.add(size);

            Self {
                start,
                end: AtomicPtr::new(end),
                size,
            }
        }
    }

    pub fn alloc<T>(&self, value: T) -> BumpBox<'_, T> {
        let layout = std::alloc::Layout::new::<T>();

        let mut new_end;
        loop {
            let end = self.end.load(Relaxed);

            let end_addr = end as usize;
            let start_addr = self.start as usize;

            let unaligned_end = end_addr.saturating_sub(layout.size());
            let new_end_addr = unaligned_end & !(layout.align() - 1);

            if new_end_addr < start_addr {
                panic!("out of memory")
            }

            new_end = new_end_addr as *mut u8;
            if self
                .end
                .compare_exchange(end, new_end, Acquire, Relaxed)
                .is_ok()
            {
                break;
            }
        }

        let ptr = new_end.cast::<T>();

        unsafe { ptr.write(value) };

        BumpBox { ptr, alloc: self }
    }

    pub fn alloc_pin<T>(&self, value: T) -> Pin<BumpBox<'_, T>> {
        unsafe { Pin::new_unchecked(self.alloc(value)) }
    }

    unsafe fn free(&self, ptr: *mut u8, size: usize) {
        let new_end = ptr.add(size);
        _ = self.end.compare_exchange(ptr, new_end, Release, Relaxed);
    }
}

impl Drop for BumpArena {
    fn drop(&mut self) {
        unsafe {
            let layout = std::alloc::Layout::from_size_align(self.size, Self::ALIGN).unwrap();
            std::alloc::dealloc(self.start, layout);
        }
    }
}

pub struct BumpBox<'a, T: ?Sized> {
    alloc: &'a BumpArena,
    ptr: *mut T,
}

unsafe impl<'a, T: Send + ?Sized> Send for BumpBox<'a, T> {}

impl<T: ?Sized> Drop for BumpBox<'_, T> {
    fn drop(&mut self) {
        unsafe {
            let size = std::mem::size_of_val(&*self.ptr);
            self.ptr.drop_in_place();
            self.alloc.free(self.ptr.cast(), size);
        }
    }
}

impl<'a, T: ?Sized> std::ops::Deref for BumpBox<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

impl<'a, T: ?Sized> std::ops::DerefMut for BumpBox<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.ptr }
    }
}

impl<'a, T, U> std::ops::CoerceUnsized<BumpBox<'a, U>> for BumpBox<'a, T>
where
    T: std::marker::Unsize<U> + ?Sized,
    U: ?Sized,
{
}

impl<'a, T: ?Sized> std::fmt::Debug for BumpBox<'a, T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(self, f)
    }
}

impl<'a, T: ?Sized> std::fmt::Display for BumpBox<'a, T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        T::fmt(self, f)
    }
}

impl<F> Future for BumpBox<'_, F>
where
    F: Future + Unpin + ?Sized,
{
    type Output = F::Output;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        let fut: &mut F = &mut self;
        Pin::new(fut).poll(cx)
    }
}
