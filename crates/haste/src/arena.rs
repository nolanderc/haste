use std::{
    alloc::Layout,
    marker::PhantomData,
    sync::atomic::{
        AtomicUsize,
        Ordering::{AcqRel, Relaxed},
    },
};

pub struct RawArena {
    allocation: region::Allocation,
    committed: AtomicUsize,
}

unsafe impl Sync for RawArena {}
unsafe impl Send for RawArena {}

impl RawArena {
    pub fn new(layout: Layout) -> Self {
        let size = page_ceil(layout.size());

        let allocation =
            region::alloc(size, region::Protection::NONE).expect("memory allocation failed");

        if (allocation.as_ptr::<u8>() as usize & (layout.align() - 1)) != 0 {
            panic!("unaligned allocation")
        }

        let initial_size = page_ceil(size / 256);

        unsafe {
            region::protect(
                allocation.as_ptr::<u8>(),
                initial_size,
                region::Protection::READ_WRITE,
            )
            .expect("allocation failed");
        }

        Self {
            allocation,
            committed: AtomicUsize::new(initial_size),
        }
    }

    pub fn grow(&self, min_size: usize) {
        let current = self.committed.load(Relaxed);
        if min_size < current {
            return;
        }

        if min_size > self.allocation.len() {
            panic!("out of memory");
        }

        let mut new_size = (current * 2).clamp(min_size, self.allocation.len());
        new_size = page_ceil(new_size);

        unsafe {
            region::protect(
                self.allocation.as_ptr::<u8>(),
                new_size,
                region::Protection::READ_WRITE,
            )
            .expect("allocation failed");
        }

        self.committed.fetch_max(new_size, AcqRel);
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.allocation.as_ptr()
    }
}

fn page_ceil(size: usize) -> usize {
    let page_size = region::page::size();
    (size + page_size - 1) & !(page_size - 1)
}

pub struct Arena<T> {
    raw: RawArena,
    _phantom: PhantomData<*const T>,
}

unsafe impl<T: Send> Send for Arena<T> {}
unsafe impl<T: Send + Sync> Sync for Arena<T> {}

impl<T> Arena<T> {
    pub fn with_capacity(len: usize) -> Self {
        Self {
            raw: RawArena::new(Layout::array::<T>(len).unwrap()),
            _phantom: PhantomData,
        }
    }

    pub fn ensure_in_bounds(&self, index: usize)
    where
        T: bytemuck::Zeroable,
    {
        let required_len = index + 1;
        self.raw.grow(required_len * std::mem::size_of::<T>());
    }

    pub fn get_or_allocate(&self, index: usize) -> &T
    where
        T: bytemuck::Zeroable,
    {
        self.ensure_in_bounds(index);
        unsafe { self.get_unchecked(index) }
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        unsafe { &*self.raw.as_ptr().cast::<T>().add(index) }
    }
}
