use std::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    ptr::NonNull,
    sync::atomic::{
        AtomicU8, AtomicUsize,
        Ordering::{Acquire, Relaxed, Release},
    },
};

mod memory;

pub struct RawArena<T> {
    ptr: NonNull<T>,
    reserved: AtomicUsize,
    committed: AtomicUsize,
    capacity: usize,
}

unsafe impl<T: Send> Send for RawArena<T> {}
unsafe impl<T: Send + Sync> Sync for RawArena<T> {}

impl<T> Default for RawArena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> RawArena<T> {
    pub fn new() -> Self {
        Self::with_capacity(u32::MAX as usize)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let bytes = std::mem::size_of::<T>() * capacity;
        let ptr = memory::reserve(bytes);
        assert_eq!(
            ptr.as_ptr() as usize & (std::mem::align_of::<T>() - 1),
            0,
            "allocated memory was not aligned"
        );

        Self {
            ptr: ptr.cast(),
            reserved: AtomicUsize::new(0),
            committed: AtomicUsize::new(0),
            capacity,
        }
    }

    /// Get a pointer to the value at the given offset.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the given offset lies within the allocated memory region.
    pub unsafe fn get_raw(&self, offset: usize) -> *mut T {
        self.ptr.as_ptr().add(offset)
    }

    /// Get a reference to the value at the given index.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the given index lies within the allocated memory region and
    /// that it is properly initialized.
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &*self.get_raw(index)
    }

    /// Get a mutable reference to the value at the given index.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the given index lies within the allocated memory region and
    /// that it is properly initialized.
    #[allow(unused)]
    pub unsafe fn get_mut_unchecked(&mut self, index: usize) -> &mut T {
        &mut *self.get_raw(index)
    }

    /// Returns `true` if the `index` has been allocated
    pub fn is_allocated(&self, index: usize) -> bool {
        index < self.committed.load(Relaxed)
    }
}

impl<T> RawArena<T>
where
    T: bytemuck::Zeroable,
{
    /// Get a reference to the value at the given index. Returns `None` if the index has not yet
    /// been allocated.
    pub fn get(&self, index: usize) -> Option<&T> {
        if self.is_allocated(index) {
            // SAFETY: since we only allow values that have been initialized to zero, they are
            // implicitly initialized as long they have been allocated.
            unsafe { Some(self.get_unchecked(index)) }
        } else {
            None
        }
    }

    /// Get a mutable reference to the value at the given index. Returns `None` if the index has
    /// not yet been allocated.
    #[allow(unused)]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if self.is_allocated(index) {
            // SAFETY: since we only allow values that have been initialized to zero, they are
            // implicitly initialized as long they have been allocated.
            unsafe { Some(self.get_mut_unchecked(index)) }
        } else {
            None
        }
    }

    /// Get a reference to the value at the given index. If the value is not allocated, grows the
    /// underlying buffer up until that index.
    pub(crate) fn get_or_allocate(&self, index: usize) -> &T {
        let committed = self.committed.load(Relaxed);
        let old_reserved = self.reserved.fetch_max(index + 1, Relaxed);

        if index >= committed {
            let new_reserved = old_reserved.max(index + 1);
            unsafe { self.grow(committed, new_reserved) };
        }

        return unsafe { self.get_unchecked(index) };
    }

    /// Get an index into the arena to a region of zero-initialized memory.
    pub fn reserve_zeroed(&self, count: usize) -> usize {
        let offset = self.reserved.fetch_add(count, Relaxed);
        let new_reserved = offset + count;

        let old_committed = self.committed.load(Relaxed);
        if new_reserved > old_committed {
            unsafe { self.grow(old_committed, new_reserved) };
        }

        offset
    }

    unsafe fn grow(&self, current_len: usize, required: usize) {
        if required > self.capacity {
            panic!("out of memory");
        }

        let new = current_len.saturating_mul(2).clamp(required, self.capacity);

        // SAFETY: we know that `new` is in the range `[0, self.capacity]`. Thus `old_ptr` will
        // also lie within the reserved memory range, and we can safely commit it.
        let old_ptr = self.get_raw(current_len).cast();
        let new_bytes = (new - current_len) * std::mem::size_of::<T>();
        memory::commit(old_ptr, new_bytes);

        self.committed.fetch_max(new, Relaxed);
    }

    /// Push a new zero-initialized value to the end of the allocated memory region.
    pub fn push_zeroed(&self) -> usize {
        self.reserve_zeroed(1)
    }
}

impl<T> Drop for RawArena<T> {
    fn drop(&mut self) {
        unsafe {
            memory::release(
                self.ptr.as_ptr().cast(),
                self.capacity * std::mem::size_of::<T>(),
            );
        }
    }
}

pub struct Arena<T> {
    raw: RawArena<OnceCell<T>>,
}

unsafe impl<T: Send> Send for Arena<T> {}
unsafe impl<T: Send + Sync> Sync for Arena<T> {}

impl<T> std::ops::Index<usize> for Arena<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index) {
            Some(value) => value,
            None => panic!("index out of bounds: {index}"),
        }
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            raw: RawArena::new(),
        }
    }

    #[allow(unused)]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            raw: RawArena::with_capacity(capacity),
        }
    }

    pub fn push(&self, value: T) -> usize {
        let index = self.raw.push_zeroed();
        // SAFETY: we just pushed this index, so no other thread will write to the same slot.
        unsafe { self.raw.get_unchecked(index).write_unique(value) };
        index
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        self.raw.get(index)?.get()
    }

    #[allow(dead_code)]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.raw.get_mut(index)?.get_mut()
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A region of memory that can only be initialized once.
///
/// This implements `Zeroable`, which is the primary way to construct it.
struct OnceCell<T> {
    state: OnceCellState,
    value: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T> bytemuck::Zeroable for OnceCell<T> {}

impl<T> OnceCell<T> {
    #[allow(unused)]
    fn write(&self, value: T) -> Result<&T, T> {
        if !self.state.start_write() {
            return Err(value);
        }
        unsafe { Ok(self.write_unique(value)) }
    }

    /// # Safety
    ///
    /// The caller ensures that the cell has never been written to before and that there are no
    /// concurrent writes.
    unsafe fn write_unique(&self, value: T) -> &T {
        self.value.get().write(MaybeUninit::new(value));
        self.state.finish_write();
        self.get_unchecked()
    }

    fn get(&self) -> Option<&T> {
        if !self.state.is_written() {
            return None;
        }
        unsafe { Some(self.get_unchecked()) }
    }

    #[allow(dead_code)]
    fn get_mut(&mut self) -> Option<&mut T> {
        if !self.state.is_written() {
            return None;
        }
        unsafe { Some(self.get_mut_unchecked()) }
    }

    unsafe fn get_unchecked(&self) -> &T {
        (*self.value.get()).assume_init_ref()
    }

    #[allow(dead_code)]
    unsafe fn get_mut_unchecked(&mut self) -> &mut T {
        (*self.value.get()).assume_init_mut()
    }
}

struct OnceCellState {
    state: AtomicU8,
}

impl OnceCellState {
    /// The slot is currently being initialized by some thread.
    const BEING_WRITTEN: u8 = 0x1;

    /// The slot is fully initialized.
    const INITIALIZED: u8 = 0x2;

    fn is(mask: u8, state: u8) -> bool {
        (state & mask) != 0
    }

    pub fn start_write(&self) -> bool {
        let old_state = self.state.fetch_or(Self::BEING_WRITTEN, Relaxed);
        !Self::is(Self::BEING_WRITTEN, old_state)
    }

    pub unsafe fn finish_write(&self) {
        let finished = Self::BEING_WRITTEN | Self::INITIALIZED;
        self.state.store(finished, Release);
    }

    pub fn is_written(&self) -> bool {
        Self::is(Self::INITIALIZED, self.state.load(Acquire))
    }
}

unsafe impl bytemuck::Zeroable for OnceCellState {}

/// An arena where values can be cheaply appended at the end, but reading requires the caller to
/// guarantee that indices are valid.
///
/// Unlike `Vec` this never requires reallocating the backing buffer, which might be faster once
/// the arena grows larger. This also means that one can hold onto references into the backing
/// buffer accross write calls and multiple threads.
pub struct AppendArena<T> {
    raw: RawArena<UnsafeCell<MaybeUninit<T>>>,
}

unsafe impl<T: Send> Send for AppendArena<T> {}
unsafe impl<T: Send + Sync> Sync for AppendArena<T> {}

impl<T> Default for AppendArena<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> AppendArena<T> {
    pub fn new() -> Self {
        Self {
            raw: RawArena::new(),
        }
    }

    /// Push a value to the arena, returning its index
    #[allow(unused)]
    pub fn push(&self, value: T) -> usize {
        let index = self.raw.push_zeroed();

        let cell = UnsafeCell::new(MaybeUninit::new(value));

        // SAFETY: no other thread will read or write to/from this index as we have not made it
        // available yet, so we have exclusive access to this slot.
        unsafe { self.raw.get_raw(index).write(cell) };

        index
    }

    /// Append a sequence of values at the end of the buffer, returning the range they inhabit.
    #[allow(unused)]
    pub fn extend(
        &self,
        mut values: impl Iterator<Item = T> + ExactSizeIterator,
    ) -> std::ops::Range<usize> {
        let len = values.len();
        let start = self.raw.reserve_zeroed(len);

        unsafe {
            let ptr = self.raw.get_raw(start);
            for i in 0..len {
                let value = values.next().expect("buggy ExactSizeIterator impl");

                // SAFETY: no other thread will read or write to/from this index as we have not made it
                // available yet, so we have exclusive access to this slot.
                ptr.add(i).write(UnsafeCell::new(MaybeUninit::new(value)));
            }
        }

        start..start + len
    }

    pub fn extend_from_slice(&self, values: &[T]) -> std::ops::Range<usize>
    where
        T: Copy,
    {
        let start = self.raw.reserve_zeroed(values.len());
        unsafe {
            let ptr = self.raw.get_raw(start);
            ptr.copy_from_nonoverlapping(values.as_ptr().cast(), values.len())
        }
        start..start + values.len()
    }

    /// Get the value at the given index.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the provided index is valid for this structure (ie. it was
    /// previously returned from a call to `push`).
    #[allow(unused)]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        (*self.raw.get_unchecked(index).get()).assume_init_ref()
    }

    /// Get a range of values.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the provided indices are valid for this structure (ie. they
    /// were previously returned from a call to `append`).
    #[allow(unused)]
    pub unsafe fn get_slice_unchecked(&self, range: std::ops::Range<usize>) -> &[T] {
        let len = range.end - range.start;
        let ptr = UnsafeCell::raw_get(self.raw.get_raw(range.start));
        std::slice::from_raw_parts(ptr.cast(), len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_arena_alloc() {
        let arena = RawArena::<u32>::new();

        for _ in 0..10 {
            let index = arena.push_zeroed();
            assert_eq!(arena.get(index), Some(&0));
        }

        let count = 1 << 12;
        let index = arena.reserve_zeroed(count);
        for i in index..index + count {
            assert_eq!(arena.get(i), Some(&0));
        }
    }

    #[test]
    fn typed_arena_alloc() {
        let arena = Arena::<u32>::new();

        for x in 0..1 << 12 {
            let index = arena.push(x);
            assert_eq!(arena.get(index), Some(&x));
        }
    }
}
