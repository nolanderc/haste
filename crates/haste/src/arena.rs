use std::{
    cell::UnsafeCell,
    marker::PhantomData,
    mem::MaybeUninit,
    sync::{
        atomic::{
            AtomicPtr, AtomicU8, AtomicUsize,
            Ordering::{Acquire, Relaxed, Release},
        },
        Mutex,
    },
};

pub struct RawArena<T> {
    allocation: region::Allocation,
    reserved: AtomicUsize,
    committed: AtomicUsize,
    _phantom: PhantomData<T>,
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
        let bytes = std::mem::size_of::<T>()
            .checked_mul(capacity)
            .expect("allocation exceeds system limits");

        let allocation = region::alloc(bytes, region::Protection::NONE).expect("allocation failed");

        let ptr = allocation.as_ptr::<u8>();
        assert_eq!(
            ptr as usize & (std::mem::align_of::<T>() - 1),
            0,
            "allocated memory was not aligned"
        );

        Self {
            allocation,
            reserved: AtomicUsize::new(0),
            committed: AtomicUsize::new(0),
            _phantom: PhantomData,
        }
    }

    pub fn capacity(&self) -> usize {
        self.allocation.len() / std::mem::size_of::<T>()
    }

    /// Get a pointer to the value at the given offset.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the given offset lies within the allocated memory region.
    pub unsafe fn get_raw(&self, offset: usize) -> *mut T {
        self.allocation.as_ptr::<T>().cast_mut().add(offset)
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
        if required > self.capacity() {
            panic!("out of memory");
        }

        let new = current_len
            .saturating_mul(8)
            .max(256)
            .clamp(required.next_power_of_two(), self.capacity());

        // SAFETY: we know that `new` is in the range `[0, self.capacity]`. Thus `old_ptr` will
        // also lie within the reserved memory range, and we can safely commit it.
        let old_ptr = self.get_raw(current_len);
        let additional_bytes = (new - current_len) * std::mem::size_of::<T>();

        region::protect(
            old_ptr.cast_const().cast::<u8>(),
            additional_bytes,
            region::Protection::READ_WRITE,
        )
        .expect("could not commit memory");

        self.committed.fetch_max(new, Relaxed);
    }

    /// Push a new zero-initialized value to the end of the allocated memory region.
    pub fn push_zeroed(&self) -> usize {
        self.reserve_zeroed(1)
    }
}

impl<T> Drop for RawArena<T> {
    fn drop(&mut self) {
        if !std::mem::needs_drop::<T>() {
            return;
        }

        let len = *self.reserved.get_mut();
        let start = self.allocation.as_mut_ptr::<T>();
        for i in 0..len {
            unsafe { start.add(i).drop_in_place() };
        }
    }
}

const INIT_BUCKET: usize = 32;
const BUCKETS: usize = 32;

#[allow(dead_code)]
pub struct BucketArena<T> {
    buckets: [Bucket<T>; BUCKETS],
}

pub struct Bucket<T> {
    ptr: AtomicPtr<T>,
    init_mutex: Mutex<()>,
}

impl<T> BucketArena<T> {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            buckets: std::array::from_fn(|_| Bucket::new()),
        }
    }
}

impl<T> BucketArena<T>
where
    T: bytemuck::Zeroable,
{
    #[allow(dead_code)]
    pub fn get(&self, index: usize) -> &T {
        let bucket = find_bucket(index);
        let bucket_size = bucket_size(bucket);
        let subindex = index - bucket_size * (bucket != 0) as usize;
        unsafe { &*self.buckets[bucket].get_or_init(subindex, bucket_size) }
    }

    #[allow(dead_code)]
    pub fn get_mut(&mut self, index: usize) -> &mut T {
        let bucket = find_bucket(index);
        let bucket_size = bucket_size(bucket);
        let subindex = index - bucket_size * (bucket != 0) as usize;
        unsafe { &mut *self.buckets[bucket].get_or_init(subindex, bucket_size) }
    }
}

impl<T> Drop for BucketArena<T> {
    fn drop(&mut self) {
        for (i, bucket) in self.buckets.iter_mut().enumerate() {
            let ptr = *bucket.ptr.get_mut();
            if ptr.is_null() {
                continue;
            }
            let size = bucket_size(i);
            let layout = std::alloc::Layout::array::<T>(size).unwrap();
            unsafe { std::alloc::dealloc(ptr.cast(), layout) };
        }
    }
}

/// Given the index of a bucket, its size.
fn bucket_size(bucket_index: usize) -> usize {
    INIT_BUCKET << bucket_index.saturating_sub(1)
}

/// Get the index of an element, the bucket it lies in.
fn find_bucket(index: usize) -> usize {
    // index norm norm+1 power ilog bucket size start
    //     0    0      1     1    0      0    2     0
    //     1    0      1     1    0      0    2     0
    //     2    1      2     2    1      1    2     2
    //     3    1      2     2    1      1    2     2
    //     4    2      3     4    1      2    4     4
    //     5    2      3     4    1      2    4     4
    //     6    3      4     4    0      2    4     4
    //     7    3      4     4    0      2    4     4
    //     8    4      5     8    0      3    8     8
    let norm = index / INIT_BUCKET;
    let power = (norm + 1).next_power_of_two();
    let bucket = power.trailing_zeros();
    bucket as usize
}

#[test]
fn bucket_indexing() {
    assert_eq!(find_bucket(0), 0);
    assert_eq!(find_bucket(INIT_BUCKET - 1), 0);

    assert_eq!(find_bucket(INIT_BUCKET), 1);
    assert_eq!(find_bucket(2 * INIT_BUCKET - 1), 1);

    assert_eq!(find_bucket(2 * INIT_BUCKET), 2);
    assert_eq!(find_bucket(4 * INIT_BUCKET - 1), 2);

    assert_eq!(find_bucket(4 * INIT_BUCKET), 3);
    assert_eq!(find_bucket(8 * INIT_BUCKET - 1), 3);
}

impl<T> Bucket<T> {
    pub const fn new() -> Self {
        Self {
            ptr: AtomicPtr::new(std::ptr::null_mut()),
            init_mutex: Mutex::new(()),
        }
    }
}

impl<T> Bucket<T>
where
    T: bytemuck::Zeroable,
{
    pub unsafe fn get_or_init(&self, index: usize, size: usize) -> *mut T {
        let mut ptr = self.ptr.load(Relaxed);
        if ptr.is_null() {
            ptr = self.init(size);
        }
        ptr.add(index)
    }

    fn init(&self, size: usize) -> *mut T {
        let _guard = self.init_mutex.lock();

        // another thread may have beaten us to it
        let ptr = self.ptr.load(Relaxed);
        if !ptr.is_null() {
            return ptr;
        }

        let layout = std::alloc::Layout::array::<T>(size).unwrap();

        let ptr = unsafe { std::alloc::alloc_zeroed(layout).cast::<T>() };
        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        self.ptr.store(ptr, Relaxed);

        ptr
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

impl<T> Drop for OnceCell<T> {
    fn drop(&mut self) {
        if std::mem::needs_drop::<T>() && self.state.is_written() {
            unsafe { self.value.get_mut().assume_init_drop() }
        }
    }
}

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
