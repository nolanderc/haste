#[cfg(target_family = "unix")]
pub use self::unix::*;

#[cfg(target_family = "unix")]
pub mod unix {
    use std::{
        ptr::{self, NonNull},
        sync::atomic::{AtomicUsize, Ordering},
    };

    static PAGE_SIZE: AtomicUsize = AtomicUsize::new(0);

    fn get_page_size() -> usize {
        match PAGE_SIZE.load(Ordering::Relaxed) {
            0 => {
                let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
                assert!(size.is_power_of_two(), "page size is not power of two");
                PAGE_SIZE.store(size, Ordering::Relaxed);
                size
            }
            size => size,
        }
    }

    /// Reserve a region of memory which is at least `size` bytes large.
    ///
    /// All memory is initially 0.
    pub fn reserve(size: usize) -> NonNull<u8> {
        let protection = libc::PROT_NONE;
        let flags = libc::MAP_ANONYMOUS | libc::MAP_PRIVATE;
        let ptr = unsafe { libc::mmap(ptr::null_mut(), size, protection, flags, -1, 0) };
        match NonNull::new(ptr) {
            Some(ptr) => ptr.cast(),
            None => panic!("could not reserve virtual memory ({} bytes)", size),
        }
    }

    /// Marks the memory range `[ptr, ptr+size-1]` as being in use.
    ///
    /// # Safety
    ///
    /// The memory region lies within a successful call to `reserve`.
    pub unsafe fn commit(mut ptr: *mut u8, mut size: usize) {
        let page_size = get_page_size();
        let page_mask = page_size - 1;

        // align the pointer to the nearest page boundary, adjusting the size as necessary
        let addr = ptr as usize;
        let page_aligned_addr = addr & !page_mask;
        size += addr - page_aligned_addr;
        ptr = page_aligned_addr as *mut u8;

        let protection = libc::PROT_READ | libc::PROT_WRITE;
        if libc::mprotect(ptr.cast(), size, protection) == 0 {
            return;
        }

        panic!("could not commit memory region: {:p}+{}", ptr, size)
    }

    /// Unmap a region of memory.
    ///
    /// # Safety
    ///
    /// The memory region must be the entire region returned by a call to `reserve`.
    pub unsafe fn release(ptr: *mut u8, size: usize) {
        libc::munmap(ptr.cast(), size);
    }
}
