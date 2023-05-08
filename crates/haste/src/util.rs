use std::mem::MaybeUninit;

/// Type erased pointer to a fat pointer
#[repr(C)]
pub struct DynPointer {
    addr: [MaybeUninit<usize>; 2],
}

impl DynPointer {
    pub fn erase<T: ?Sized>(ptr: *const T) -> DynPointer {
        unsafe {
            let ptr_bytes: &[u8] = std::slice::from_raw_parts(
                &ptr as *const *const T as *const u8,
                std::mem::size_of::<*const T>(),
            );

            let mut bytes = [0u8; std::mem::size_of::<DynPointer>()];
            bytes[..ptr_bytes.len()].copy_from_slice(ptr_bytes);
            std::mem::transmute(bytes)
        }
    }

    pub unsafe fn unerase<T: ?Sized>(self) -> *const T {
        let mut ptr = MaybeUninit::<*const T>::uninit();
        let ptr_bytes: &mut [MaybeUninit<u8>] = std::slice::from_raw_parts_mut(
            (&mut ptr as *mut MaybeUninit<*const T>).cast(),
            std::mem::size_of::<*const T>(),
        );

        let bytes: [MaybeUninit<u8>; std::mem::size_of::<DynPointer>()] = std::mem::transmute(self);
        ptr_bytes.copy_from_slice(&bytes[..std::mem::size_of::<*const T>()]);
        ptr.assume_init()
    }
}
