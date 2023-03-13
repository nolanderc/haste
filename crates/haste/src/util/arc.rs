use std::{
    mem::ManuallyDrop,
    sync::{
        atomic::{AtomicPtr, Ordering},
        Arc, Weak,
    },
};

pub struct AtomicWeak<T> {
    ptr: AtomicPtr<T>,
}

impl<T> AtomicWeak<T> {
    pub fn new(value: Option<Weak<T>>) -> Self {
        let ptr = value.map(Weak::into_raw).unwrap_or(std::ptr::null());
        Self {
            ptr: AtomicPtr::new(ptr.cast_mut()),
        }
    }

    pub fn upgrade(&self, order: Ordering, failure: Ordering) -> Option<Arc<T>> {
        unsafe {
            let ptr = self.ptr.load(order);
            if ptr.is_null() {
                return None;
            }

            let weak = ManuallyDrop::new(Weak::from_raw(ptr));
            let arc = weak.upgrade();

            if arc.is_none() {
                self.swap(None, failure);
            }

            arc
        }
    }

    pub fn swap(&self, value: Option<Weak<T>>, order: Ordering) -> Option<Weak<T>> {
        let ptr = value.map(Weak::into_raw).unwrap_or(std::ptr::null());
        let old = self.ptr.swap(ptr.cast_mut(), order);

        if old.is_null() {
            None
        } else {
            unsafe { Some(Weak::from_raw(old)) }
        }
    }
}

impl<T> Drop for AtomicWeak<T> {
    fn drop(&mut self) {
        let ptr = *self.ptr.get_mut();
        if ptr.is_null() {
            return;
        }
        unsafe { drop(Weak::from_raw(ptr)) }
    }
}
