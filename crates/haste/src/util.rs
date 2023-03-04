pub mod fmt;
mod signal;

pub use signal::{DropSignal, Signal, WaitSignal};

pub struct CallOnDrop<T, F: FnMut() -> T>(pub F);

impl<T, F: FnMut() -> T> Drop for CallOnDrop<T, F> {
    fn drop(&mut self) {
        let _ = self.0();
    }
}

pub struct SendWrapper<T>(pub T);

unsafe impl<T> Send for SendWrapper<T> {}
unsafe impl<T> Sync for SendWrapper<T> {}

impl<T> std::ops::Deref for SendWrapper<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> std::ops::DerefMut for SendWrapper<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
