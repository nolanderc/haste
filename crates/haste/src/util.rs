mod signal;
pub mod fmt;

pub use signal::{DropSignal, Signal, WaitSignal};

pub struct CallOnDrop<T, F: FnMut() -> T>(pub F);

impl<T, F: FnMut() -> T> Drop for CallOnDrop<T, F> {
    fn drop(&mut self) {
        let _ = self.0();
    }
}
