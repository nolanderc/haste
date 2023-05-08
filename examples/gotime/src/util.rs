use std::{
    fmt::{Debug, Display, Formatter},
    sync::Arc,
};

use bstr::BStr;

pub mod future;

pub fn display_fn<F>(f: F) -> DisplayFn<F>
where
    F: Fn(&mut Formatter<'_>) -> std::fmt::Result,
{
    DisplayFn(f)
}

pub struct DisplayFn<F>(F);

impl<F> Display for DisplayFn<F>
where
    F: Fn(&mut Formatter<'_>) -> std::fmt::Result,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        (self.0)(f)
    }
}

impl<F> Debug for DisplayFn<F>
where
    F: Fn(&mut Formatter<'_>) -> std::fmt::Result,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        (self.0)(f)
    }
}

pub trait Fallible {
    type Success;
    fn into_result(self) -> crate::Result<Self::Success>;
}

impl<T> Fallible for crate::Result<T> {
    type Success = T;
    fn into_result(self) -> crate::Result<T> {
        self
    }
}

impl<'a, T> Fallible for &'a crate::Result<T> {
    type Success = &'a T;
    fn into_result(self) -> crate::Result<&'a T> {
        match self {
            Ok(output) => Ok(output),
            Err(error) => Err(error.clone()),
        }
    }
}

pub fn fmt_tuple<T>(items: &[T]) -> impl Display + '_
where
    T: Display,
{
    display_fn(move |f| {
        write!(f, "(")?;
        for (i, item) in items.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            T::fmt(item, f)?;
        }
        write!(f, ")")?;
        Ok(())
    })
}

pub fn bstr_arc(bytes: Arc<[u8]>) -> Arc<BStr> {
    let ptr: *const [u8] = Arc::into_raw(bytes);
    let ptr: *const BStr = ptr as *const BStr;

    // SAFETY: `BStr` is a `#[repr(transparent)]` wrapper around a `[u8]`, so they have the same
    // memory layout, which makes this transmute safe.
    unsafe { Arc::from_raw(ptr) }
}
