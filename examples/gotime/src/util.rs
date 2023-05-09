use std::{
    fmt::{Debug, Display, Formatter},
    sync::Arc,
};

use bstr::BStr;

use crate::Diagnostic;

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

pub fn bstr_arc(bytes: Arc<[u8]>) -> Arc<BStr> {
    let ptr: *const [u8] = Arc::into_raw(bytes);
    let ptr: *const BStr = ptr as *const BStr;

    // SAFETY: `BStr` is a `#[repr(transparent)]` wrapper around a `[u8]`, so they have the same
    // memory layout, which makes this transmute safe.
    unsafe { Arc::from_raw(ptr) }
}

pub trait Task {
    type Output;
    fn join(self) -> Self::Output;
}

impl<'a, Q> Task for haste::QueryHandle<'a, Q>
where
    Q: haste::Query,
{
    type Output = Q::View<'a>;

    fn join(self) -> Self::Output {
        self.join()
    }
}

impl<F, T> Task for F
where
    F: FnOnce() -> T,
{
    type Output = T;

    fn join(self) -> Self::Output {
        self()
    }
}

pub trait TaskExt {
    fn with_context<F>(self, add_context: F) -> WithContext<Self, F>
    where
        Self: Sized,
        F: FnOnce(Diagnostic) -> Diagnostic,
    {
        WithContext {
            inner: self,
            add_context,
        }
    }
}

impl<T: Task> TaskExt for T {}

pub struct WithContext<T, F> {
    inner: T,
    add_context: F,
}

impl<T, F> Task for WithContext<T, F>
where
    T: Task,
    T::Output: Fallible,
    F: FnOnce(Diagnostic) -> Diagnostic,
{
    type Output = crate::Result<<T::Output as Fallible>::Success>;

    fn join(self) -> Self::Output {
        self.inner.join().into_result().map_err(self.add_context)
    }
}

pub fn try_join_all<I>(
    tasks: I,
) -> crate::Result<Vec<<<I::Item as Task>::Output as Fallible>::Success>>
where
    I: IntoIterator,
    I::Item: Task,
    <I::Item as Task>::Output: Fallible,
{
    let tasks = Vec::from_iter(tasks);

    let mut errors = Vec::new();
    let mut values = Vec::with_capacity(tasks.len());

    for task in tasks {
        match task.join().into_result() {
            Ok(value) => values.push(value),
            Err(error) => errors.push(error),
        }
    }

    if errors.is_empty() {
        Ok(values)
    } else {
        Err(crate::Diagnostic::combine(errors))
    }
}
