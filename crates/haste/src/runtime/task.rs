use std::{future::Future, pin::Pin};

use crate::IngredientPath;

pub trait QueryTask {
    /// Poll the task for completion.
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<()>;

    /// Get a unique identifier for the query.
    fn path(&self) -> IngredientPath;
}

pub trait StaticQueryTask: QueryTask {
    type StaticFuture: Future<Output = ()> + 'static;

    /// Extend the lifetime of the task to the `'static` lifetime so that it can be spawned on an
    /// executor.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the task does not outlive its original lifetime.
    unsafe fn into_static(self) -> Self::StaticFuture;
}
