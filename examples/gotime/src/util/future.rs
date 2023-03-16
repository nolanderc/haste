use std::{future::Future, pin::Pin, task::Poll};

use crate::Diagnostic;

use super::Fallible;

pub trait FutureExt: Future {
    fn with_context<F>(self, add_context: F) -> WithContextFuture<Self, F>
    where
        Self: Sized,
        F: FnOnce(Diagnostic) -> Diagnostic,
    {
        WithContextFuture {
            inner: self,
            add_context: Some(add_context),
        }
    }
}

impl<F> FutureExt for F where F: Future {}

#[pin_project::pin_project]
pub struct WithContextFuture<T, F> {
    #[pin]
    inner: T,
    add_context: Option<F>,
}

impl<T, F, O> Future for WithContextFuture<T, F>
where
    T: Future<Output = crate::Result<O>>,
    F: FnOnce(Diagnostic) -> Diagnostic,
{
    type Output = crate::Result<O>;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let this = self.project();
        let output = std::task::ready!(this.inner.poll(cx));
        Poll::Ready(output.map_err(this.add_context.take().unwrap()))
    }
}

pub async fn try_join_all<F>(
    items: impl IntoIterator<Item = F>,
) -> crate::Result<Vec<<F::Output as Fallible>::Success>>
where
    F: std::future::Future,
    F::Output: Fallible,
{
    let futures = Vec::from_iter(items);

    let mut outputs = Vec::with_capacity(futures.len());
    let mut errors = Vec::new();

    for future in futures {
        match future.await.into_result() {
            Ok(output) => outputs.push(output),
            Err(error) => errors.push(error),
        }
    }

    if errors.is_empty() {
        Ok(outputs)
    } else {
        Err(crate::Diagnostic::combine(errors.into_iter()))
    }
}
