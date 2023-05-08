use std::{future::Future, pin::Pin, task::Poll};

use futures::Stream;

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

pub trait IteratorExt: IntoIterator {
    /// Consume the `self` iterator, forcing evaluation of all its items, then returns a stream of
    /// the futures' values.
    ///
    /// This can be used to spawn queries in the `haste` runtime, scheduling them for execution,
    /// and then awaiting their results in parallel.
    fn start_all(self) -> StartAllStream<Self::Item>
    where
        Self: Sized,
        Self::Item: Future,
    {
        StartAllStream::new(self)
    }

    /// Starts all futures in `self` in parallel, and returns a future which evaluates to their
    /// results.
    fn try_join_all(self) -> TryJoinAll<StartAllStream<Self::Item>>
    where
        Self: Sized,
        Self::Item: Future,
        <Self::Item as Future>::Output: Fallible,
    {
        TryJoinAll::new(StartAllStream::new(self))
    }
}

impl<T> IteratorExt for T where T: IntoIterator {}

#[pin_project::pin_project]
pub struct StartAllStream<T> {
    items: std::vec::IntoIter<T>,
    #[pin]
    curr: Option<T>,
}

impl<T> StartAllStream<T> {
    pub fn new(iterator: impl IntoIterator<Item = T>) -> Self {
        Self {
            items: Vec::from_iter(iterator).into_iter(),
            curr: None,
        }
    }
}

impl<T> Stream for StartAllStream<T>
where
    T: Future,
{
    type Item = T::Output;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let mut this = self.project();

        if this.curr.is_none() {
            this.curr.set(this.items.next());
        }

        match this.curr.as_mut().as_pin_mut() {
            None => Poll::Ready(None),
            Some(item) => {
                let value = std::task::ready!(item.poll(cx));
                this.curr.set(None);
                Poll::Ready(Some(value))
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.items.len() + self.curr.is_some() as usize;
        (len, Some(len))
    }
}

pub trait StreamExt: Stream {
    fn try_join_all(self) -> TryJoinAll<Self>
    where
        Self: Sized,
        Self::Item: Fallible,
    {
        TryJoinAll::new(self)
    }
}

impl<T> StreamExt for T where T: Stream {}

#[pin_project::pin_project]
pub struct TryJoinAll<S>
where
    S: Stream,
    S::Item: Fallible,
{
    #[pin]
    stream: S,
    errors: Vec<crate::Diagnostic>,
    values: Vec<<S::Item as Fallible>::Success>,
}

impl<S> TryJoinAll<S>
where
    S: Stream,
    S::Item: Fallible,
{
    pub fn new(stream: S) -> Self {
        let len = match stream.size_hint() {
            (min, Some(max)) if 2 * min >= max || max <= 32 => max,
            (min, _) => min,
        };
        Self {
            stream,
            errors: Vec::new(),
            values: Vec::with_capacity(len),
        }
    }
}

impl<S> Future for TryJoinAll<S>
where
    S: Stream,
    S::Item: Fallible,
{
    type Output = crate::Result<Vec<<S::Item as Fallible>::Success>>;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let mut this = self.project();

        while let Some(result) = std::task::ready!(this.stream.as_mut().poll_next(cx)) {
            match result.into_result() {
                Ok(value) => this.values.push(value),
                Err(error) => this.errors.push(error),
            }
        }

        if this.errors.is_empty() {
            Poll::Ready(Ok(std::mem::take(this.values)))
        } else {
            let errors = std::mem::take(this.errors);
            Poll::Ready(Err(crate::Diagnostic::combine(errors.into_iter())))
        }
    }
}
