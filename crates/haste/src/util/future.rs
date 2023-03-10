use std::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

pub fn map<Fut, F, T>(future: Fut, func: F) -> impl Future<Output = T>
where
    Fut: Future,
    F: FnOnce(Fut::Output) -> T,
{
    #[pin_project::pin_project(project = MapProj, project_replace = MapProjReplace)]
    enum Map<Fut, F> {
        Running {
            #[pin]
            future: Fut,
            func: F,
        },
        Done,
    }

    impl<Fut, F, T> Future for Map<Fut, F>
    where
        Fut: Future,
        F: FnOnce(Fut::Output) -> T,
    {
        type Output = T;

        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            match self.as_mut().project() {
                MapProj::Running { future, .. } => {
                    let output = std::task::ready!(future.poll(cx));
                    match self.project_replace(Self::Done) {
                        MapProjReplace::Running { func, .. } => Poll::Ready(func(output)),
                        MapProjReplace::Done => unreachable!(),
                    }
                }
                MapProj::Done => panic!(
                    "`{}` polled after it returned `Ready`",
                    std::any::type_name::<Self>()
                ),
            }
        }
    }

    Map::Running { future, func }
}

pub fn poll_fn_pin<Fut, F, T>(future: Fut, poll_fn: F) -> impl Future<Output = T>
where
    F: FnMut(Pin<&mut Fut>, &mut Context) -> Poll<T>,
{
    #[pin_project::pin_project]
    struct PollFnPin<Fut, F> {
        #[pin]
        future: Fut,
        poll_fn: F,
    }

    impl<Fut, F, T> Future for PollFnPin<Fut, F>
    where
        F: FnMut(Pin<&mut Fut>, &mut Context) -> Poll<T>,
    {
        type Output = T;

        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            let this = self.project();
            (this.poll_fn)(this.future, cx)
        }
    }

    PollFnPin { future, poll_fn }
}
