use std::{
    future::Future,
    sync::{Arc, Mutex},
    task::Waker,
};

pub struct Signal {
    state: Arc<SignalState>,
}

pub struct WaitSignal {
    state: Arc<SignalState>,
    registered: bool,
}

struct SignalState {
    wakers: Mutex<Option<Vec<Waker>>>,
}

impl Signal {
    pub fn new() -> Self {
        Signal {
            state: Arc::new(SignalState {
                wakers: Mutex::new(Some(Vec::new())),
            }),
        }
    }

    pub fn wait(&self) -> WaitSignal {
        WaitSignal {
            state: self.state.clone(),
            registered: false,
        }
    }
}

impl Drop for Signal {
    fn drop(&mut self) {
        let wakers = self.state.wakers.lock().unwrap().take();
        for waker in wakers.unwrap() {
            waker.wake();
        }
    }
}

impl Future for WaitSignal {
    type Output = ();

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        let this = self.get_mut();

        let wakers = &mut *this.state.wakers.lock().unwrap();
        match wakers {
            None => std::task::Poll::Ready(()),
            Some(list) => {
                if !this.registered {
                    this.registered = true;
                    let waker = cx.waker().clone();
                    list.push(waker);
                }
                std::task::Poll::Pending
            }
        }
    }
}
