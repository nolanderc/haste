use std::{
    collections::VecDeque,
    sync::{
        atomic::{AtomicUsize, Ordering::Relaxed},
        Mutex,
    },
};

use super::task::Task;

pub struct Injector {
    approx_len: AtomicUsize,
    tasks: Mutex<VecDeque<Task>>,
}

impl Injector {
    pub fn new() -> Self {
        Self {
            approx_len: AtomicUsize::new(0),
            tasks: Mutex::new(VecDeque::with_capacity(1024)),
        }
    }

    /// Inject a new task, returning the number of tasks available
    pub fn push(&self, task: Task) {
        self.approx_len.fetch_add(1, Relaxed);
        self.tasks.lock().unwrap().push_back(task);
    }

    pub fn pop(&self) -> Option<Task> {
        let _guard = crate::enter_span(|| "steal global");

        if self.approx_len.load(Relaxed) == 0 {
            return None;
        }

        let task = self.tasks.lock().unwrap().pop_back()?;
        self.approx_len.fetch_sub(1, Relaxed);
        Some(task)
    }

    pub fn drain(&self) {
        self.tasks.lock().unwrap().clear();
    }
}
