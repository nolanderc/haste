use std::{
    cell::Cell,
    marker::PhantomData,
    mem::{ManuallyDrop, MaybeUninit},
    ops::ControlFlow,
    panic::AssertUnwindSafe,
};

use context::{
    stack::{ProtectedFixedSizeStack, StackError},
    Context, Transfer,
};

use crate::util::CallOnDrop;

pub struct Coroutine<Output, Yield = ()> {
    #[allow(dead_code)]
    stack: ProtectedFixedSizeStack,
    context: Option<Context>,
    _phantom: PhantomData<(*const Output, *const Yield)>,
}

impl<Output, Yield> Coroutine<Output, Yield> {
    pub fn new<F>(size: usize, f: F) -> Result<Self, StackError>
    where
        F: FnOnce(&mut Yielder<Output, Yield>) -> Output,
    {
        let stack = ProtectedFixedSizeStack::new(usize::max(size, 4 * 4096))?;
        Ok(Self::with_stack(stack, move |yielder| {
            let output = f(yielder);
            yielder.finish(output)
        }))
    }

    fn with_stack<F>(stack: ProtectedFixedSizeStack, func: F) -> Self
    where
        F: FnOnce(&mut Yielder<Output, Yield>) -> Never,
    {
        let context = unsafe { Context::new(&stack, Self::entry_point::<F>) };

        // initialize the coroutine with the function
        let f = MaybeUninit::new(CoroInit { func });
        let transfer = unsafe { context.resume(f.as_ptr() as usize) };

        Self {
            stack,
            context: Some(transfer.context),
            _phantom: PhantomData,
        }
    }

    extern "C" fn entry_point<F>(transfer: Transfer) -> !
    where
        F: FnOnce(&mut Yielder<Output, Yield>) -> Never,
    {
        let mut yielder = Yielder {
            transfer: ManuallyDrop::new(transfer),
            _phantom: PhantomData,
        };

        let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let init = unsafe { (yielder.transfer.data as *const CoroInit<F>).read() };

            let func = init.func;

            yielder.resume(0);

            func(&mut yielder)
        }));

        match result {
            Ok(never) => match never {},
            Err(payload) => {
                PANIC_PAYLOAD.with(|p| p.set(Some(payload)));
                loop {
                    yielder.resume(PANIC);
                }
            }
        }
    }

    pub fn resume(&mut self) -> ControlFlow<Output, Yield> {
        let context = self
            .context
            .take()
            .expect("coroutine resumed after it already terminated");

        let transfer = {
            let old_stack = STACK.with(|stack| {
                stack.replace(Some(StackAddr {
                    top: self.stack.top() as usize,
                    bottom: self.stack.bottom() as usize,
                }))
            });

            let _guard = CallOnDrop::new(move || STACK.with(|stack| stack.set(old_stack)));

            unsafe { context.resume(0) }
        };

        if transfer.data == PANIC {
            let payload = PANIC_PAYLOAD
                .with(|payload| payload.take())
                .expect("coroutine already panicked");

            if payload.is::<Cancel>() {
                panic!("coroutine has been cancelled");
            }

            std::panic::resume_unwind(payload);
        }

        let tag = transfer.data & 0b11;
        let addr = transfer.data & !0b11;

        match tag {
            tag::YIELD => {
                self.context = Some(transfer.context);
                let yield_ = unsafe { &mut *(addr as *mut AlignedTransfer<Yield>) };
                ControlFlow::Continue(yield_.0.take().unwrap())
            }
            tag::FINISH => {
                let output = unsafe { &mut *(addr as *mut AlignedTransfer<Output>) };
                ControlFlow::Break(output.0.take().unwrap())
            }
            _ => unreachable!("invalid tag: {tag}"),
        }
    }
}

impl<Output, Yield> Drop for Coroutine<Output, Yield> {
    fn drop(&mut self) {
        if let Some(context) = self.context.take() {
            unsafe { context.resume(CANCEL) };
        }
    }
}

struct Cancel;

thread_local! {
    static PANIC_PAYLOAD: Cell<Option<PanicPayload>> = Cell::new(None);
}

type PanicPayload = Box<dyn std::any::Any + Send>;

struct CoroInit<F> {
    func: F,
}

pub enum Never {}

pub struct Yielder<Output, Yield = ()> {
    transfer: ManuallyDrop<Transfer>,
    _phantom: PhantomData<(*const Output, *const Yield)>,
}

#[derive(Clone, Copy)]
pub struct StackAddr {
    pub top: usize,
    pub bottom: usize,
}

impl<Output, Yield> Yielder<Output, Yield> {
    pub fn yield_(&mut self, value: Yield) {
        let mut aligned = AlignedTransfer(Some(value));
        self.resume(aligned.addr(tag::YIELD))
    }

    fn finish(&mut self, output: Output) -> ! {
        let mut aligned = AlignedTransfer(Some(output));
        loop {
            self.resume(aligned.addr(tag::FINISH));
        }
    }

    fn resume(&mut self, value: usize) {
        unsafe {
            let context = ManuallyDrop::take(&mut self.transfer).context;
            self.transfer = ManuallyDrop::new(context.resume(value));
            if self.transfer.data == CANCEL {
                std::panic::resume_unwind(Box::new(Cancel));
            }
        }
    }
}

#[repr(align(4))]
struct AlignedTransfer<T>(Option<T>);

impl<T> AlignedTransfer<T> {
    fn addr(&mut self, tag: usize) -> usize {
        assert!(tag < 4);
        (self as *mut Self as usize) | tag
    }
}

const PANIC: usize = 0;
const CANCEL: usize = 1;

mod tag {
    pub const YIELD: usize = 0;
    pub const FINISH: usize = 1;
}

#[test]
fn range_generator() -> Result<(), StackError> {
    let min = 3;
    let max = 10;

    let mut gen = Coroutine::new(4096, |scope| {
        for i in min..max {
            scope.yield_(i);
        }
    })?;

    assert_eq!(gen.resume(), ControlFlow::Continue(3));
    assert_eq!(gen.resume(), ControlFlow::Continue(4));
    assert_eq!(gen.resume(), ControlFlow::Continue(5));
    assert_eq!(gen.resume(), ControlFlow::Continue(6));
    assert_eq!(gen.resume(), ControlFlow::Continue(7));
    assert_eq!(gen.resume(), ControlFlow::Continue(8));
    assert_eq!(gen.resume(), ControlFlow::Continue(9));
    assert_eq!(gen.resume(), ControlFlow::Break(()));

    Ok(())
}

pub fn maybe_grow<F, R>(red_zone: usize, stack_size: usize, callback: F) -> R
where
    F: FnOnce() -> R,
{
    if remaining_stack().unwrap_or(0) > red_zone {
        return callback();
    }

    let mut coro =
        Coroutine::new(stack_size, move |_yielder| callback()).expect("could not allocate stack");

    loop {
        match coro.resume() {
            std::ops::ControlFlow::Continue(()) => unreachable!(),
            std::ops::ControlFlow::Break(value) => return value,
        }
    }
}

pub fn remaining_stack() -> Option<usize> {
    if let Some(stack) = STACK.with(|s| s.get()) {
        let current = psm::stack_pointer() as usize;

        if !(stack.bottom <= current && current <= stack.top) {
            return None;
        }

        match psm::StackDirection::new() {
            psm::StackDirection::Ascending => Some(stack.top - current),
            psm::StackDirection::Descending => Some(current - stack.bottom),
        }
    } else {
        stacker::remaining_stack()
    }
}

thread_local! {
    static STACK: Cell<Option<StackAddr>> = Cell::new(None);
}
