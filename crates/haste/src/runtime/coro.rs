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

    fn with_stack<F>(stack: ProtectedFixedSizeStack, f: F) -> Self
    where
        F: FnOnce(&mut Yielder<Output, Yield>) -> Never,
    {
        let context = unsafe { Context::new(&stack, Self::entry_point::<F>) };

        // initialize the coroutine with the function
        let f = MaybeUninit::new(f);
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
            let f: F = unsafe { (yielder.transfer.data as *const F).read() };
            yielder.resume(0);
            f(&mut yielder)
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

        let transfer = unsafe { context.resume(0) };

        if transfer.data == PANIC {
            let payload = PANIC_PAYLOAD
                .with(|payload| payload.take())
                .expect("coroutine already panicked");

            if payload.is::<Cancel>() {
                panic!("coroutine has been cancelled");
            }

            std::panic::resume_unwind(payload);
        }

        if transfer.data & 1 == 1 {
            self.context = Some(transfer.context);

            let addr = transfer.data & !1;
            let yield_ = unsafe { &mut *(addr as *mut AlignedTransfer<Yield>) };
            let yield_ = yield_.0.take().unwrap();

            return ControlFlow::Continue(yield_);
        }

        let output = unsafe { &mut *(transfer.data as *mut AlignedTransfer<Output>) };
        ControlFlow::Break(output.0.take().unwrap())
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

pub enum Never {}

pub struct Yielder<Output, Yield> {
    transfer: ManuallyDrop<Transfer>,
    _phantom: PhantomData<(*const Output, *const Yield)>,
}

impl<Output, Yield> Yielder<Output, Yield> {
    pub fn yield_(&mut self, value: Yield) {
        let mut aligned = AlignedTransfer(Some(value));
        self.resume(aligned.addr(true))
    }

    fn finish(&mut self, output: Output) -> ! {
        let mut aligned = AlignedTransfer(Some(output));
        loop {
            self.resume(aligned.addr(false))
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
    fn addr(&mut self, yield_: bool) -> usize {
        (self as *mut Self as usize) | (yield_ as usize)
    }
}

const PANIC: usize = 0;
const CANCEL: usize = 1;

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
