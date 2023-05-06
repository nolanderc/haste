mod lookup;
mod state;

use std::{cell::UnsafeCell, hash::Hash, mem::MaybeUninit};

use crate::{
    arena::Arena,
    runtime::{ExecutionInfo, StackId},
    Container, Database, ElementDb, ElementId, Query, QueryHandle, QueryPath, Runtime,
};

use self::{lookup::HashLookup, state::FinishResult};

pub use self::state::SlotState;

pub struct QueryCache<Q: Query> {
    slots: Arena<Slot<Q>>,
    lookup: HashLookup,
    element: ElementId,
}

impl<Q: Query> Container for QueryCache<Q> {
    fn new(element: ElementId) -> Self {
        Self {
            element,
            lookup: HashLookup::default(),
            slots: Arena::with_capacity(1 << 32),
        }
    }

    fn element(&self) -> ElementId {
        self.element
    }
}

impl<Q: Query> QueryCache<Q> {
    pub(crate) fn get_or_execute<'a>(&'a self, db: &ElementDb<Q>, input: Q::Input) -> &'a Q::Output
    where
        Q::Input: Eq + Hash,
    {
        let stack = || db.runtime().current_stack();

        let lookup = self.lookup.get_or_allocate(input, &self.slots, stack);
        let slot = unsafe { self.slots.get_unchecked(lookup.id.index()) };

        let claim = if lookup.claim.is_some() {
            ClaimResult::Claimed
        } else {
            slot.claim_blocking(stack())
        };

        match claim {
            ClaimResult::Ready => {}
            ClaimResult::Claimed => unsafe {
                let path = self.path(lookup.id);
                db.runtime().execute::<Q>(db, path, slot)
            },
            ClaimResult::Pending(claimant) => {
                let path = self.path(lookup.id);
                db.runtime().block_until_ready(path, claimant, slot.state())
            }
        }

        unsafe { slot.output_unchecked() }
    }

    pub(crate) fn spawn<'a>(&'a self, db: &'a ElementDb<Q>, input: Q::Input) -> QueryHandle<'a, Q>
    where
        Q::Input: Eq + Hash,
    {
        let runtime = db.runtime();

        let stack = || runtime.allocate_stack();

        let lookup = self.lookup.get_or_allocate(input, &self.slots, stack);
        let slot = unsafe { self.slots.get_unchecked(lookup.id.index()) };

        let claim = if let Some(stack) = lookup.claim {
            Some(stack)
        } else {
            let stack = stack();
            match slot.claim_non_blocking(stack) {
                ClaimResult::Ready | ClaimResult::Pending(_) => None,
                ClaimResult::Claimed => Some(stack),
            }
        };

        let path = self.path(lookup.id);

        if let Some(stack) = claim {
            unsafe { runtime.spawn::<Q>(db, slot, path, stack) }
        }

        QueryHandle {
            path,
            slot,
            runtime,
        }
    }

    fn path(&self, slot: SlotId) -> QueryPath {
        QueryPath {
            element: self.element,
            slot,
        }
    }
}

pub(crate) struct Slot<Q: Query> {
    input: UnsafeCell<MaybeUninit<Q::Input>>,
    output: UnsafeCell<MaybeUninit<Q::Output>>,
    state: UnsafeCell<SlotState>,
}

unsafe impl<Q: Query> bytemuck::Zeroable for Slot<Q> {}

impl<Q: Query> Slot<Q> {
    pub(crate) unsafe fn input_unchecked(&self) -> &Q::Input {
        (*self.input.get()).assume_init_ref()
    }

    pub(crate) unsafe fn output_unchecked(&self) -> &Q::Output {
        (*self.output.get()).assume_init_ref()
    }

    /// Initialize the slot, claiming it simultaneously.
    /// Caller ensures that they have exclusive access to the slot and that it has never been
    /// initialized previously.
    unsafe fn init_claim(&self, input: Q::Input, current: StackId) {
        self.input.get().write(MaybeUninit::new(input));
        (*self.state.get()).init_claim(current)
    }

    pub(crate) unsafe fn write_output(
        &self,
        output: Q::Output,
        info: ExecutionInfo,
    ) -> FinishResult {
        self.output.get().write(MaybeUninit::new(output));
        self.state().finish()
    }

    pub(crate) fn state(&self) -> &SlotState {
        unsafe { &*self.state.get() }
    }

    fn claim_blocking(&self, stack: StackId) -> ClaimResult {
        self.state().claim(stack, true)
    }

    fn claim_non_blocking(&self, stack: StackId) -> ClaimResult {
        self.state().claim(stack, false)
    }

    pub(crate) fn wait_output(&self, path: QueryPath, runtime: &Runtime) -> &Q::Output {
        match self.claim_blocking(runtime.current_stack()) {
            ClaimResult::Ready => {}
            ClaimResult::Claimed => unreachable!(),
            ClaimResult::Pending(claimant) => {
                runtime.block_until_ready(path, claimant, self.state())
            }
        }
        unsafe { self.output_unchecked() }
    }
}

#[derive(Debug, Clone, Copy)]
enum ClaimResult {
    /// The output from the query is already available.
    Ready,
    /// Caller has exclusive access to the query and should execute it.
    Claimed,
    /// Another thread is currently executing the query
    Pending(StackId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SlotId(u32);

impl SlotId {
    fn index(&self) -> usize {
        self.0 as usize
    }
}
