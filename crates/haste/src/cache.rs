mod lookup;
mod state;

use std::{
    cell::UnsafeCell,
    hash::Hash,
    mem::MaybeUninit,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

use crate::{
    arena::Arena,
    runtime::{ExecutionInfo, StackId},
    Container, Database, ElementDb, ElementId, Query, QueryPath, Runtime,
};

use self::{lookup::HashLookup, state::FinishResult};

pub use self::state::SlotState;

pub struct QueryCache<Q: Query> {
    arena: SlotArena<Q>,
    lookup: HashLookup,
    element: ElementId,
}

impl<Q: Query> Container for QueryCache<Q> {
    fn new(element: ElementId) -> Self {
        Self {
            element,
            lookup: HashLookup::default(),
            arena: SlotArena {
                slots: Arena::with_capacity(1 << 32),
                ids: IdAllocator {
                    next: AtomicU64::new(0),
                },
            },
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

        let lookup = self.lookup.get_or_allocate(input, &self.arena, stack);
        let slot = unsafe { self.arena.slots.get_unchecked(lookup.id.index()) };

        let claim = if lookup.claim.is_some() {
            ClaimResult::Claimed
        } else {
            slot.claim_blocking(stack())
        };

        match claim {
            ClaimResult::Ready => {}
            ClaimResult::Claimed => unsafe {
                db.runtime().execute::<Q>(db, slot, self.path(lookup.id))
            },
            ClaimResult::Pending(claimant) => {
                db.runtime().block_until_ready(claimant, slot.state())
            }
        }

        unsafe { slot.output_unchecked() }
    }

    pub(crate) fn spawn<'a>(&'a self, db: &ElementDb<Q>, input: Q::Input) -> &'a Slot<Q>
    where
        Q::Input: Eq + Hash,
    {
        let stack = || db.runtime().allocate_stack();

        let lookup = self.lookup.get_or_allocate(input, &self.arena, stack);
        let slot = unsafe { self.arena.slots.get_unchecked(lookup.id.index()) };

        let claim = if let Some(stack) = lookup.claim {
            Some(stack)
        } else {
            let stack = stack();
            match slot.claim_non_blocking(stack) {
                ClaimResult::Ready | ClaimResult::Pending(_) => None,
                ClaimResult::Claimed => Some(stack),
            }
        };

        if let Some(stack) = claim {
            let path = self.path(lookup.id);
            unsafe { db.runtime().spawn::<Q>(db, slot, path, stack) }
        }

        slot
    }

    fn path(&self, slot: SlotId) -> QueryPath {
        QueryPath {
            element: self.element,
            slot,
        }
    }
}

struct SlotArena<Q: Query> {
    slots: Arena<Slot<Q>>,
    ids: IdAllocator,
}

impl<Q: Query> SlotArena<Q> {
    unsafe fn get_input_unchecked(&self, id: SlotId) -> &Q::Input {
        self.slots.get_unchecked(id.index()).input_unchecked()
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

    pub(crate) fn wait_output(&self, runtime: &Runtime) -> &Q::Output {
        match self.claim_blocking(runtime.current_stack()) {
            ClaimResult::Ready => {}
            ClaimResult::Claimed => unreachable!(),
            ClaimResult::Pending(claimant) => runtime.block_until_ready(claimant, self.state()),
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
    fn new(index: usize) -> Self {
        Self(index.try_into().expect("exhausted query slot IDs"))
    }

    fn index(&self) -> usize {
        self.0 as usize
    }
}

struct IdAllocator {
    next: AtomicU64,
}

impl IdAllocator {
    fn allocate(&self, count: u64) -> std::ops::Range<usize> {
        let start = self.next.fetch_add(count, Relaxed);
        let end = start + count;

        let max = 1 << 32;
        if end > max {
            self.next.store(max + 1, Relaxed);
            panic!("exhausted query slot IDs")
        }

        start as usize..end as usize
    }
}
