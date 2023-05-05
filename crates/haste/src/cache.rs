mod lookup;
mod state;

use std::{
    cell::UnsafeCell,
    hash::Hash,
    mem::MaybeUninit,
    sync::atomic::{AtomicU64, Ordering::Relaxed},
};

use crate::{arena::Arena, Container, Database, ElementDb, Query};

use self::{lookup::HashLookup, state::SlotState};

pub struct QueryCache<Q: Query> {
    lookup: HashLookup,
    arena: SlotArena<Q>,
}

impl<Q: Query> Container for QueryCache<Q> {}

impl<Q: Query> Default for QueryCache<Q> {
    fn default() -> Self {
        Self {
            lookup: HashLookup::default(),
            arena: SlotArena {
                slots: Arena::with_capacity(1 << 32),
                ids: IdAllocator {
                    next: AtomicU64::new(0),
                },
            },
        }
    }
}

impl<Q: Query> QueryCache<Q> {
    pub fn get_or_execute<'a>(&'a self, db: &ElementDb<Q>, input: Q::Input) -> &'a Q::Output
    where
        Q::Input: Eq + Hash,
    {
        let lookup = self.lookup.get_or_allocate(input, &self.arena);
        let slot = unsafe { self.arena.slots.get_unchecked(lookup.id.index()) };

        if lookup.claimed {
            // fast path if this is the first time encountering this query
            let input = unsafe { slot.input_unchecked() };
            let output = db.runtime().execute::<Q>(db, input.clone());
            return unsafe { slot.write_output(output) };
        }

        match slot.claim() {
            ClaimResult::Claimed => {
                let input = unsafe { slot.input_unchecked() };
                let output = db.runtime().execute::<Q>(db, input.clone());
                return unsafe { slot.write_output(output) };
            }
            ClaimResult::Ready => return unsafe { slot.output_unchecked() },
            ClaimResult::Pending => panic!("dependency cycle"),
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

pub struct Slot<Q: Query> {
    input: UnsafeCell<MaybeUninit<Q::Input>>,
    output: UnsafeCell<MaybeUninit<Q::Output>>,
    state: UnsafeCell<SlotState>,
}

unsafe impl<Q: Query> bytemuck::Zeroable for Slot<Q> {}

impl<Q: Query> Slot<Q> {
    unsafe fn input_unchecked(&self) -> &Q::Input {
        (*self.input.get()).assume_init_ref()
    }

    unsafe fn output_unchecked(&self) -> &Q::Output {
        (*self.output.get()).assume_init_ref()
    }

    /// Initialize the slot, claiming it simultaneously.
    /// Caller ensures that they have exclusive access to the slot and that it has never been
    /// initialized previously.
    unsafe fn init_claim(&self, input: Q::Input) {
        self.input.get().write(MaybeUninit::new(input));
        (*self.state.get()).init_claim()
    }

    unsafe fn write_output(&self, output: Q::Output) -> &Q::Output {
        let ptr = self.output.get();
        ptr.write(MaybeUninit::new(output));

        self.state().finish();

        (*ptr).assume_init_ref()
    }

    fn state(&self) -> &SlotState {
        unsafe { &*self.state.get() }
    }

    fn claim(&self) -> ClaimResult {
        self.state().claim()
    }
}

#[derive(Debug, Clone, Copy)]
enum ClaimResult {
    /// Caller has exclusive access to the query and should execute it.
    Claimed,
    /// The output from the query is already available.
    Ready,
    /// Another thread is currently executing the query
    Pending,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct SlotId(u32);

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
