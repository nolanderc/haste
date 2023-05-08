mod lookup;
mod state;

use std::{cell::UnsafeCell, hash::Hash, mem::MaybeUninit};

use crate::{
    arena::Arena,
    revision::Revision,
    runtime::{Dependency, ExecutionInfo, StackId},
    Container, Database, Durability, ElementDb, ElementId, Input, Query, QueryHandle, QueryPath,
    Runtime,
};

use self::lookup::HashLookup;

pub use self::state::{FinishResult, SlotState};

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
    pub(crate) fn get_or_execute<'a>(
        &'a self,
        db: &ElementDb<Q>,
        args: Q::Arguments,
    ) -> &'a Q::Output
    where
        Q::Arguments: Eq + Hash,
    {
        let runtime = db.runtime();

        let lookup = self
            .lookup
            .get_or_allocate(args, &self.slots, || Some(runtime.current_stack()));

        let slot = unsafe { self.slots.get_unchecked(lookup.id.index()) };

        let claim = if lookup.claim.is_some() {
            ClaimResult::Claimed(None)
        } else {
            slot.claim_blocking(runtime.current_stack(), runtime.current_revision())
        };

        let path = self.path(lookup.id);

        match claim {
            ClaimResult::Ready => {}
            ClaimResult::Claimed(last_verified) => unsafe {
                runtime.execute::<Q>(db, path, slot, last_verified)
            },
            ClaimResult::Pending(claimant) => {
                runtime.block_until_ready(path, claimant, slot.state())
            }
        }

        runtime.register_dependency(Dependency {
            element: path.element,
            slot: path.slot,
            spawn_group: runtime.current_spawn_group(),
        });

        unsafe { &slot.output_unchecked().value }
    }

    pub(crate) fn spawn<'a>(
        &'a self,
        db: &'a ElementDb<Q>,
        args: Q::Arguments,
    ) -> QueryHandle<'a, Q>
    where
        Q::Arguments: Eq + Hash,
    {
        let runtime = db.runtime();

        let lookup = self
            .lookup
            .get_or_allocate(args, &self.slots, || Some(runtime.allocate_stack()));

        let slot = unsafe { self.slots.get_unchecked(lookup.id.index()) };

        let claim = if let Some(stack) = lookup.claim {
            Some((stack, None))
        } else {
            let stack = runtime.allocate_stack();
            match slot.claim_non_blocking(stack, runtime.current_revision()) {
                ClaimResult::Ready | ClaimResult::Pending(_) => None,
                ClaimResult::Claimed(last_verified) => Some((stack, last_verified)),
            }
        };

        let path = self.path(lookup.id);

        if let Some((stack, last_verified)) = claim {
            unsafe { runtime.spawn::<Q>(db, path, slot, last_verified, stack) }
        }

        QueryHandle {
            dependency: Dependency {
                element: path.element,
                slot: path.slot,
                spawn_group: runtime.current_spawn_group(),
            },
            slot,
            runtime,
        }
    }

    pub(crate) fn execute_input<'a>(
        &'a self,
        db: &'a ElementDb<Q>,
        args: Q::Arguments,
    ) -> (Q::Output, ExecutionInfo<'static>)
    where
        Q: Input,
        Q::Arguments: Hash + Eq,
    {
        assert!(Q::IS_INPUT);

        let runtime = db.runtime();

        let lookup = self.lookup.get_or_allocate(args, &self.slots, || None);
        let slot = self.slots.get_or_allocate(lookup.id.index());

        let path = self.path(lookup.id);
        unsafe {
            runtime.execute_with_info::<Q, _>(db, path, slot, |output, info| {
                let static_info = ExecutionInfo {
                    dependencies: &[],
                    ..info
                };
                (output, static_info)
            })
        }
    }

    pub(crate) fn set(
        &mut self,
        runtime: &mut Runtime,
        args: Q::Arguments,
        output: Q::Output,
        durability: Durability,
    ) where
        Q::Arguments: Hash + Eq,
    {
        let lookup = self.lookup.get_or_allocate(args, &self.slots, || None);

        let slot = self.slots.get_or_allocate_mut(lookup.id.index());

        if slot.state.get_mut().last_verified().is_some() {
            let previous = unsafe { slot.output.get_mut().assume_init_mut() };
            if previous.value == output && previous.durability == durability {
                return;
            }
            runtime.update_input(previous.durability);
            unsafe { slot.output.get_mut().assume_init_drop() }
        }

        *slot.output.get_mut() = MaybeUninit::new(OutputSlot {
            value: output,
            revision: runtime.current_revision(),
            durability,
            dependencies: [].into(),
        });
    }

    fn path(&self, slot: SlotId) -> QueryPath {
        QueryPath {
            element: self.element,
            slot,
        }
    }
}

pub(crate) struct Slot<Q: Query> {
    arguments: UnsafeCell<MaybeUninit<Q::Arguments>>,
    output: UnsafeCell<MaybeUninit<OutputSlot<Q>>>,
    state: UnsafeCell<SlotState>,
}

unsafe impl<Q: Query> bytemuck::Zeroable for Slot<Q> {}

impl<Q: Query> Slot<Q> {
    pub(crate) unsafe fn arguments_unchecked(&self) -> &Q::Arguments {
        (*self.arguments.get()).assume_init_ref()
    }

    pub(crate) unsafe fn output_unchecked(&self) -> &OutputSlot<Q> {
        (*self.output.get()).assume_init_ref()
    }

    /// Initialize the slot.
    /// Caller ensures that they have exclusive access to the slot and that it has never been
    /// initialized previously.
    unsafe fn init(&self, args: Q::Arguments) {
        self.arguments.get().write(MaybeUninit::new(args));
    }

    /// Initialize the slot, claiming it simultaneously.
    /// Caller ensures that they have exclusive access to the slot and that it has never been
    /// initialized previously.
    unsafe fn init_claim(&self, args: Q::Arguments, current: StackId) {
        self.arguments.get().write(MaybeUninit::new(args));
        (*self.state.get()).init_claim(current)
    }

    pub(crate) unsafe fn write_output(
        &self,
        value: Q::Output,
        info: ExecutionInfo,
        revision: Revision,
    ) -> FinishResult {
        self.output.get().write(MaybeUninit::new(OutputSlot {
            value,
            revision,
            durability: info.durability,
            dependencies: info.dependencies.into(),
        }));
        self.state().finish(revision)
    }

    pub(crate) unsafe fn backdate(&self, revision: Revision) -> FinishResult {
        self.state().finish(revision)
    }

    pub(crate) fn state(&self) -> &SlotState {
        unsafe { &*self.state.get() }
    }

    fn claim_blocking(&self, stack: StackId, revision: Revision) -> ClaimResult {
        self.state().claim(stack, revision, true)
    }

    fn claim_non_blocking(&self, stack: StackId, revision: Revision) -> ClaimResult {
        self.state().claim(stack, revision, false)
    }

    pub(crate) fn wait_output(&self, dependency: Dependency, runtime: &Runtime) -> &Q::Output {
        match self.claim_blocking(runtime.current_stack(), runtime.current_revision()) {
            ClaimResult::Ready => {}
            ClaimResult::Pending(claimant) => {
                runtime.block_until_ready(dependency.query(), claimant, self.state())
            }
            ClaimResult::Claimed(_) => unreachable!("slot should already be claimed"),
        }

        runtime.register_dependency(dependency);
        unsafe { &self.output_unchecked().value }
    }
}

pub(crate) struct OutputSlot<Q: Query> {
    pub(crate) value: Q::Output,
    pub(crate) revision: Revision,
    pub(crate) durability: Durability,
    #[allow(dead_code)]
    pub(crate) dependencies: Box<[Dependency]>,
}

#[derive(Debug, Clone, Copy)]
enum ClaimResult {
    /// The output from the query is already available.
    Ready,
    /// Caller has exclusive access to the query and should execute it. Contains the revision the
    /// query was last verified.
    Claimed(Option<Revision>),
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
