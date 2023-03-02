mod cell;

use std::future::Future;

use crate::{
    arena::{AppendArena, RawArena},
    Cycle, Dependency, Id, Query, Revision, Runtime,
};

use self::cell::QueryCell;

pub struct QueryStorage<Q: Query> {
    /// Stores data about every query.
    slots: RawArena<QuerySlot<Q>>,

    /// Stores the dependencies for all the queries. These are referenced by ranges in the
    /// `OutputSlot`.
    dependencies: AppendArena<Dependency>,
}

impl<Q: Query> Default for QueryStorage<Q> {
    fn default() -> Self {
        Self {
            slots: Default::default(),
            dependencies: Default::default(),
        }
    }
}

impl<Q: Query> QueryStorage<Q> {
    /// Record the result of a new query.
    pub(crate) fn create_output(
        &self,
        output: Q::Output,
        dependencies: &[Dependency],
    ) -> OutputSlot<Q> {
        let dependencies = {
            let range = self.dependencies.extend_from_slice(dependencies);
            let end = u32::try_from(range.end).unwrap();
            let start = range.start as u32;
            start..end
        };

        // TODO: compute the correct revisions
        OutputSlot {
            output,
            dependencies,
        }
    }

    /// Get the dependencies of the given query.
    pub unsafe fn dependencies(&self, range: std::ops::Range<u32>) -> &[Dependency] {
        self.dependencies
            .get_slice_unchecked(range.start as usize..range.end as usize)
    }

    pub fn slot(&self, id: Id) -> &QuerySlot<Q> {
        self.slots
            .get(id.raw.get() as usize)
            .expect("attempted to get query slot which does not exist")
    }

    pub unsafe fn get_slot_unchecked(&self, id: Id) -> &QuerySlot<Q> {
        self.slots.get_unchecked(id.raw.get() as usize)
    }

    pub(crate) fn slot_mut(&mut self, id: Id) -> &mut QuerySlot<Q> {
        self.slots
            .get_mut(id.raw.get() as usize)
            .expect("attempted to get query slot which does not exist")
    }

    pub fn allocate_slot(&self, input: Q::Input) -> (Id, &QuerySlot<Q>) {
        let index = self.slots.push_zeroed();
        let slot = unsafe { self.slots.get_unchecked(index) };
        slot.cell.write_input(input);
        let id = Id::try_from_usize(index).expect("exhausted IDs");
        (id, slot)
    }

    pub fn init_slot(&self, id: Id, input: Q::Input) -> &QuerySlot<Q> {
        let index = id.raw.get() as usize;
        let slot = self.slots.get_or_allocate(index);
        slot.cell.write_input(input);
        slot
    }
}

pub struct QuerySlot<Q: Query> {
    /// The result from executing the query.
    cell: QueryCell<Q::Input, OutputSlot<Q>>,
}

unsafe impl<Q: Query> Sync for QuerySlot<Q> {}
unsafe impl<Q: Query> bytemuck::Zeroable for QuerySlot<Q> {}

pub struct OutputSlot<Q: Query> {
    /// Refers to a list of dependencies collected while executing this query.
    pub dependencies: std::ops::Range<u32>,

    /// The output from a query.
    pub output: Q::Output,
}

pub type WaitFuture<'a, Q: Query> = impl Future<Output = &'a OutputSlot<Q>> + 'a;

impl<Q: Query> QuerySlot<Q> {
    pub fn input(&self) -> &Q::Input {
        self.cell
            .get_input()
            .expect("attempted to read query input which has not been written")
    }

    pub unsafe fn input_unchecked(&self) -> &Q::Input {
        self.cell.input_assume_init()
    }

    /// # Safety
    ///
    /// The output must be valid in the current revision, or the caller has exclusive access.
    pub unsafe fn get_output(&self) -> Option<&OutputSlot<Q>> {
        self.cell.get_output()
    }

    pub fn get_output_mut(&mut self) -> Option<&mut OutputSlot<Q>> {
        self.cell.get_output_mut()
    }

    /// Write a new output for the given revision, making it accessible to other threads
    ///
    /// # Safety
    ///
    /// The output value must *not* have been written and no other thread must read/write to the output.
    pub unsafe fn finish(&self, output: OutputSlot<Q>, revision: Revision) -> &OutputSlot<Q> {
        self.cell.write_output(output, revision)
    }

    /// Verify the slot for the given revision, making it accessible to other threads
    ///
    /// # Safety
    ///
    /// The output value must have been written and no other thread may write to the output.
    pub unsafe fn backdate(&self, current: Revision) {
        self.cell.backdate(current);
    }

    pub fn try_reserve_for_execution(&self, runtime: &Runtime) -> bool {
        self.cell.reserve(runtime.current_revision())
    }

    /// Block on the query until it finishes
    pub fn wait_until_verified(&self, runtime: &Runtime) -> WaitFuture<'_, Q> {
        self.cell.wait_until_verified(runtime.current_revision())
    }

    pub fn set_cycle(&self, cycle: Cycle) -> Result<(), Cycle> {
        self.cell.set_cycle(cycle)
    }

    pub fn take_cycle(&self) -> Option<Cycle> {
        self.cell.take_cycle()
    }

    pub fn set_output(&mut self, output: Q::Output, runtime: &mut Runtime)
    where
        Q: crate::Input,
    {
        self.cell.set_output(
            OutputSlot {
                output,
                dependencies: 0..0,
            },
            runtime,
        );
    }

    pub fn last_verified(&self) -> Option<Revision> {
        self.cell.last_verified()
    }

    pub fn last_changed(&self) -> Option<Revision> {
        self.cell.last_changed()
    }
}
