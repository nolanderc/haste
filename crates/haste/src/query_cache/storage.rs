mod cell;

use std::future::Future;

use crate::{
    arena::{AppendArena, RawArena},
    Cycle, Dependency, Id, Query, Revision,
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
        result: crate::ExecutionResult<Q::Output>,
    ) -> OutputSlot<Q::Output> {
        let dependencies = {
            let range = self.dependencies.extend_from_slice(&result.dependencies);
            let end = u32::try_from(range.end).unwrap();
            let start = range.start as u32;
            start..end
        };

        // TODO: compute the correct revisions
        OutputSlot {
            output: result.output,
            dependencies,
            verified_at: None,
            changed_at: None,
            max_input: None,
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

    pub fn allocate_slot(&self, input: Q::Input) -> (Id, &Q::Input) {
        let index = self.slots.push_zeroed();
        let slot = unsafe { self.slots.get_unchecked(index) };
        let input = match slot.cell.write_input(input) {
            Ok(input) | Err(input) => input,
        };
        let id = Id::try_from_usize(index).expect("exhausted IDs");
        (id, input)
    }

    pub fn init_slot(&self, id: Id, input: Q::Input) -> Result<&Q::Input, &Q::Input> {
        let index = id.raw.get() as usize;
        self.slots.get_or_allocate(index).cell.write_input(input)
    }
}

pub struct QuerySlot<Q: Query> {
    /// The result from executing the query.
    cell: QueryCell<Q::Input, OutputSlot<Q::Output>>,
}

unsafe impl<Q: Query> Sync for QuerySlot<Q> {}
unsafe impl<Q: Query> bytemuck::Zeroable for QuerySlot<Q> {}

pub struct OutputSlot<T> {
    /// Refers to a list of dependencies collected while executing this query.
    pub dependencies: std::ops::Range<u32>,

    /// The output from a query.
    pub output: T,

    pub verified_at: Option<Revision>,
    pub changed_at: Option<Revision>,
    pub max_input: Option<Revision>,
}

pub type WaitFuture<'a, Q: Query> = impl Future<Output = &'a OutputSlot<Q::Output>> + 'a;

impl<Q: Query> QuerySlot<Q> {
    pub fn input(&self) -> &Q::Input {
        self.cell
            .get_input()
            .expect("attempted to read query input which has not been written")
    }

    pub unsafe fn input_unchecked(&self) -> &Q::Input {
        self.cell.input_assume_init()
    }

    pub fn get_output(&self) -> Option<&OutputSlot<Q::Output>> {
        self.cell.get_output()
    }

    pub fn output(&self) -> &OutputSlot<Q::Output> {
        self.get_output()
            .expect("attempted to read query output which has not been written")
    }

    pub fn finish(&self, output: OutputSlot<Q::Output>) -> &OutputSlot<Q::Output> {
        self.cell.write_output(output)
    }

    /// Block on the query until it finishes
    pub fn wait_until_finished(&self) -> Result<&OutputSlot<Q::Output>, WaitFuture<'_, Q>> {
        self.cell.wait_until_finished()
    }

    pub fn set_cycle(&self, cycle: Cycle) -> Result<(), Cycle> {
        self.cell.set_cycle(cycle)
    }

    pub fn take_cycle(&self) -> Option<Cycle> {
        self.cell.take_cycle()
    }

    pub fn set_output(&mut self, output: OutputSlot<Q::Output>)
    where
        Q: crate::Input,
    {
        self.cell.set_output(output);
    }
}
