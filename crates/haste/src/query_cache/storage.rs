mod cell;

use std::future::Future;

use crate::{
    arena::{AppendArena, RawArena},
    non_max::NonMaxU32,
    Dependency, Id, Query,
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
    /// Record the result of a new query
    pub unsafe fn finish(
        &self,
        id: Id,
        output: Q::Output,
        dependencies: &[Dependency],
    ) -> &OutputSlot<Q::Output> {
        let dependencies = {
            let range = self.dependencies.extend_from_slice(dependencies);
            let end = u32::try_from(range.end).unwrap();
            let start = range.start as u32;
            start..end
        };

        let slot = self.slots.get_unchecked(id.raw.get() as usize);
        slot.finish(OutputSlot {
            output,
            dependencies,
        })
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

    pub fn push_slot(&self, input: Q::Input) -> Id {
        let index = self.slots.push_zeroed();
        unsafe {
            self.slots.get_unchecked(index).cell.write_input(input);
        }
        Id::new(NonMaxU32::new(index as u32).expect("exhausted IDs"))
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
}

impl<Q: Query> QuerySlot<Q> {
    pub fn input(&self) -> &Q::Input {
        self.cell
            .get_input()
            .expect("attempted to read query input which has not been written")
    }

    pub fn output(&self) -> &OutputSlot<Q::Output> {
        self.cell
            .get_output()
            .expect("attempted to read query output which has not been written")
    }

    pub fn finish(&self, output: OutputSlot<Q::Output>) -> &OutputSlot<Q::Output> {
        self.cell.write_output(output)
    }

    /// Block on the query until it finishes
    pub fn wait_until_finished(
        &self,
    ) -> Result<&OutputSlot<Q::Output>, impl Future<Output = &OutputSlot<Q::Output>> + '_> {
        self.cell.wait_until_finished()
    }
}
