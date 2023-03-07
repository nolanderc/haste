mod cell;

use crate::{
    arena::{AppendArena, RawArena},
    revision::Revision,
    runtime::ExecutionResult,
    Cycle, Dependency, Durability, Id, Query, Runtime,
};

use std::future::Future;

use self::cell::QueryCell;

pub use self::cell::ChangeFuture;

pub type WaitFuture<'a, Q: Query> = impl Future<Output = &'a OutputSlot<Q>>;

pub struct QueryStorage<Q: Query> {
    /// Stores data about every query.
    slots: RawArena<QuerySlot<Q>>,

    /// Stores the dependencies for all the queries. These are referenced by ranges in the
    /// `OutputSlot`.
    dependencies: AppendArena<Dependency>,

    current_revision: Option<Revision>,
    last_revision: Option<Revision>,
}

impl<Q: Query> Default for QueryStorage<Q> {
    fn default() -> Self {
        Self {
            slots: Default::default(),
            dependencies: Default::default(),
            current_revision: None,
            last_revision: None,
        }
    }
}

impl<Q: Query> QueryStorage<Q> {
    pub fn set_current_revision(&mut self, revision: Option<Revision>) {
        if let Some(current) = self.current_revision {
            self.last_revision = Some(current);
        }

        match revision {
            None => self.current_revision = None,
            Some(new) => {
                assert!(
                    self.current_revision.is_none(),
                    "only one revision may be active at the same time"
                );
                assert!(
                    revision >= self.last_revision,
                    "the revision number must not decrease"
                );

                self.current_revision = Some(new);
            }
        }
    }

    pub fn current_revision(&self) -> Revision {
        self.current_revision.expect(concat!(
            "the database has not entered a revision",
            "\nhelp: call `haste::scope` to start a new revision"
        ))
    }

    /// Record the result of a new query.
    pub(crate) fn create_output(&self, result: ExecutionResult<Q::Output>) -> OutputSlot<Q> {
        let range = self.dependencies.extend_from_slice(&result.dependencies);
        let end = u32::try_from(range.end).unwrap();
        let start = range.start as u32;

        // TODO: compute the correct revisions
        OutputSlot {
            output: result.output,
            dependencies: DependencyRange::from(start..end),
            transitive: result.transitive,
        }
    }

    /// Get the dependencies of the given query.
    pub unsafe fn dependencies(&self, range: DependencyRange) -> &[Dependency] {
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
    pub dependencies: DependencyRange,

    /// Details about the transitive dependencies of the query. Used to optimize incremental
    /// re-evaluation of queries.
    pub transitive: TransitiveDependencies,

    /// The output from a query.
    pub output: Q::Output,
}

/// Refers to a list of dependencies in the query storage.
///
/// We use this over a `Vec` to batch the allocation and reduce the size of the query outputs.
#[derive(Debug, Clone, Copy)]
pub struct DependencyRange {
    pub start: u32,
    pub end: u32,
}

impl DependencyRange {
    pub(crate) fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

impl From<std::ops::Range<u32>> for DependencyRange {
    fn from(value: std::ops::Range<u32>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TransitiveDependencies {
    /// The query only depends on inputs from these revisions.
    pub inputs: Option<RevisionRange>,

    /// Durability of the inputs the query depends on.
    pub durability: Durability,
}

impl TransitiveDependencies {
    /// Used by queries which don't depend on any inputs (ie. they are constant).
    pub const CONSTANT: Self = Self {
        inputs: None,
        durability: Durability::CONSTANT,
    };

    pub fn combine(self, other: Self) -> Self {
        Self {
            inputs: RevisionRange::join(self.inputs, other.inputs),
            durability: std::cmp::min(self.durability, other.durability),
        }
    }

    pub fn extend(&mut self, other: Self) {
        *self = self.combine(other);
    }
}

#[derive(Clone, Copy)]
pub struct RevisionRange {
    pub earliest: Revision,
    pub latest: Revision,
}

impl std::fmt::Debug for RevisionRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}..={:?}", self.earliest, self.latest)
    }
}

impl RevisionRange {
    fn join(a: Option<Self>, b: Option<Self>) -> Option<Self> {
        match (a, b) {
            (None, _) => b,
            (_, None) => a,
            (Some(a), Some(b)) => Some(Self {
                earliest: std::cmp::min(a.earliest, b.earliest),
                latest: std::cmp::max(a.latest, b.latest),
            }),
        }
    }
}

impl std::ops::RangeBounds<Revision> for RevisionRange {
    fn start_bound(&self) -> std::ops::Bound<&Revision> {
        std::ops::Bound::Included(&self.earliest)
    }

    fn end_bound(&self) -> std::ops::Bound<&Revision> {
        std::ops::Bound::Included(&self.latest)
    }
}

impl<Q: Query> QuerySlot<Q> {
    pub fn input(&self) -> &Q::Input {
        self.cell
            .get_input()
            .expect("attempted to read query input which has not been written")
    }

    pub unsafe fn input_unchecked(&self) -> &Q::Input {
        self.cell.input_assume_init()
    }

    pub unsafe fn output_unchecked(&self) -> &OutputSlot<Q> {
        self.cell.output_assume_init()
    }

    pub fn get_output_mut(&mut self) -> Option<&mut OutputSlot<Q>> {
        self.cell.get_output_mut()
    }

    /// # Safety
    ///
    /// The slot must have an input value and the revision must be monotonically increasing.
    pub unsafe fn claim(
        &self,
        revision: Revision,
    ) -> Result<ClaimedSlot<'_, Q>, Option<&OutputSlot<Q>>> {
        self.cell.claim(revision)?;
        Ok(ClaimedSlot {
            slot: self,
            revision,
        })
    }

    /// Block on the query until it finishes
    ///
    /// # Safety
    ///
    /// Only the current revision of the database must be used.
    pub unsafe fn wait_until_verified(&self, current: Revision) -> WaitFuture<Q> {
        async move {
            self.cell.wait_until_verified(current).await;
            unsafe { self.cell.output_assume_init() }
        }
    }

    pub fn set_cycle(&self, cycle: Cycle) -> Result<(), Cycle> {
        self.cell.set_cycle(cycle)
    }

    pub fn set_output(&mut self, output: Q::Output, durability: Durability, runtime: &mut Runtime)
    where
        Q: crate::Input,
    {
        self.cell
            .set_output(runtime, durability, |current| OutputSlot {
                output,
                dependencies: (0..0).into(),
                transitive: TransitiveDependencies {
                    inputs: Some(RevisionRange {
                        earliest: current,
                        latest: current,
                    }),
                    durability,
                },
            });
    }

    pub fn last_verified(&self) -> Option<Revision> {
        self.cell.last_verified()
    }

    pub fn last_changed(&self) -> Option<Revision> {
        self.cell.last_changed()
    }

    pub fn set_verified(&mut self, current: Revision) {
        self.cell.set_verified(current)
    }

    pub fn wait_for_change(&self, revision: Revision) -> ChangeFuture<'_> {
        self.cell.wait_for_change(revision, |output| unsafe {
            std::ptr::addr_of!((*output).transitive)
        })
    }

    pub unsafe fn try_get(&self, current: Revision) -> Option<&OutputSlot<Q>> {
        self.cell.try_get_output(current)
    }
}

pub struct ClaimedSlot<'a, Q: Query> {
    slot: &'a QuerySlot<Q>,
    revision: Revision,
}

impl<Q: Query> Drop for ClaimedSlot<'_, Q> {
    fn drop(&mut self) {
        unsafe { self.slot.cell.release_claim() }
    }
}

impl<'a, Q: Query> ClaimedSlot<'a, Q> {
    pub fn current_revision(&self) -> Revision {
        self.revision
    }

    pub fn input(&self) -> &Q::Input {
        // SAFETY: the input slot must be initialized when calling [`QuerySlot::claim`]
        unsafe { self.slot.input_unchecked() }
    }

    pub fn take_cycle(&self) -> Option<Cycle> {
        self.slot.cell.take_cycle()
    }

    /// Write a new output for the given revision, releasing the claim.
    pub fn finish(self, output: OutputSlot<Q>) -> &'a OutputSlot<Q> {
        let output = unsafe { self.slot.cell.write_output(output, self.revision) };

        // don't release the claim twice:
        std::mem::forget(self);

        output
    }

    /// Signals that the previous output is still valid in the current revision.
    pub fn backdate(self) -> &'a OutputSlot<Q> {
        unsafe {
            // SAFETY: we have a claim on the query and use the same revision
            self.slot.cell.backdate(self.revision);

            // SAFETY: we managed to backdate the value, so the output is initialized.
            let output = self.slot.output_unchecked();

            // don't release the claim twice:
            std::mem::forget(self);

            output
        }
    }

    pub fn get_output(&mut self) -> Option<&mut OutputSlot<Q>> {
        // SAFETY: we have a claim on the query
        unsafe { self.slot.cell.get_output_claimed() }
    }

    pub fn last_verified(&self) -> Option<Revision> {
        self.slot.cell.last_verified()
    }
}
