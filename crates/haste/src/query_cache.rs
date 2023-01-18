use std::{future::Future, hash::Hash};

use parking_lot::RwLockUpgradableReadGuard;

use crate::{
    arena::AppendArena, shard_map::ShardMap, Database, Dependency, Id, IngredientDatabase,
    IngredientPath, Query,
};

pub trait QueryCache: crate::Container {
    type Query: Query;

    type Future<'a>: Future<Output = Id>
    where
        Self: 'a;

    /// Executes the query with the given input, returning an ID for accessing the result of the
    /// query.
    fn evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        input: <Self::Query as Query>::Input,
    ) -> Self::Future<'a>;

    /// Get the output from the query.
    ///
    /// # Safety
    ///
    /// The `id` must be one previously returned from `execute` in the same revision.
    unsafe fn get_output_untracked(&self, id: Id) -> &<Self::Query as Query>::Output;

    /// Get the dependencies of a query.
    ///
    /// # Safety
    ///
    /// The `id` must be one previously returned from `execute` in the same revision.
    unsafe fn get_dependencies_untracked(&self, id: Id) -> &[Dependency];

    /// Get the output from the query.
    ///
    /// # Safety
    ///
    /// The `id` must be one previously returned from `execute` in the same revision.
    unsafe fn get_output(
        &self,
        id: Id,
        runtime: &crate::Runtime,
    ) -> &<Self::Query as Query>::Output {
        runtime.register_dependency(Dependency {
            ingredient: self.path(),
            resource: id,
            extra: 0,
        });
        self.get_output_untracked(id)
    }
}

pub struct HashQueryCache<Q: Query> {
    path: IngredientPath,
    entries: ShardMap<Q::Input, InputSlot>,
    outputs: OutputStorage<Q::Output>,
}

struct OutputStorage<T> {
    /// Stores data about each completed query.
    slots: AppendArena<OutputSlot<T>>,

    /// Stores the dependencies for all the queries. These are referenced by ranges in the
    /// `OutputSlot`.
    dependencies: AppendArena<Dependency>,
}

impl<T> Default for OutputStorage<T> {
    fn default() -> Self {
        Self {
            slots: Default::default(),
            dependencies: Default::default(),
        }
    }
}

impl<T> OutputStorage<T> {
    /// Record the result of a new query
    fn push(&self, output: T, dependencies: &[Dependency]) -> usize {
        let dependencies = {
            let range = self.dependencies.extend_from_slice(dependencies);
            let end = u32::try_from(range.end).unwrap();
            let start = range.start as u32;
            start..end
        };

        self.slots.push(OutputSlot {
            output,
            dependencies,
        })
    }

    /// Get the dependencies of the given query
    #[allow(unused)]
    unsafe fn dependencies(&self, range: std::ops::Range<u32>) -> &[Dependency] {
        self.dependencies
            .get_slice_unchecked(range.start as usize..range.end as usize)
    }
}

enum InputSlot {
    /// The query associated with this specific input is currently is still progressing
    Progress(QueryProgress),
    /// The query has completed, and its result is associated with the given ID
    Done(Id),
}

struct QueryProgress {}

impl QueryProgress {
    fn new() -> Self {
        Self {}
    }
}

struct OutputSlot<T> {
    /// The output from a query.
    output: T,

    /// Refers to a sequence of dependencies in `OutputStorage::dependencies`.
    #[allow(unused)]
    dependencies: std::ops::Range<u32>,
}

impl<Q: Query> crate::Container for HashQueryCache<Q> {
    fn new(path: IngredientPath) -> Self {
        Self {
            path,
            entries: Default::default(),
            outputs: Default::default(),
        }
    }

    fn path(&self) -> IngredientPath {
        self.path
    }
}

impl<Q: Query> QueryCache for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    type Query = Q;

    type Future<'a> = impl Future<Output = Id> + 'a where Q: 'a;

    fn evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: <Q as Query>::Input,
    ) -> Self::Future<'a> {
        async move {
            // only hash the input once:
            let hash = self.entries.hash(&input);

            match self.get_or_reserve_slot(input, hash) {
                // the query has run before, so we reuse the cached output
                Ok(id) => id,
                // this is the first time we encounter this query, so execute it from scratch
                Err(input) => self.execute_query(db, input, hash).await,
            }
        }
    }

    unsafe fn get_output_untracked(&self, id: Id) -> &<Self::Query as Query>::Output {
        &self.output(id).output
    }

    unsafe fn get_dependencies_untracked(&self, id: Id) -> &[Dependency] {
        let slot = self.output(id);
        self.outputs.dependencies(slot.dependencies.clone())
    }
}

impl<Q: Query> HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn get_or_reserve_slot(&self, input: Q::Input, hash: u64) -> Result<Id, Q::Input> {
        let shard = self.entries.shard(hash);

        // check if the query has already executed previously, and return that result
        let table = shard.raw().upgradable_read();
        if let Some(entry) = table.get(hash, self.entries.eq_fn(&input)) {
            match &entry.value {
                InputSlot::Done(id) => return Ok(*id),
                InputSlot::Progress(_) => todo!("handle cycle"),
            }
        }

        // otherwise, we need to reserve a slot ourselves: take a write lock on the table
        let mut table = RwLockUpgradableReadGuard::upgrade(table);

        // avoid a race condition where the slot was reserved while we upgraded the lock
        if let Some(entry) = table.get(hash, self.entries.eq_fn(&input)) {
            match &entry.value {
                InputSlot::Done(id) => return Ok(*id),
                InputSlot::Progress(_) => todo!("handle cycle"),
            }
        }

        // take ownership of the slot, by marking it as being in progress by us
        let slot = InputSlot::Progress(QueryProgress::new());
        table.insert_entry(
            hash,
            crate::shard_map::Entry::new(input.clone(), slot),
            self.entries.hash_fn(),
        );

        Err(input)
    }

    async fn execute_query(&self, db: &IngredientDatabase<Q>, input: Q::Input, hash: u64) -> Id {
        let result = db.runtime().execute_query::<Q>(db, input.clone()).await;

        let index = self.outputs.push(result.output, &result.dependencies);

        // make the value available for other threads
        let mut shard = self.entries.shard(hash).raw().write();
        let entry = shard.get_mut(hash, self.entries.eq_fn(&input)).unwrap();

        let id = Id::try_from_usize(index).expect("exhausted query IDs");
        entry.value = InputSlot::Done(id);
        id
    }
}

impl<Q: Query> HashQueryCache<Q> {
    /// # Safety
    ///
    /// The caller must ensure that the output slot associated with the given `id` has been
    /// initialized.
    unsafe fn output(&self, id: Id) -> &OutputSlot<Q::Output> {
        self.outputs.slots.get_unchecked(id.raw.get() as usize)
    }
}
