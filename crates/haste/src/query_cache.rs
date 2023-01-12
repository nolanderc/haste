use std::hash::Hash;

use parking_lot::RwLockUpgradableReadGuard;

use crate::{
    arena::AppendArena, shard_map::ShardMap, Database, Dependency, Id, IngredientDatabase,
    IngredientId, Query,
};

pub trait QueryCache<Q: Query> {
    fn get_or_execute<'a>(&'a self, db: &IngredientDatabase<Q>, input: Q::Input) -> &'a Q::Output;
}

pub struct HashQueryCache<Q: Query> {
    id: IngredientId,
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
    fn new(id: IngredientId) -> Self {
        Self {
            id,
            entries: Default::default(),
            outputs: Default::default(),
        }
    }

    fn id(&self) -> IngredientId {
        self.id
    }
}

impl<Q: Query> QueryCache<Q> for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn get_or_execute<'a>(
        &'a self,
        db: &IngredientDatabase<Q>,
        input: <Q as Query>::Input,
    ) -> &'a <Q as Query>::Output {
        let runtime = db.runtime();

        // only hash the input once:
        let hash = self.entries.hash(&input);

        let id = match self.get_or_reserve_slot(input, hash) {
            // the query has run before, so we reuse the cached output
            Ok(id) => id,
            // this is the first time we encounter this query, so execute it from scratch
            Err(input) => self.execute_query(db, input, hash),
        };

        runtime.register_dependency(Dependency {
            ingredient: self.id,
            resource: id,
            extra: 0,
        });

        unsafe { &self.output(id).output }
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

    fn execute_query(&self, db: &IngredientDatabase<Q>, input: Q::Input, hash: u64) -> Id {
        let result = db.runtime().execute_query::<Q>(db, input.clone());

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
