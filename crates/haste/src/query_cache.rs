use std::{future::Future, hash::Hash, pin::Pin};

use parking_lot::RwLockUpgradableReadGuard;

use crate::{
    arena::AppendArena, shard_map::ShardMap, Database, Dependency, ExecutionResult, Id,
    IngredientDatabase, IngredientPath, Query, QueryFuture, QueryTask,
};

pub trait QueryCache: crate::Container {
    type Query: Query;

    type EvalTask<'a>: QueryTask
    where
        Self: 'a;

    /// Executes the query with the given input, returning an ID for accessing the result of the
    /// query.
    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        input: <Self::Query as Query>::Input,
    ) -> Result<Id, Self::EvalTask<'a>>;

    /// Get the output from the query.
    ///
    /// # Safety
    ///
    /// The `id` must be one previously returned from `execute` in the same revision.
    unsafe fn output(&self, id: Id) -> &<Self::Query as Query>::Output;

    /// Get the dependencies of a query.
    ///
    /// # Safety
    ///
    /// The `id` must be one previously returned from `execute` in the same revision.
    unsafe fn dependencies(&self, id: Id) -> &[Dependency];
}

pub struct HashQueryCache<Q: Query> {
    path: IngredientPath,
    entries: ShardMap<Q::Input, InputSlot>,
    outputs: OutputStorage<Q::Output>,
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
    Q::Input: Hash + Eq + Clone + Unpin,
{
    type Query = Q;

    type EvalTask<'a> = impl QueryTask + 'a where Q: 'a;

    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: <Q as Query>::Input,
    ) -> Result<Id, Self::EvalTask<'a>> {
        self.get_or_reserve_slot(db, input)
    }

    unsafe fn output(&self, id: Id) -> &<Self::Query as Query>::Output {
        &self.output(id).output
    }

    unsafe fn dependencies(&self, id: Id) -> &[Dependency] {
        let slot = self.output(id);
        self.outputs.dependencies(slot.dependencies.clone())
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

impl<Q: Query> HashQueryCache<Q>
where
    Q::Input: Hash + Eq,
{
    /// If the query has run before: returns the output slot ID. Otherwise it returns a future
    /// which must be polled in order to finilize the query.
    fn get_or_reserve_slot<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: Q::Input,
    ) -> Result<Id, impl QueryTask + 'a>
    where
        Q::Input: Clone + Unpin,
    {
        // only hash the input once:
        let hash = self.entries.hash(&input);
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

        Err(self.execute_query(db, input, hash))
    }

    fn execute_query<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: Q::Input,
        hash: u64,
    ) -> impl QueryTask + 'a
    where
        Q::Input: Clone + Unpin,
    {
        let result = db.runtime().execute_query::<Q>(db, input.clone());
        HashQueryCacheTask {
            cache: self,
            input: Some(input),
            input_hash: hash,
            result,
        }
    }

    fn insert(&self, input: Q::Input, hash: u64, result: ExecutionResult<Q::Output>) -> Id {
        let index = self.outputs.push(result.output, &result.dependencies);

        // make the value available for other threads
        let mut shard = self.entries.shard(hash).raw().write();
        let entry = shard.get_mut(hash, self.entries.eq_fn(&input)).unwrap();

        let id = Id::try_from_usize(index).expect("exhausted query IDs");
        entry.value = InputSlot::Done(id);
        id
    }
}

struct HashQueryCacheTask<'a, Q: Query> {
    cache: &'a HashQueryCache<Q>,
    input: Option<Q::Input>,
    input_hash: u64,
    result: QueryFuture<'a, Q>,
}

impl<Q: Query> QueryTask for HashQueryCacheTask<'_, Q>
where
    Q::Input: Hash + Eq + Clone + Unpin,
{
    fn description(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Q>())
    }
}

impl<'a, Q: Query> Future for HashQueryCacheTask<'a, Q>
where
    Q::Input: Hash + Eq + Clone + Unpin,
{
    type Output = Id;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: `result` points to `self`, which is `Pin`
        let result = unsafe { Pin::new_unchecked(&mut this.result) };
        let output = std::task::ready!(result.poll(cx));

        // SAFETY: we can move out of `input` because it is `Unpin`
        let input = this.input.take().unwrap();

        let id = this.cache.insert(input, this.input_hash, output);

        std::task::Poll::Ready(id)
    }
}
