mod slot;

use std::{future::Future, hash::Hash, pin::Pin};

use hashbrown::raw::RawTable;

use crate::{
    arena::AppendArena, non_max::NonMaxU32, shard_map::ShardMap, Database, Dependency, Id,
    IngredientDatabase, IngredientPath, Query, QueryFuture, QueryTask,
};

use self::slot::{OutputSlot, QuerySlot};

pub enum EvalResult<Eval, Pending> {
    Cached(Id),
    Eval(Eval),
    Pending(Pending),
}

pub trait QueryCache: crate::Container {
    type Query: Query;

    type EvalTask<'a>: QueryTask + Send + 'a
    where
        Self: 'a;

    type PendingFuture<'a>: Future<Output = Id>
    where
        Self: 'a;

    /// Executes the query with the given input, returning an ID for accessing the result of the
    /// query.
    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        input: <Self::Query as Query>::Input,
    ) -> EvalResult<Self::EvalTask<'a>, Self::PendingFuture<'a>>;

    /// Get the output from the query.
    ///
    /// # Safety
    ///
    /// An `id` is only valid if the corresponding query has finished executing in the same
    /// revision.
    unsafe fn output(&self, id: Id) -> &<Self::Query as Query>::Output;

    /// Get the dependencies of a query.
    ///
    /// # Safety
    ///
    /// An `id` is only valid if the corresponding query has finished executing in the same
    /// revision.
    unsafe fn dependencies(&self, id: Id) -> &[Dependency];
}

pub struct HashQueryCache<Q: Query> {
    path: IngredientPath,
    entries: ShardMap<Id>,
    storage: QueryStorage<Q>,
}

struct QueryStorage<Q: Query> {
    /// Stores data about every query.
    slots: AppendArena<QuerySlot<Q>>,

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
    unsafe fn finish(
        &self,
        id: Id,
        output: Q::Output,
        dependencies: &[Dependency],
    ) -> Option<&OutputSlot<Q::Output>> {
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

    /// Get the dependencies of the given query
    #[allow(unused)]
    unsafe fn dependencies(&self, range: std::ops::Range<u32>) -> &[Dependency] {
        self.dependencies
            .get_slice_unchecked(range.start as usize..range.end as usize)
    }

    unsafe fn slot(&self, id: Id) -> &QuerySlot<Q> {
        self.slots.get_unchecked(id.raw.get() as usize)
    }
}

impl<Q: Query> crate::Container for HashQueryCache<Q> {
    fn new(path: IngredientPath) -> Self {
        Self {
            path,
            entries: Default::default(),
            storage: Default::default(),
        }
    }
}

impl<Q: Query> crate::DynContainer for HashQueryCache<Q> {
    fn path(&self) -> IngredientPath {
        self.path
    }
}

impl<Q: Query> QueryCache for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone + Sync,
{
    type Query = Q;

    type EvalTask<'a> = impl QueryTask + Send + 'a where Q: 'a;

    type PendingFuture<'a> = impl Future<Output = Id> + 'a where Q: 'a;

    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: <Q as Query>::Input,
    ) -> EvalResult<Self::EvalTask<'a>, Self::PendingFuture<'a>> {
        // only hash the input once:
        let hash = self.entries.hash(&input);
        let shard = self.entries.shard(hash);

        {
            // check if the query has already executed previously, and return that result
            let table = shard.read().unwrap();
            if let Some(result) = self.try_get_or_wait(&table, hash, &input) {
                return result;
            }
        }

        let id = {
            // Else we have to insert the slot ourselves.
            let mut table = shard.write().unwrap();

            // We also have to check for a race condition where another thread inserted its slot
            // while we were still waiting for the write lock.
            if let Some(result) = self.try_get_or_wait(&table, hash, &input) {
                return result;
            }

            // take ownership of the slot, by marking it as being in progress by us
            self.insert(&mut table, hash, &input, |input| self.entries.hash(input))
        };

        EvalResult::Eval(self.execute_query(db, id, input))
    }

    unsafe fn output(&self, id: Id) -> &<Self::Query as Query>::Output {
        &self.output(id).output
    }

    unsafe fn dependencies(&self, id: Id) -> &[Dependency] {
        let slot = self.output(id);
        self.storage.dependencies(slot.dependencies.clone())
    }
}

impl<Q: Query> HashQueryCache<Q> {
    /// # Safety
    ///
    /// The caller must ensure that the output slot associated with the given `id` has been
    /// initialized.
    unsafe fn output(&self, id: Id) -> &OutputSlot<Q::Output> {
        let slot = self.storage.slots.get_unchecked(id.raw.get() as usize);
        (*slot.output.get()).assume_init_ref()
    }

    fn try_get_or_wait<Eval>(
        &self,
        table: &RawTable<Id>,
        hash: u64,
        input: &<Q as Query>::Input,
    ) -> Option<EvalResult<Eval, impl Future<Output = Id> + '_>>
    where
        Q::Input: Eq,
    {
        let eq_fn = |key: &Id| {
            let slot = unsafe { self.storage.slot(*key) };
            slot.input == *input
        };

        let id = *table.get(hash, eq_fn)?;
        let slot = unsafe { self.storage.slot(id) };

        match slot.try_wait() {
            None => Some(EvalResult::Cached(id)),
            Some(fut) => Some(EvalResult::Pending(async move {
                fut.await;
                id
            })),
        }
    }

    fn insert(
        &self,
        table: &mut RawTable<Id>,
        hash: u64,
        input: &<Q as Query>::Input,
        hasher: impl Fn(&Q::Input) -> u64,
    ) -> Id
    where
        Q::Input: Clone,
    {
        let index = self.storage.slots.push(QuerySlot::new(input.clone()));
        let id = Id::new(NonMaxU32::new(index as u32).expect("exhausted IDs"));

        let hash_fn = |key: &Id| -> u64 {
            let slot = unsafe { self.storage.slot(*key) };
            hasher(&slot.input)
        };

        table.insert(hash, id, hash_fn);

        id
    }
}

impl<Q: Query> HashQueryCache<Q>
where
    Q::Input: Hash + Eq,
{
    fn execute_query<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        id: Id,
        input: Q::Input,
    ) -> HashQueryCacheTask<'a, Q> {
        let result = db.runtime().execute_query::<Q>(db, input);
        HashQueryCacheTask {
            cache: self,
            id,
            future: result,
        }
    }
}

pub struct HashQueryCacheTask<'a, Q: Query> {
    cache: &'a HashQueryCache<Q>,
    id: Id,
    future: QueryFuture<'a, Q>,
}

impl<Q: Query> QueryTask for HashQueryCacheTask<'_, Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn description(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Q>())
    }
}

impl<'a, Q: Query> Future for HashQueryCacheTask<'a, Q>
where
    Q::Input: Hash + Eq + Clone,
{
    type Output = Id;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: `result` points to `self`, which is `Pin`
        let future = unsafe { Pin::new_unchecked(&mut this.future) };
        let result = std::task::ready!(future.poll(cx));

        unsafe {
            this.cache
                .storage
                .finish(this.id, result.output, &result.dependencies);
        }

        std::task::Poll::Ready(this.id)
    }
}
