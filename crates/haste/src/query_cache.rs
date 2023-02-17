mod storage;

use std::{future::Future, hash::Hash, pin::Pin};

use futures_lite::FutureExt;
use hashbrown::raw::RawTable;

use crate::{
    shard_map::ShardMap, ContainerPath, CycleStrategy, Database, Dependency, DynContainer, Id,
    IngredientDatabase, IngredientPath, Query, QueryFuture, QueryTask,
};

use self::storage::{OutputSlot, QueryStorage};

pub trait QueryCache: crate::Container + DynQueryCache {
    type Query: Query;

    type EvalTask<'a>: QueryTask + Future<Output = QueryResult<'a, Self::Query>> + Send + 'a
    where
        Self: 'a;

    type PendingFuture<'a>: Future<Output = QueryResult<'a, Self::Query>>
    where
        Self: 'a;

    /// Executes the query with the given input, returning an ID for accessing the result of the
    /// query.
    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        input: <Self::Query as Query>::Input,
    ) -> CacheEvalResult<'a, Self>;

    /// Get the output from the query.
    ///
    /// # Safety
    ///
    /// An `id` is only valid if the corresponding query has finished executing in the same
    /// revision.
    fn output(&self, id: Id) -> &<Self::Query as Query>::Output;
}

pub trait DynQueryCache: DynContainer {
    /// Get the dependencies of a query.
    ///
    /// # Safety
    ///
    /// An `id` is only valid if the corresponding query has finished executing in the same
    /// revision.
    fn dependencies(&self, id: Id) -> &[Dependency];

    /// Get the cycle recovery stategy used by the query
    fn cycle_strategy(&self) -> CycleStrategy;
}

pub type QueryResult<'a, Q> = (Id, &'a <Q as Query>::Output);

pub enum EvalResult<Result, Eval, Pending> {
    Cached(Result),
    Eval(Eval),
    Pending(Pending),
}

pub type CacheEvalResult<'a, Cache> = EvalResult<
    QueryResult<'a, <Cache as QueryCache>::Query>,
    <Cache as QueryCache>::EvalTask<'a>,
    <Cache as QueryCache>::PendingFuture<'a>,
>;

pub struct HashQueryCache<Q: Query> {
    path: ContainerPath,
    entries: ShardMap<Id>,
    storage: QueryStorage<Q>,
}

impl<Q: Query> crate::Container for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            entries: Default::default(),
            storage: Default::default(),
        }
    }
}

impl<Q: Query> crate::DynContainer for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn path(&self) -> ContainerPath {
        self.path
    }

    fn fmt(&self, path: IngredientPath, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        assert_eq!(path.container, self.path);
        let slot = self.storage.slot(path.resource);
        Q::fmt(slot.input(), f)
    }

    fn as_query_cache(&self) -> Option<&dyn DynQueryCache> {
        Some(self)
    }
}

impl<Q: Query> QueryCache for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    type Query = Q;

    type EvalTask<'a> = impl QueryTask + Future<Output = QueryResult<'a, Q>> + Send + 'a where Q: 'a;

    type PendingFuture<'a> = impl Future<Output = QueryResult<'a, Q>> + 'a where Q: 'a;

    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: Q::Input,
    ) -> CacheEvalResult<'a, Self> {
        // only hash the input once:
        let hash = self.entries.hash(&input);
        let shard = self.entries.shard(hash);

        {
            // check if the query has already executed previously, and return that result
            let table = shard.read().unwrap();
            if let Some(result) = self.try_get_or_wait(&table, hash, &input, db) {
                return result;
            }
        }

        // Else we have to insert the slot ourselves.
        let mut table = shard.write().unwrap();

        // We also have to check for a race condition where another thread inserted its slot
        // while we were still waiting for the write lock.
        if let Some(result) = self.try_get_or_wait(&table, hash, &input, db) {
            return result;
        }

        // take ownership of the slot, by marking it as being in progress by us
        let id = self.storage.push_slot(input.clone());
        table.insert(hash, id, |key| {
            // SAFETY: all IDs in the cache are valid
            let slot = unsafe { self.storage.get_slot_unchecked(*key) };
            self.entries.hash(slot.input())
        });

        drop(table);

        EvalResult::Eval(self.execute_query(db, id, input))
    }

    fn output(&self, id: Id) -> &Q::Output {
        &self.output_slot(id).output
    }
}

impl<Q: Query> DynQueryCache for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn dependencies(&self, id: Id) -> &[Dependency] {
        let slot = self.output_slot(id);
        unsafe { self.storage.dependencies(slot.dependencies.clone()) }
    }

    fn cycle_strategy(&self) -> CycleStrategy {
        Q::CYCLE_STRATEGY
    }
}

impl<Q: Query> HashQueryCache<Q> {
    fn output_slot(&self, id: Id) -> &OutputSlot<Q::Output> {
        self.storage.slot(id).output()
    }

    fn try_get_or_wait<'a, Eval>(
        &'a self,
        table: &RawTable<Id>,
        hash: u64,
        input: &Q::Input,
        db: &'a IngredientDatabase<Q>,
    ) -> Option<EvalResult<QueryResult<'a, Q>, Eval, impl Future<Output = QueryResult<'a, Q>> + 'a>>
    where
        Q::Input: Clone + Hash + Eq,
    {
        let eq_fn = |key: &Id| {
            // SAFETY: all IDs in the cache are valid
            let slot = unsafe { self.storage.get_slot_unchecked(*key) };
            slot.input() == input
        };

        let id = *table.get(hash, eq_fn)?;
        let slot = unsafe { self.storage.get_slot_unchecked(id) };

        match slot.wait_until_finished() {
            Ok(slot) => Some(EvalResult::Cached((id, &slot.output))),
            Err(mut fut) => Some(EvalResult::Pending({
                let query_path = IngredientPath {
                    container: self.path,
                    resource: id,
                };
                let mut is_blocked = false;
                std::future::poll_fn(move |cx| {
                    let result = fut.poll(cx);

                    if result.is_pending() && !is_blocked {
                        let db = db.as_dyn();
                        if let Some(cycle) = db.runtime().would_block_on(query_path, db) {
                            panic!("dependency cycle: {:#}", cycle.fmt(db))
                        }
                        is_blocked = true;
                    }
                    if result.is_ready() && is_blocked {
                        db.runtime().unblock(query_path, db.as_dyn());
                        is_blocked = false;
                    }

                    result.map(|slot| (id, &slot.output))
                })
            })),
        }
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
        let this = IngredientPath {
            container: self.path,
            resource: id,
        };
        let result = db.runtime().execute_query::<Q>(db, input, this);
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

impl<'a, Q: Query> HashQueryCacheTask<'a, Q> {
    fn poll_advanced(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<(Id, &'a Q::Output)> {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: `result` points to `self`, which is `Pin`
        let future = unsafe { Pin::new_unchecked(&mut this.future) };
        let result = std::task::ready!(future.poll(cx));

        let slot = unsafe {
            this.cache
                .storage
                .finish(this.id, result.output, &result.dependencies)
        };

        std::task::Poll::Ready((this.id, &slot.output))
    }
}

impl<Q: Query> QueryTask for HashQueryCacheTask<'_, Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<()> {
        self.poll_advanced(cx).map(|_| ())
    }

    fn container(&self) -> &dyn DynQueryCache {
        self.cache
    }

    fn path(&self) -> IngredientPath {
        IngredientPath {
            container: self.cache.path,
            resource: self.id,
        }
    }
}

impl<'a, Q: Query> Future for HashQueryCacheTask<'a, Q>
where
    Q::Input: Hash + Eq + Clone,
{
    type Output = (Id, &'a Q::Output);

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        self.poll_advanced(cx)
    }
}
