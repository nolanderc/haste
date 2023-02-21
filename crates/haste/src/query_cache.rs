mod lookup;
mod storage;

use std::{future::Future, pin::Pin};

use futures_lite::FutureExt;

use crate::{
    Container, ContainerPath, Cycle, CycleStrategy, Database, Dependency, DynContainer, Id,
    IngredientDatabase, IngredientPath, Query, QueryFuture, QueryTask,
};

use self::storage::{QuerySlot, QueryStorage, WaitFuture};

pub use self::lookup::*;

pub trait QueryCache: DynQueryCache + Container {
    type Query: Query;

    /// Executes the query with the given input, returning an ID for accessing the result of the
    /// query.
    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        input: <Self::Query as Query>::Input,
    ) -> EvalResult<'a, Self::Query>;

    /// Get the result of a query. If the query is currently being evaluated returns `Err` with a
    /// future that is ready when the query has been evaluated.
    ///
    /// # Panics
    ///
    /// If the `id` is not valid.
    fn get<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        id: Id,
    ) -> Result<QueryResult<'a, Self::Query>, PendingFuture<'a, Self::Query>>;
}

pub trait DynQueryCache: DynContainer {
    /// Get the dependencies of a query.
    ///
    /// # Panics
    ///
    /// If the `id` is not valid.
    fn dependencies(&self, id: Id) -> &[Dependency];

    /// Get the cycle recovery stategy used by the query
    fn cycle_strategy(&self) -> CycleStrategy;

    /// Signals that the specific query is part of a cycle.
    ///
    /// Returns `Err` if the query is already recovering from a cycle.
    fn set_cycle(&self, id: Id, cycle: Cycle) -> Result<(), Cycle>;
}

/// A query cache which uses the hash of the input as a key.
pub type HashQueryCache<Q> = QueryCache2<Q, HashStrategy>;

pub struct QueryCache2<Q: Query, Lookup> {
    path: ContainerPath,
    lookup: Lookup,
    storage: QueryStorage<Q>,
}

impl<Q: Query, Lookup> crate::Container for QueryCache2<Q, Lookup>
where
    Lookup: Default + 'static,
{
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            lookup: Lookup::default(),
            storage: QueryStorage::default(),
        }
    }
}

impl<Q: Query, Lookup> crate::DynContainer for QueryCache2<Q, Lookup>
where
    Lookup: 'static,
{
    fn path(&self) -> ContainerPath {
        self.path
    }

    fn fmt(&self, id: Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let slot = self.storage.slot(id);
        Q::fmt(slot.input(), f)
    }

    fn as_query_cache(&self) -> Option<&dyn DynQueryCache> {
        Some(self)
    }
}

impl<Q: Query, Lookup> QueryCache for QueryCache2<Q, Lookup>
where
    Lookup: LookupStrategy<Q> + Default + 'static,
    Q::Input: Clone,
{
    type Query = Q;

    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        input: <Self::Query as Query>::Input,
    ) -> EvalResult<'a, Q> {
        match self.lookup.try_insert(input, &self.storage) {
            Err(id) => {
                let slot = self.storage.slot(id);
                return match try_get(self.ingredient(id), slot, db) {
                    Ok(cached) => EvalResult::Cached(cached),
                    Err(pending) => EvalResult::Pending(pending),
                };
            }
            Ok((id, input)) => EvalResult::Eval(self.execute_query(db, id, input.clone())),
        }
    }

    fn get<'a>(
        &'a self,
        db: &'a IngredientDatabase<Self::Query>,
        id: Id,
    ) -> Result<QueryResult<'a, Self::Query>, PendingFuture<'a, Q>> {
        let slot = self.storage.slot(id);
        try_get(self.ingredient(id), slot, db)
    }
}

impl<Q: Query, Lookup> DynQueryCache for QueryCache2<Q, Lookup>
where
    Lookup: 'static,
{
    fn dependencies(&self, id: Id) -> &[Dependency] {
        let range = self.storage.slot(id).output().dependencies.clone();
        unsafe { self.storage.dependencies(range) }
    }

    fn cycle_strategy(&self) -> CycleStrategy {
        Q::CYCLE_STRATEGY
    }

    fn set_cycle(&self, id: Id, cycle: Cycle) -> Result<(), Cycle> {
        self.storage.slot(id).set_cycle(cycle)
    }
}

pub type QueryResult<'a, Q> = (Id, &'a <Q as Query>::Output);

pub enum EvalResult<'a, Q: Query> {
    Cached(QueryResult<'a, Q>),
    Pending(PendingFuture<'a, Q>),
    Eval(QueryCacheTask<'a, Q>),
}

fn try_get<'a, Q: Query>(
    path: IngredientPath,
    slot: &'a QuerySlot<Q>,
    db: &'a IngredientDatabase<Q>,
) -> Result<QueryResult<'a, Q>, PendingFuture<'a, Q>> {
    match slot.wait_until_finished() {
        Ok(slot) => Ok((path.resource, &slot.output)),
        Err(fut) => Err(PendingFuture {
            db,
            path,
            fut,
            blocks: None,
        }),
    }
}

pub struct PendingFuture<'a, Q: Query> {
    db: &'a IngredientDatabase<Q>,
    path: IngredientPath,
    blocks: Option<IngredientPath>,
    fut: WaitFuture<'a, Q>,
}

impl<'a, Q: Query> Drop for PendingFuture<'a, Q> {
    fn drop(&mut self) {
        if let Some(parent) = self.blocks {
            self.db.runtime().unblock(parent);
        }
    }
}

impl<'a, Q: Query> Future for PendingFuture<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(
        mut self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        use std::task::Poll;
        let result = self.fut.poll(cx);

        match (&result, self.blocks) {
            (Poll::Pending, None) => {
                let db = self.db.as_dyn();
                let runtime = self.db.runtime();
                if let Some(parent) = runtime.current_query() {
                    self.blocks = Some(parent);
                    runtime.would_block_on(parent, self.path, cx.waker(), db);
                }
            }
            (Poll::Ready(_), Some(parent)) => {
                let runtime = self.db.runtime();
                runtime.unblock(parent);
                self.blocks = None;
            }
            _ => {}
        }

        result.map(|slot| (self.path.resource, &slot.output))
    }
}

impl<Q: Query, Lookup> QueryCache2<Q, Lookup> {
    fn execute_query<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        id: Id,
        input: Q::Input,
    ) -> QueryCacheTask<'a, Q> {
        let this = self.ingredient(id);
        let future = db.runtime().execute_query(db, input, this);
        QueryCacheTask {
            this,
            storage: &self.storage,
            future,
        }
    }

    fn ingredient(&self, id: Id) -> IngredientPath {
        IngredientPath {
            container: self.path,
            resource: id,
        }
    }
}

pub struct QueryCacheTask<'a, Q: Query> {
    this: IngredientPath,
    storage: &'a QueryStorage<Q>,
    future: QueryFuture<'a, Q>,
}

impl<'a, Q: Query> QueryCacheTask<'a, Q> {
    fn poll_advanced(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<(Id, &'a Q::Output)>
    where
        Q::Input: Clone,
    {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };
        let id = this.this.resource;

        let slot = unsafe { this.storage.get_slot_unchecked(id) };

        // SAFETY: `this` is an alias for `self` which is pinned.
        let mut future = unsafe { Pin::new_unchecked(&mut this.future) };

        if let Some(cycle) = slot.take_cycle() {
            future.as_mut().recover(cycle, slot.input());
        }

        let result = std::task::ready!(future.poll(cx));

        let output = this.storage.create_output(result);
        let output_slot = slot.finish(output);

        std::task::Poll::Ready((id, &output_slot.output))
    }
}

impl<Q: Query> QueryTask for QueryCacheTask<'_, Q>
where
    Q::Input: Clone,
{
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<()> {
        self.poll_advanced(cx).map(|_| ())
    }

    fn path(&self) -> IngredientPath {
        self.this
    }
}

impl<'a, Q: Query> Future for QueryCacheTask<'a, Q>
where
    Q::Input: Clone,
{
    type Output = (Id, &'a Q::Output);

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        self.poll_advanced(cx)
    }
}
