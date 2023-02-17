mod lookup;
mod storage;

use std::{future::Future, pin::Pin};

use futures_lite::FutureExt;

use crate::{
    Container, ContainerPath, CycleStrategy, Database, Dependency, DynContainer, Id,
    IngredientDatabase, IngredientPath, Query, QueryFuture, QueryTask,
};

use self::storage::{QuerySlot, QueryStorage};

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
                return match try_get(self.path, id, slot, db) {
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
        try_get(self.path, id, slot, db)
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
}

pub type QueryResult<'a, Q> = (Id, &'a <Q as Query>::Output);

pub enum EvalResult<'a, Q: Query> {
    Cached(QueryResult<'a, Q>),
    Pending(PendingFuture<'a, Q>),
    Eval(QueryCacheTask<'a, Q>),
}

pub type PendingFuture<'a, Q: Query> = impl Future<Output = QueryResult<'a, Q>> + 'a;

fn try_get<'a, Q: Query>(
    container: ContainerPath,
    id: Id,
    slot: &'a QuerySlot<Q>,
    db: &'a IngredientDatabase<Q>,
) -> Result<QueryResult<'a, Q>, PendingFuture<'a, Q>> {
    match slot.wait_until_finished() {
        Ok(slot) => Ok((id, &slot.output)),
        Err(mut fut) => Err({
            let query_path = IngredientPath {
                container,
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
        }),
    }
}

impl<Q: Query, Lookup> QueryCache2<Q, Lookup> {
    fn execute_query<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        id: Id,
        input: Q::Input,
    ) -> QueryCacheTask<'a, Q> {
        let this = IngredientPath {
            container: self.path,
            resource: id,
        };
        let future = db.runtime().execute_query(db, input, this);
        QueryCacheTask {
            this,
            storage: &self.storage,
            future,
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
    ) -> std::task::Poll<(Id, &'a Q::Output)> {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: `result` points to `self`, which is `Pin`
        let future = unsafe { Pin::new_unchecked(&mut this.future) };
        let result = std::task::ready!(future.poll(cx));

        let id = this.this.resource;
        let slot = unsafe { this.storage.finish(id, result.output, &result.dependencies) };

        std::task::Poll::Ready((id, &slot.output))
    }
}

impl<Q: Query> QueryTask for QueryCacheTask<'_, Q> {
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> std::task::Poll<()> {
        self.poll_advanced(cx).map(|_| ())
    }

    fn path(&self) -> IngredientPath {
        self.this
    }
}

impl<'a, Q: Query> Future for QueryCacheTask<'a, Q> {
    type Output = (Id, &'a Q::Output);

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        self.poll_advanced(cx)
    }
}
