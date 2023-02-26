mod lookup;
mod storage;

use std::{future::Future, pin::Pin};

use futures_lite::FutureExt;

use crate::{
    Container, ContainerPath, Cycle, CycleStrategy, Database, DatabaseFor, DynContainer, Id,
    IngredientPath, Query, QueryFuture, QueryTask, Runtime,
};

use self::storage::{OutputSlot, QuerySlot, QueryStorage, WaitFuture};

pub use self::lookup::*;

pub trait QueryCache: DynQueryCache + Container {
    type Query: Query;

    /// Executes the query with the given input, returning an ID for accessing the result of the
    /// query.
    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a DatabaseFor<Self::Query>,
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
        db: &'a DatabaseFor<Self::Query>,
        id: Id,
    ) -> PendingFuture<'a, Self::Query>;

    fn set(
        &mut self,
        runtime: &mut Runtime,
        input: <Self::Query as Query>::Input,
        output: <Self::Query as Query>::Output,
    ) where
        Self::Query: crate::Input;
}

pub trait DynQueryCache: DynContainer {
    /// Get the cycle recovery stategy used by the query
    fn cycle_strategy(&self) -> CycleStrategy;

    /// Signals that the specific query is part of a cycle.
    ///
    /// Returns `Err` if the query is already recovering from a cycle.
    fn set_cycle(&self, id: Id, cycle: Cycle) -> Result<(), Cycle>;
}

/// A query cache which uses the hash of the input as a key.
pub type HashQueryCache<Q> = QueryCacheImpl<Q, HashStrategy>;

pub struct QueryCacheImpl<Q: Query, Lookup> {
    path: ContainerPath,
    lookup: Lookup,
    storage: QueryStorage<Q>,
}

impl<Q: Query, Lookup> crate::Container for QueryCacheImpl<Q, Lookup>
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

impl<Q: Query, Lookup> crate::DynContainer for QueryCacheImpl<Q, Lookup>
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

impl<Q: Query, Lookup> QueryCache for QueryCacheImpl<Q, Lookup>
where
    Lookup: LookupStrategy<Q> + Default + 'static,
{
    type Query = Q;

    fn get_or_evaluate<'a>(&'a self, db: &'a DatabaseFor<Q>, input: Q::Input) -> EvalResult<'a, Q> {
        let (id, input) = match self.lookup.try_insert(input, &self.storage) {
            Err(id) => {
                let slot = self.storage.slot(id);
                if !slot.reserve(db.runtime()) {
                    let pending = wait_until_finished(self.ingredient(id), slot, db);
                    return EvalResult::Pending(pending);
                }
                (id, slot.input())
            }
            Ok((id, input)) => (id, input),
        };

        EvalResult::Eval(self.execute_query(db, id, input.clone()))
    }

    fn get<'a>(&'a self, db: &'a DatabaseFor<Q>, id: Id) -> PendingFuture<'a, Self::Query> {
        let slot = self.storage.slot(id);
        wait_until_finished(self.ingredient(id), slot, db)
    }

    fn set(&mut self, runtime: &mut Runtime, input: Q::Input, output: Q::Output)
    where
        Self::Query: crate::Input,
    {
        let id = match self.lookup.try_insert(input, &self.storage) {
            Ok((id, _)) => id,
            Err(id) => id,
        };
        let slot = self.storage.slot_mut(id);
        slot.set_output(output, runtime);
    }
}

impl<Q: Query, Lookup> DynQueryCache for QueryCacheImpl<Q, Lookup>
where
    Lookup: 'static,
{
    fn cycle_strategy(&self) -> CycleStrategy {
        Q::CYCLE_STRATEGY
    }

    fn set_cycle(&self, id: Id, cycle: Cycle) -> Result<(), Cycle> {
        self.storage.slot(id).set_cycle(cycle)
    }
}

pub struct QueryResult<'a, Q: Query> {
    pub id: Id,
    pub slot: &'a OutputSlot<Q>,
}

pub enum EvalResult<'a, Q: Query> {
    Pending(PendingFuture<'a, Q>),
    Eval(QueryCacheTask<'a, Q>),
}

fn wait_until_finished<'a, Q: Query>(
    path: IngredientPath,
    slot: &'a QuerySlot<Q>,
    db: &'a DatabaseFor<Q>,
) -> PendingFuture<'a, Q> {
    let fut = slot.wait_until_finished(db.runtime());
    PendingFuture {
        db,
        path,
        fut,
        blocks: None,
    }
}

pub struct PendingFuture<'a, Q: Query> {
    db: &'a DatabaseFor<Q>,
    path: IngredientPath,
    blocks: Option<IngredientPath>,
    fut: WaitFuture<'a, Q>,
}

impl<'a, Q: Query> Drop for PendingFuture<'a, Q> {
    fn drop(&mut self) {
        if let Some(parent) = self.blocks.take() {
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
                    runtime.would_block_on(parent, self.path, cx.waker(), db);
                    self.blocks = Some(parent);
                }
            }
            (Poll::Ready(_), Some(parent)) => {
                let runtime = self.db.runtime();
                runtime.unblock(parent);
                self.blocks = None;
            }
            _ => {}
        }

        result.map(|slot| QueryResult {
            id: self.path.resource,
            slot,
        })
    }
}

impl<Q: Query, Lookup> QueryCacheImpl<Q, Lookup> {
    fn execute_query<'a>(
        &'a self,
        db: &'a DatabaseFor<Q>,
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
    ) -> std::task::Poll<QueryResult<'a, Q>> {
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

        let db = this.future.database();
        let runtime = db.runtime();
        let current = runtime.current_revision();

        if let Some(previous) = unsafe { slot.get_output() } {
            if result.output == previous.output {
                // backdate the result (verify the output, but keep the revision it was last
                // changed)
                unsafe { slot.backdate(current) };
                return std::task::Poll::Ready(QueryResult { id, slot: previous });
            }
        }

        let output = this
            .storage
            .create_output(result.output, &result.dependencies);
        let output_slot = unsafe { slot.finish(output, current) };
        std::task::Poll::Ready(QueryResult {
            id,
            slot: output_slot,
        })
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
    type Output = QueryResult<'a, Q>;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        self.poll_advanced(cx)
    }
}
