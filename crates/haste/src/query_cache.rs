mod lookup;
mod storage;
mod verify;

use std::{future::Future, pin::Pin, task::Poll};

use futures_lite::FutureExt;

use crate::{
    ContainerPath, Cycle, CycleStrategy, Database, DatabaseFor, ExecFuture, Id, IngredientPath,
    LastChangedFuture, Query, QueryTask, Revision, Runtime, WithStorage,
};

use self::storage::{ClaimedSlot, OutputSlot, QuerySlot, QueryStorage, WaitFuture};

pub use self::lookup::*;

pub trait QueryCache: DynQueryCache {
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
    ) -> Result<QueryResult<'a, Self::Query>, PendingFuture<'a, Self::Query>>;

    fn set(
        &mut self,
        runtime: &mut Runtime,
        input: <Self::Query as Query>::Input,
        output: <Self::Query as Query>::Output,
    ) where
        Self::Query: crate::Input;
}

pub trait DynQueryCache {
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

impl<Q: Query, Lookup> crate::StaticContainer for QueryCacheImpl<Q, Lookup>
where
    Lookup: Default + Sync + 'static,
{
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            lookup: Lookup::default(),
            storage: QueryStorage::default(),
        }
    }

    fn begin(&mut self, current: Revision) {
        self.storage.set_current_revision(Some(current));
    }

    fn end(&mut self) {
        self.storage.set_current_revision(None);
    }
}

impl<DB: ?Sized, Q: Query, Lookup> crate::Container<DB> for QueryCacheImpl<Q, Lookup>
where
    DB: WithStorage<Q::Storage>,
    Lookup: Sync + 'static,
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

    fn last_changed<'a>(&'a self, db: &'a DB, dep: crate::Dependency) -> LastChangedFuture<'a> {
        let id = dep.resource;
        let slot = self.storage.slot(id);
        let current = self.storage.current_revision();

        if slot.last_verified() == Some(current) {
            return LastChangedFuture::Ready(slot.last_changed());
        }

        let db = db.cast_dyn();
        let pending = match self.get_or_evaluate_slot(db, id, slot) {
            EvalResult::Cached(_) => return LastChangedFuture::Ready(slot.last_changed()),
            EvalResult::Pending(pending) => pending,
            EvalResult::Eval(task) => {
                db.runtime().spawn_query(task);
                wait_until_finished(db, slot, current, dep.ingredient())
            }
        };

        // TODO: use a type-erased future.
        LastChangedFuture::Future(Box::pin(async move {
            // yield to the scheduler so that the query has an oppurtunity to execute
            futures_lite::future::yield_now().await;
            pending.await;
            slot.last_changed()
        }))
    }
}

impl<Q: Query, Lookup> QueryCache for QueryCacheImpl<Q, Lookup>
where
    Lookup: LookupStrategy<Q> + 'static,
{
    type Query = Q;

    fn get_or_evaluate<'a>(&'a self, db: &'a DatabaseFor<Q>, input: Q::Input) -> EvalResult<'a, Q> {
        let (id, slot) = self.lookup.get_or_insert(input, &self.storage);
        self.get_or_evaluate_slot(db, id, slot)
    }

    fn get<'a>(
        &'a self,
        db: &'a DatabaseFor<Q>,
        id: Id,
    ) -> Result<QueryResult<'a, Q>, PendingFuture<'a, Q>> {
        let slot = self.storage.slot(id);
        let current = self.storage.current_revision();

        if slot.last_verified() == Some(current) {
            let slot = unsafe { slot.output_unchecked() };
            return Ok(QueryResult { id, slot });
        }

        Err(wait_until_finished(db, slot, current, self.ingredient(id)))
    }

    fn set(&mut self, runtime: &mut Runtime, input: Q::Input, output: Q::Output)
    where
        Self::Query: crate::Input,
    {
        let (id, _) = self.lookup.get_or_insert(input, &self.storage);
        let slot = self.storage.slot_mut(id);

        if let Some(previous) = slot.get_output_mut() {
            if previous.output == output {
                // no change: the value is still valid
                slot.set_verified(runtime.current_revision());
                return;
            }
        }

        slot.set_output(output, runtime);
    }
}

impl<Q: Query, Lookup> DynQueryCache for QueryCacheImpl<Q, Lookup>
where
    Lookup: Sync + 'static,
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
    Cached(QueryResult<'a, Q>),
    Pending(PendingFuture<'a, Q>),
    Eval(QueryCacheTask<'a, Q>),
}

fn wait_until_finished<'a, Q: Query>(
    db: &'a DatabaseFor<Q>,
    slot: &'a QuerySlot<Q>,
    revision: Revision,
    path: IngredientPath,
) -> PendingFuture<'a, Q> {
    let fut = slot.wait_until_verified(revision);
    PendingFuture::new(db, path, fut)
}

pub struct PendingFuture<'a, Q: Query> {
    db: &'a DatabaseFor<Q>,
    path: IngredientPath,
    blocks: Option<IngredientPath>,
    fut: WaitFuture<'a, Q>,
}

impl<'a, Q: Query> PendingFuture<'a, Q> {
    pub fn new(db: &'a DatabaseFor<Q>, path: IngredientPath, fut: WaitFuture<'a, Q>) -> Self {
        Self {
            db,
            path,
            blocks: None,
            fut,
        }
    }
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

    fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
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
    fn claim<'a>(
        &self,
        slot: &'a QuerySlot<Q>,
    ) -> Result<ClaimedSlot<'a, Q>, Option<&'a OutputSlot<Q>>> {
        unsafe { slot.claim(self.storage.current_revision()) }
    }

    fn get_or_evaluate_slot<'a>(
        &'a self,
        db: &'a DatabaseFor<Q>,
        id: Id,
        slot: &'a QuerySlot<Q>,
    ) -> EvalResult<'a, Q> {
        match self.claim(slot) {
            Ok(slot) => EvalResult::Eval(self.execute_query(db, id, slot)),
            Err(None) => {
                // the query is executed elsewhere: await its result
                let path = self.ingredient(id);
                let current = self.storage.current_revision();
                EvalResult::Pending(wait_until_finished(db, slot, current, path))
            }
            Err(Some(slot)) => EvalResult::Cached(QueryResult { id, slot }),
        }
    }

    fn execute_query<'a>(
        &'a self,
        db: &'a DatabaseFor<Q>,
        id: Id,
        slot: ClaimedSlot<'a, Q>,
    ) -> QueryCacheTask<'a, Q> {
        let this = self.ingredient(id);
        QueryCacheTask {
            state: TaskState::Verify {
                db,
                this,
                storage: &self.storage,
                future: verify::verify(db.as_dyn(), &self.storage, slot),
            },
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
    state: TaskState<'a, Q>,
}

enum TaskState<'a, Q: Query> {
    Verify {
        db: &'a DatabaseFor<Q>,
        storage: &'a QueryStorage<Q>,
        this: IngredientPath,
        future: verify::VerifyFuture<'a, Q>,
    },
    Exec(ExecTaskFuture<'a, Q>),
}

impl<Q: Query> QueryTask for QueryCacheTask<'_, Q> {
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> Poll<()> {
        Future::poll(self, cx).map(|_| ())
    }

    fn path(&self) -> IngredientPath {
        match &self.state {
            TaskState::Verify { this, .. } => *this,
            TaskState::Exec(future) => future.inner.query(),
        }
    }
}

impl<'a, Q: Query> Future for QueryCacheTask<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let selff = unsafe { self.get_unchecked_mut() };
        loop {
            match &mut selff.state {
                TaskState::Verify {
                    future,
                    this,
                    db,
                    storage,
                    ..
                } => {
                    let future = unsafe { Pin::new_unchecked(future) };
                    match std::task::ready!(Future::poll(future, cx)) {
                        Ok(slot) => {
                            let id = this.resource;
                            break Poll::Ready(QueryResult { id, slot });
                        }
                        Err(slot) => {
                            let input = slot.input().clone();
                            let inner = db.runtime().execute_query(*db, input, *this);
                            selff.state = TaskState::Exec(ExecTaskFuture {
                                storage,
                                slot: Some(slot),
                                inner,
                            })
                        }
                    }
                }
                TaskState::Exec(future) => {
                    let future = unsafe { Pin::new_unchecked(future) };
                    break Future::poll(future, cx);
                }
            }
        }
    }
}

struct ExecTaskFuture<'a, Q: Query> {
    storage: &'a QueryStorage<Q>,
    slot: Option<ClaimedSlot<'a, Q>>,
    inner: ExecFuture<'a, Q>,
}

impl<'a, Q: Query> Future for ExecTaskFuture<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: `this` is an alias for `self` which is pinned.
        let mut future = unsafe { Pin::new_unchecked(&mut this.inner) };

        let slot = this.slot.as_ref().expect("query already completed");

        if let Some(cycle) = slot.take_cycle() {
            future.as_mut().recover(cycle, slot.input());
        }

        let id = future.as_ref().query().resource;

        let result = std::task::ready!(future.poll(cx));

        if let Some(previous) = slot.get_output() {
            if result.output == previous.output {
                // backdate the result (verify the output, but keep the revision it was last
                // changed)
                let slot = this.slot.take().unwrap().backdate();
                return Poll::Ready(QueryResult { id, slot });
            }
        }

        let mut output = this.storage.create_output(result);

        if Q::IS_INPUT {
            output.latest_dependency = Some(slot.current_revision());
        }

        let slot = this.slot.take().unwrap().finish(output);
        Poll::Ready(QueryResult { id, slot })
    }
}
