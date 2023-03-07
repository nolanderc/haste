mod lookup;
mod storage;
mod verify;

use std::{future::Future, pin::Pin, task::Poll};

use crate::{
    Change, ContainerPath, Cycle, CycleStrategy, Database, DatabaseFor, Durability, ExecFuture, Id,
    IngredientPath, LastChangeFuture, Query, QueryTask, Revision, Runtime, WithStorage,
};

use self::storage::{ClaimedSlot, OutputSlot, QuerySlot, QueryStorage, WaitFuture};

pub use self::lookup::*;
pub use self::storage::{ChangeFuture, RevisionRange, TransitiveDependencies};

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
        durability: Durability,
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

    fn last_change<'a>(&'a self, db: &'a DB, dep: crate::Dependency) -> LastChangeFuture<'a> {
        let id = dep.resource;
        let slot = self.storage.slot(id);
        let current = self.storage.current_revision();

        match self.claim(slot) {
            Err(Some(output)) => {
                return LastChangeFuture::Ready(Change {
                    changed_at: slot.last_changed(),
                    transitive: output.transitive,
                })
            }
            Err(None) => {}
            Ok(claim) => {
                let task = self.execute_query(db.cast_dyn(), id, claim);
                db.runtime().spawn_query(task);
            }
        }

        LastChangeFuture::Pending(slot.wait_for_change(current))
    }
}

impl<Q: Query, Lookup> QueryCache for QueryCacheImpl<Q, Lookup>
where
    Lookup: LookupStrategy<Q> + 'static,
{
    type Query = Q;

    fn get_or_evaluate<'a>(&'a self, db: &'a DatabaseFor<Q>, input: Q::Input) -> EvalResult<'a, Q> {
        let (id, slot) = self.lookup.get_or_insert(input, &self.storage);

        let span = tracing::trace_span!(
            "get_or_evaluate",
            query = %crate::util::fmt::ingredient(db.as_dyn(), self.ingredient(id)),
        );
        let _guard = span.entered();

        self.get_or_evaluate_slot(db, id, slot)
    }

    fn get<'a>(
        &'a self,
        db: &'a DatabaseFor<Q>,
        id: Id,
    ) -> Result<QueryResult<'a, Q>, PendingFuture<'a, Q>> {
        let slot = self.storage.slot(id);
        let current = self.storage.current_revision();

        unsafe {
            if let Some(slot) = slot.try_get(current) {
                return Ok(QueryResult { id, slot });
            }

            let path = self.ingredient(id);
            Err(wait_until_finished(db, slot, current, path))
        }
    }

    fn set(
        &mut self,
        runtime: &mut Runtime,
        input: Q::Input,
        output: Q::Output,
        durability: Durability,
    ) where
        Self::Query: crate::Input,
    {
        let (id, _) = self.lookup.get_or_insert(input, &self.storage);
        let slot = self.storage.slot_mut(id);

        if let Some(previous) = slot.get_output_mut() {
            if previous.output == output && previous.transitive.durability == durability {
                // no change: the value is still valid
                slot.set_verified(runtime.current_revision());
                return;
            }
        }

        slot.set_output(output, durability, runtime);
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

/// # Safety
///
/// Only the current revision of the database must be used.
unsafe fn wait_until_finished<'a, Q: Query>(
    db: &'a DatabaseFor<Q>,
    slot: &'a QuerySlot<Q>,
    revision: Revision,
    path: IngredientPath,
) -> PendingFuture<'a, Q> {
    let fut = slot.wait_until_verified(revision);
    PendingFuture::new(db, path, fut)
}

#[pin_project::pin_project(PinnedDrop)]
pub struct PendingFuture<'a, Q: Query> {
    db: &'a DatabaseFor<Q>,
    path: IngredientPath,
    blocks: Option<IngredientPath>,
    #[pin]
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

#[pin_project::pinned_drop]
impl<Q: Query> PinnedDrop for PendingFuture<'_, Q> {
    fn drop(self: Pin<&mut Self>) {
        let this = self.project();
        if let Some(parent) = this.blocks.take() {
            this.db.runtime().unblock(parent);
        }
    }
}

impl<'a, Q: Query> Future for PendingFuture<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let this = self.project();

        let result = this.fut.poll(cx);

        match (&result, *this.blocks) {
            (Poll::Pending, None) => {
                let db = this.db.as_dyn();
                let runtime = this.db.runtime();
                if let Some(parent) = runtime.current_query() {
                    runtime.would_block_on(parent, *this.path, cx.waker(), db);
                    *this.blocks = Some(parent);
                }
            }
            (Poll::Ready(_), Some(parent)) => {
                let runtime = this.db.runtime();
                runtime.unblock(parent);
                *this.blocks = None;
            }
            _ => {}
        }

        result.map(|slot| QueryResult {
            id: this.path.resource,
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
            Ok(slot) => {
                tracing::trace!("needs to be evaluated");
                EvalResult::Eval(self.execute_query(db, id, slot))
            }
            Err(None) => {
                tracing::trace!("wait until completed");
                // the query is executed elsewhere: await its result
                let path = self.ingredient(id);
                let current = self.storage.current_revision();
                let pending = unsafe { wait_until_finished(db, slot, current, path) };
                EvalResult::Pending(pending)
            }
            Err(Some(slot)) => {
                tracing::trace!("using cached output");
                EvalResult::Cached(QueryResult { id, slot })
            }
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
                path: this,
                storage: &self.storage,
                future: verify::verify(db.as_dyn(), &self.storage, slot),
            },
            span: None,
        }
    }

    fn ingredient(&self, id: Id) -> IngredientPath {
        IngredientPath {
            container: self.path,
            resource: id,
        }
    }
}

#[pin_project::pin_project]
pub struct QueryCacheTask<'a, Q: Query> {
    #[pin]
    state: TaskState<'a, Q>,
    /// A span representing the duration of the query.
    span: Option<tracing::Span>,
}

#[pin_project::pin_project(project = TaskStateProj)]
enum TaskState<'a, Q: Query> {
    Verify {
        db: &'a DatabaseFor<Q>,
        storage: &'a QueryStorage<Q>,
        path: IngredientPath,
        #[pin]
        future: verify::VerifyFuture<'a, Q>,
    },
    Exec(#[pin] ExecTaskFuture<'a, Q>),
}

impl<'a, Q: Query> TaskState<'a, Q> {
    fn path(&self) -> IngredientPath {
        match &self {
            TaskState::Verify { path, .. } => *path,
            TaskState::Exec(future) => future.inner.query(),
        }
    }

    fn database(&self) -> &DatabaseFor<Q> {
        match &self {
            TaskState::Verify { db, .. } => *db,
            TaskState::Exec(future) => future.inner.database(),
        }
    }
}

impl<Q: Query> QueryTask for QueryCacheTask<'_, Q> {
    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context) -> Poll<()> {
        Future::poll(self, cx).map(|_| ())
    }

    fn path(&self) -> IngredientPath {
        match &self.state {
            TaskState::Verify { path, .. } => *path,
            TaskState::Exec(future) => future.inner.query(),
        }
    }
}

impl<'a, Q: Query> Future for QueryCacheTask<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let mut this = self.project();

        if this.span.is_none() {
            *this.span = Some(tracing::debug_span!(
                parent: None,
                "evaluate",
                query = %crate::util::fmt::ingredient(this.state.database().as_dyn(), this.state.path()),
            ));
        }

        let _guard = this.span.as_ref().map(|span| span.enter());

        loop {
            match this.state.as_mut().project() {
                TaskStateProj::Verify {
                    future,
                    path,
                    db,
                    storage,
                } => match std::task::ready!(Future::poll(future, cx)) {
                    Ok(slot) => {
                        let id = path.resource;
                        break Poll::Ready(QueryResult { id, slot });
                    }
                    Err(slot) => {
                        let input = slot.input().clone();
                        let inner = db.runtime().execute_query(*db, input, *path);
                        let next = TaskState::Exec(ExecTaskFuture {
                            storage,
                            slot: Some(slot),
                            inner,
                        });
                        this.state.set(next);
                    }
                },
                TaskStateProj::Exec(future) => break Future::poll(future, cx),
            }
        }
    }
}

#[pin_project::pin_project]
struct ExecTaskFuture<'a, Q: Query> {
    storage: &'a QueryStorage<Q>,
    slot: Option<ClaimedSlot<'a, Q>>,
    #[pin]
    inner: ExecFuture<'a, Q>,
}

impl<'a, Q: Query> Future for ExecTaskFuture<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        let mut this = self.project();

        let slot = this.slot.as_mut().expect("query already completed");

        if let Some(cycle) = slot.take_cycle() {
            this.inner.as_mut().recover(cycle, slot.input());
        }

        let id = this.inner.query().resource;

        let result = std::task::ready!(this.inner.poll(cx));
        let new = this.storage.create_output(result);

        let mut slot = this.slot.take().unwrap();

        if let Some(previous) = slot.get_output() {
            if new.output == previous.output {
                // backdate the result (verify the output, but keep the revision it was last
                // changed)
                tracing::debug!(reason = "output unchanged", "backdating");
                previous.dependencies = new.dependencies;
                previous.transitive = new.transitive;
                let slot = slot.backdate();
                return Poll::Ready(QueryResult { id, slot });
            }
        }

        let slot = slot.finish(new);
        Poll::Ready(QueryResult { id, slot })
    }
}
