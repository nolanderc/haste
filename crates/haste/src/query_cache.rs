mod lookup;
mod storage;

use std::{future::Future, pin::Pin, task::Poll};

use futures_lite::FutureExt;

use crate::{
    ContainerPath, Cycle, CycleStrategy, Database, DatabaseFor, Container, ExecFuture, Id,
    IngredientPath, MakeContainer, Query, QueryTask, Revision, Runtime, WithStorage,
};

use self::storage::{OutputSlot, QuerySlot, QueryStorage, WaitFuture};

pub use self::lookup::*;

pub trait QueryCache: MakeContainer {
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

pub trait DynQueryCache<DB: ?Sized>: Container<DB> {
    /// Get the cycle recovery stategy used by the query
    fn cycle_strategy(&self) -> CycleStrategy;

    /// Signals that the specific query is part of a cycle.
    ///
    /// Returns `Err` if the query is already recovering from a cycle.
    fn set_cycle(&self, id: Id, cycle: Cycle) -> Result<(), Cycle>;
}

pub enum LastChangedFuture<'a> {
    Ready(Revision),
    Pending(Pin<Box<dyn Future<Output = Revision> + 'a + Send + Sync>>),
}

impl Future for LastChangedFuture<'_> {
    type Output = Revision;

    fn poll(self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        match self.get_mut() {
            LastChangedFuture::Ready(revision) => Poll::Ready(*revision),
            LastChangedFuture::Pending(pending) => pending.poll(cx),
        }
    }
}

/// A query cache which uses the hash of the input as a key.
pub type HashQueryCache<Q> = QueryCacheImpl<Q, HashStrategy>;

pub struct QueryCacheImpl<Q: Query, Lookup> {
    path: ContainerPath,
    lookup: Lookup,
    storage: QueryStorage<Q>,
}

impl<Q: Query, Lookup> crate::MakeContainer for QueryCacheImpl<Q, Lookup>
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

    fn as_query_cache(&self) -> Option<&dyn DynQueryCache<DB>> {
        Some(self)
    }
}

impl<Q: Query, Lookup> QueryCache for QueryCacheImpl<Q, Lookup>
where
    Lookup: LookupStrategy<Q> + Default + 'static,
{
    type Query = Q;

    fn get_or_evaluate<'a>(&'a self, db: &'a DatabaseFor<Q>, input: Q::Input) -> EvalResult<'a, Q> {
        let (id, slot) = self.lookup.get_or_insert(input, &self.storage);

        let runtime = db.runtime();

        if !slot.try_reserve_for_execution(runtime) {
            // the query is executed elsewhere: await its result
            let pending = wait_until_finished(self.ingredient(id), slot, db);
            return EvalResult::Pending(pending);
        }

        unsafe { EvalResult::Eval(self.execute_query(db, id, slot)) }
    }

    fn get<'a>(&'a self, db: &'a DatabaseFor<Q>, id: Id) -> PendingFuture<'a, Self::Query> {
        let slot = self.storage.slot(id);
        wait_until_finished(self.ingredient(id), slot, db)
    }

    fn set(&mut self, runtime: &mut Runtime, input: Q::Input, output: Q::Output)
    where
        Self::Query: crate::Input,
    {
        let (id, _) = self.lookup.get_or_insert(input, &self.storage);
        let slot = self.storage.slot_mut(id);
        slot.set_output(output, runtime);
    }
}

impl<DB: ?Sized, Q: Query, Lookup> DynQueryCache<DB> for QueryCacheImpl<Q, Lookup>
where
    DB: WithStorage<Q::Storage>,
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
    Pending(PendingFuture<'a, Q>),
    Eval(QueryCacheTask<'a, Q>),
}

fn wait_until_finished<'a, Q: Query>(
    path: IngredientPath,
    slot: &'a QuerySlot<Q>,
    db: &'a DatabaseFor<Q>,
) -> PendingFuture<'a, Q> {
    let fut = slot.wait_until_verified(db.runtime());
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
    unsafe fn execute_query<'a>(
        &'a self,
        db: &'a DatabaseFor<Q>,
        id: Id,
        slot: &'a QuerySlot<Q>,
    ) -> QueryCacheTask<'a, Q> {
        let this = self.ingredient(id);
        QueryCacheTask {
            state: TaskState::Verify {
                db,
                this,
                slot,
                storage: &self.storage,
                future: verify(db.as_dyn(), &self.storage, slot),
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
        slot: &'a QuerySlot<Q>,
        this: IngredientPath,
        future: VerifyFuture<'a, Q>,
    },
    Exec(ExecTaskFuture<'a, Q>),
}

pub type VerifyFuture<'a, Q: Query> = impl Future<Output = Option<&'a OutputSlot<Q>>> + 'a;

/// # Safety
///
/// The slot must be reserved for execution by the current thread
unsafe fn verify<'a, Q: Query>(
    db: &'a dyn Database,
    storage: &'a QueryStorage<Q>,
    slot: &'a QuerySlot<Q>,
) -> VerifyFuture<'a, Q> {
    async move {
        let last_verified = slot.last_verified()?;
        let previous = slot.get_output()?;

        let dependencies = storage.dependencies(previous.dependencies.clone());
        for &dependency in dependencies {
            if Some(last_verified) < db.last_changed(dependency) {
                // the dependency has changed since last time
                return None;
            }
        }

        // all dependencies were up-to-date
        let current = db.runtime().current_revision();
        unsafe { slot.backdate(current) };
        Some(previous)
    }
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
                    db,
                    storage,
                    slot,
                    this,
                    future,
                } => {
                    let future = unsafe { Pin::new_unchecked(future) };
                    if let Some(slot) = std::task::ready!(Future::poll(future, cx)) {
                        return Poll::Ready(QueryResult {
                            id: this.resource,
                            slot,
                        });
                    }

                    let input = unsafe { slot.input_unchecked().clone() };
                    selff.state = TaskState::Exec(ExecTaskFuture {
                        storage,
                        slot,
                        inner: db.runtime().execute_query(*db, input, *this),
                    })
                }
                TaskState::Exec(future) => {
                    let future = unsafe { Pin::new_unchecked(future) };
                    return Future::poll(future, cx);
                }
            }
        }
    }
}

struct ExecTaskFuture<'a, Q: Query> {
    storage: &'a QueryStorage<Q>,
    slot: &'a QuerySlot<Q>,
    inner: ExecFuture<'a, Q>,
}

impl<'a, Q: Query> Future for ExecTaskFuture<'a, Q> {
    type Output = QueryResult<'a, Q>;

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        // SAFETY: we never move anything out of `self` that is not `Unpin`
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY: `this` is an alias for `self` which is pinned.
        let mut future = unsafe { Pin::new_unchecked(&mut this.inner) };

        if let Some(cycle) = this.slot.take_cycle() {
            future.as_mut().recover(cycle, this.slot.input());
        }

        let id = future.as_ref().query().resource;

        let result = std::task::ready!(future.poll(cx));

        let db = this.inner.database();
        let runtime = db.runtime();
        let current = runtime.current_revision();

        if let Some(previous) = unsafe { this.slot.get_output() } {
            if result.output == previous.output {
                // backdate the result (verify the output, but keep the revision it was last
                // changed)
                unsafe { this.slot.backdate(current) };
                return Poll::Ready(QueryResult { id, slot: previous });
            }
        }

        let output = this
            .storage
            .create_output(result.output, &result.dependencies);
        let slot = unsafe { this.slot.finish(output, current) };
        Poll::Ready(QueryResult { id, slot })
    }
}
