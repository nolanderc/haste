use std::{
    future::Future,
    hash::Hash,
    pin::Pin,
    sync::{Arc, Mutex},
    task::Waker,
};

use crate::{
    arena::AppendArena, Database, Dependency, ExecutionResult, Id, IngredientDatabase,
    IngredientPath, Query, QueryFuture, QueryTask,
};

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
    entries: flurry::HashMap<Q::Input, Mutex<InputSlot>>,
    outputs: OutputStorage<Q::Output>,
}

enum InputSlot {
    /// The query associated with this specific input is currently is still progressing
    Progress(QueryProgress),
    /// The query has completed, and its result is associated with the given ID
    Done(Id),
}

struct QueryProgress {
    state: Option<Arc<Mutex<(Option<Id>, Vec<Waker>)>>>,
}

impl QueryProgress {
    fn new() -> Self {
        Self { state: None }
    }

    fn wait(&mut self) -> impl Future<Output = Id> {
        let state = self.state.get_or_insert_with(Default::default).clone();
        let mut registered = false;

        std::future::poll_fn(move |ctx| {
            let mut state = state.lock().unwrap();
            let (id, wakers) = &mut *state;
            if let Some(id) = id {
                return std::task::Poll::Ready(*id);
            }

            if !registered {
                wakers.push(ctx.waker().clone());
                registered = true;
            }

            std::task::Poll::Pending
        })
    }

    fn finish(self, id: Id) {
        if let Some(state) = self.state {
            let mut state = state.lock().unwrap();
            state.0 = Some(id);
            for waker in state.1.drain(..) {
                waker.wake();
            }
        }
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
    Q::Input: Hash + Ord + Clone + Unpin + Sync,
{
    type Query = Q;

    type EvalTask<'a> = impl QueryTask + Send + 'a where Q: 'a;

    type PendingFuture<'a> = impl Future<Output = Id> + 'a where Q: 'a;

    fn get_or_evaluate<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: <Q as Query>::Input,
    ) -> EvalResult<Self::EvalTask<'a>, Self::PendingFuture<'a>> {
        let guard = self.entries.guard();

        let slot = Mutex::new(InputSlot::Progress(QueryProgress::new()));
        match self.entries.try_insert(input.clone(), slot, &guard) {
            Ok(_) => return EvalResult::Eval(self.execute_query(db, input)),
            Err(error) => match &mut *error.current.lock().unwrap() {
                InputSlot::Done(id) => return EvalResult::Cached(*id),
                InputSlot::Progress(progress) => return EvalResult::Pending(progress.wait()),
            },
        }
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
    Q::Input: Hash + Ord + Sync,
{
    fn execute_query<'a>(
        &'a self,
        db: &'a IngredientDatabase<Q>,
        input: Q::Input,
    ) -> HashQueryCacheTask<'a, Q>
    where
        Q::Input: Clone + Unpin,
    {
        let result = db.runtime().execute_query::<Q>(db, input.clone());
        HashQueryCacheTask {
            cache: self,
            input,
            result,
        }
    }

    fn insert(&self, input: &Q::Input, result: ExecutionResult<Q::Output>) -> Id {
        let index = self.outputs.push(result.output, &result.dependencies);

        // make the value available for other threads
        let guard = self.entries.guard();
        let slot = self.entries.get(input, &guard).unwrap();

        let id = Id::try_from_usize(index).expect("exhausted query IDs");
        let previous = std::mem::replace(&mut *slot.lock().unwrap(), InputSlot::Done(id));
        match previous {
            InputSlot::Done(_) => unreachable!("query evaluated twice"),
            InputSlot::Progress(progress) => progress.finish(id),
        }

        id
    }
}

pub struct HashQueryCacheTask<'a, Q: Query> {
    cache: &'a HashQueryCache<Q>,
    input: Q::Input,
    result: QueryFuture<'a, Q>,
}

impl<Q: Query> QueryTask for HashQueryCacheTask<'_, Q>
where
    Q::Input: Hash + Ord + Sync + Clone,
{
    fn description(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", std::any::type_name::<Q>())
    }
}

impl<'a, Q: Query> Future for HashQueryCacheTask<'a, Q>
where
    Q::Input: Hash + Ord + Sync + Clone,
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

        let id = this.cache.insert(&this.input, output);

        std::task::Poll::Ready(id)
    }
}
