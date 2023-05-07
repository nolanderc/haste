pub mod arena;
mod cache;
mod interner;
mod runtime;
pub mod shard;
mod durability;

use cache::SlotId;
use std::borrow::Borrow;

pub use cache::QueryCache;
pub use interner::{InternId, Interner, ValueInterner};
pub use runtime::{Dependency, Runtime};
pub use durability::Durability;

pub use haste_macros::*;

pub trait Database {
    fn runtime(&self) -> &Runtime;
    fn runtime_mut(&mut self) -> &mut Runtime;
}

pub trait StaticDatabase: Database + Sized {
    type StorageList: StorageList<Self>;
}

pub trait StorageList<DB> {
    fn new(router: &mut StorageRouter<DB>) -> Self;
}

macro_rules! storage_list_tuple_impl {
    ($($T:ident)*) => {
        #[allow(unused_variables, clippy::unused_unit)]
        impl<DB, $($T: Storage),*> StorageList<DB> for ($($T,)*)
        where
            $(DB: WithStorage<$T>),*
        {
            fn new(router: &mut StorageRouter<DB>) -> Self {
                ( $($T::new(router),)* )
            }
        }
    }
}

storage_list_tuple_impl!();
storage_list_tuple_impl!(A);
storage_list_tuple_impl!(A B);
storage_list_tuple_impl!(A B C);
storage_list_tuple_impl!(A B C D);
storage_list_tuple_impl!(A B C D E);
storage_list_tuple_impl!(A B C D E F);
storage_list_tuple_impl!(A B C D E F G);
storage_list_tuple_impl!(A B C D E F G H);
storage_list_tuple_impl!(A B C D E F G H I);
storage_list_tuple_impl!(A B C D E F G H I J);
storage_list_tuple_impl!(A B C D E F G H I J K);

pub struct DatabaseStorage<DB: StaticDatabase> {
    runtime: Runtime,
    routes: Vec<Route<DB>>,
    storages: DB::StorageList,
}

impl<DB: StaticDatabase> Default for DatabaseStorage<DB>
where
    DB: StaticDatabase,
{
    fn default() -> Self {
        let mut router = StorageRouter::new();
        let storages = <DB::StorageList as StorageList<DB>>::new(&mut router);

        Self {
            runtime: Runtime::new(),
            routes: router.routes,
            storages,
        }
    }
}

impl<DB: StaticDatabase> DatabaseStorage<DB> {
    pub fn runtime(&self) -> &Runtime {
        &self.runtime
    }

    pub fn runtime_mut(&mut self) -> &mut Runtime {
        &mut self.runtime
    }

    pub fn storages(&self) -> &DB::StorageList {
        &self.storages
    }

    pub fn container<'a>(&self, db: &'a DB, element: ElementId) -> &'a dyn Container {
        self.routes[usize::from(element.0)](db)
    }
}

pub trait Storage: Sized + 'static {
    type Database: Database + ?Sized;

    fn new<DB>(router: &mut StorageRouter<DB>) -> Self
    where
        DB: WithStorage<Self>;
}

pub trait WithStorage<S: Storage>: Database {
    fn storage(&self) -> &S;
    fn cast_database(&self) -> &S::Database;
}

pub struct StorageRouter<DB> {
    routes: Vec<Route<DB>>,
}

impl<DB> StorageRouter<DB> {
    pub(crate) fn new() -> Self {
        Self { routes: Vec::new() }
    }

    pub fn push(&mut self, route: Route<DB>) -> ElementId {
        let index = u16::try_from(self.routes.len()).expect("too many containers");
        self.routes.push(route);
        ElementId(index)
    }
}

type Route<DB> = fn(&DB) -> &dyn Container;

pub trait Container {
    fn new(element: ElementId) -> Self
    where
        Self: Sized;

    fn element(&self) -> ElementId;
}

pub trait WithElement<E: Element + ?Sized>: Storage {
    fn container(&self) -> &E::Container;
}

pub trait Element: 'static {
    type Storage: WithElement<Self>;
    type Container: Container;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ElementId(u16);

pub type ElementDb<T> = <<T as Element>::Storage as Storage>::Database;

pub trait Query: Element {
    type Input: Clone;
    type Output: Clone;

    /// Amount of stack space required by the
    const REQUIRED_STACK: usize = 512 * 1024;

    fn execute(db: &ElementDb<Self>, input: Self::Input) -> Self::Output;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct QueryPath {
    pub(crate) element: ElementId,
    pub(crate) slot: SlotId,
}

pub trait Intern: Element {
    type Value;

    fn from_id(id: InternId) -> Self;
    fn id(self) -> InternId;
}

pub trait DatabaseExt: Database {
    #[inline]
    fn query<Q: Query>(&self, input: Q::Input) -> &Q::Output
    where
        Self: WithStorage<Q::Storage>,
        Q::Container: Borrow<QueryCache<Q>>,
        Q::Input: Eq + std::hash::Hash,
    {
        let storage = self.storage();
        let container = storage.container();
        container
            .borrow()
            .get_or_execute(self.cast_database(), input)
    }

    #[inline]
    fn spawn<Q: Query>(&self, input: Q::Input) -> QueryHandle<Q>
    where
        Self: WithStorage<Q::Storage>,
        Q::Container: Borrow<QueryCache<Q>>,
        Q::Input: Eq + std::hash::Hash,
    {
        let storage = self.storage();
        let container = storage.container();
        container.borrow().spawn(self.cast_database(), input)
    }

    fn intern<T: Intern>(&self, value: T::Value) -> T
    where
        Self: WithStorage<T::Storage>,
        T::Container: Interner<T::Value>,
    {
        let storage = self.storage();
        let container = storage.container();
        let id = container.insert(value);
        T::from_id(id)
    }

    fn lookup<T: Intern>(&self, interned: T) -> &T::Value
    where
        Self: WithStorage<T::Storage>,
        T::Container: Interner<T::Value>,
    {
        let storage = self.storage();
        let container = storage.container();
        container
            .lookup(interned.id())
            .expect("interned value not found")
    }

    #[inline]
    fn scope<R>(&mut self, block: impl FnOnce(&Self) -> R) -> R {
        scope(self, block)
    }
}

impl<DB> DatabaseExt for DB where DB: Database + ?Sized {}

pub struct QueryHandle<'a, Q: Query> {
    dependency: Dependency,
    slot: &'a cache::Slot<Q>,
    runtime: &'a Runtime,
}

impl<Q: Query> Copy for QueryHandle<'_, Q> {}
impl<Q: Query> Clone for QueryHandle<'_, Q> {
    fn clone(&self) -> Self {
        Self {
            dependency: self.dependency,
            slot: self.slot,
            runtime: self.runtime,
        }
    }
}

impl<'a, Q: Query> QueryHandle<'a, Q> {
    pub fn join(self) -> &'a Q::Output {
        self.slot.wait_output(self.dependency, self.runtime)
    }
}

pub fn scope<DB, F, R>(db: &mut DB, block: F) -> R
where
    DB: Database + ?Sized,
    F: FnOnce(&DB) -> R,
{
    use std::panic::AssertUnwindSafe;

    unsafe { db.runtime_mut().enter() };
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| block(db)));
    unsafe { db.runtime_mut().exit() };

    match result {
        Ok(output) => output,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}
