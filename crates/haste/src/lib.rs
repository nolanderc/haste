mod arena;
mod cache;
mod interner;
mod runtime;
mod shard;

use std::borrow::Borrow;

pub use cache::QueryCache;
use cache::SlotId;

pub use runtime::Runtime;

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

pub trait Container: 'static {
    fn new(element: ElementId) -> Self
    where
        Self: Sized;

    fn element(&self) -> ElementId;
}

pub trait WithContainer<C: Container>: Storage {
    fn container(&self) -> &C;
}

pub trait Element: 'static {
    type Storage: WithContainer<Self::Container>;
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

    #[inline]
    fn scope<R>(&mut self, block: impl FnOnce(&Self) -> R) -> R {
        self.runtime_mut().enter();
        let result = block(self);
        self.runtime_mut().exit();
        result
    }
}

impl<DB> DatabaseExt for DB where DB: Database {}

pub struct QueryHandle<'a, Q: Query> {
    path: QueryPath,
    slot: &'a cache::Slot<Q>,
    runtime: &'a Runtime,
}

impl<Q: Query> Copy for QueryHandle<'_, Q> {}
impl<Q: Query> Clone for QueryHandle<'_, Q> {
    fn clone(&self) -> Self {
        Self {
            path: self.path,
            slot: self.slot,
            runtime: self.runtime,
        }
    }
}

impl<'a, Q: Query> QueryHandle<'a, Q> {
    pub fn join(self) -> &'a Q::Output {
        self.slot.wait_output(self.path, self.runtime)
    }
}

pub fn scope<DB, R>(db: &mut DB, block: impl FnOnce(&DB) -> R) -> R
where
    DB: Database,
{
    db.runtime_mut().enter();
    let result = block(db);
    db.runtime_mut().exit();
    result
}
