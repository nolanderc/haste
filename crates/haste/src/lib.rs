pub mod arena;
mod cache;
mod durability;
pub mod fmt;
mod interner;
mod revision;
mod runtime;
pub mod shard;
mod util;

use std::borrow::{Borrow, BorrowMut};

pub use cache::{QueryCache, SlotId};
pub use durability::Durability;
pub use fmt::*;
pub use interner::{InternId, Interner, ValueInterner};
pub use runtime::{Dependency, LastChange, Runtime};

pub use haste_macros::*;

pub trait Database {
    fn runtime(&self) -> &Runtime;
    fn runtime_mut(&mut self) -> &mut Runtime;
    fn last_change(&self, element: ElementPath) -> Option<LastChange>;
    fn storage_any(&self, type_id: std::any::TypeId) -> Option<&dyn std::any::Any>;
}

pub trait StaticDatabase: Database + Sized {
    type StorageList: StorageList<Self>;
}

pub trait StorageList<DB> {
    fn new(router: &mut StorageRouter<DB>) -> Self;
    fn storage_any(&self, type_id: std::any::TypeId) -> Option<&dyn std::any::Any>;
}

macro_rules! storage_list_tuple_impl {
    ($($T:ident)*) => {
        #[allow(unused_variables, non_snake_case, clippy::unused_unit)]
        impl<DB, $($T: Storage + 'static),*> StorageList<DB> for ($($T,)*)
        where
            $(DB: WithStorage<$T>),*
        {
            fn new(router: &mut StorageRouter<DB>) -> Self {
                ( $($T::new(router),)* )
            }

            fn storage_any(&self, type_id: std::any::TypeId) -> Option<&dyn std::any::Any> {
                let ($($T,)*) = self;

                $(
                    if std::any::TypeId::of::<$T>() == type_id {
                        return Some($T)
                    }
                )*

                None
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

    pub fn storages_mut(&mut self) -> (&mut DB::StorageList, &mut Runtime) {
        (&mut self.storages, &mut self.runtime)
    }

    pub fn container<'a>(&self, db: &'a DB, element: ElementId) -> &'a dyn Container<DB> {
        self.routes[usize::from(element.0)](db)
    }

    pub fn last_change(&self, db: &DB, query: ElementPath) -> Option<LastChange> {
        self.container(db, query.element)
            .last_change(db, query.slot)
    }
}

pub trait Storage: Sized {
    type Database<'a>: Database + ?Sized + 'a;

    fn new<DB>(router: &mut StorageRouter<DB>) -> Self
    where
        DB: WithStorage<Self>;
}

pub trait WithStorage<S: Storage>: Database {
    fn storage(&self) -> &S;
    fn storage_mut(&mut self) -> (&mut S, &mut Runtime);
    fn cast_database(&self) -> &S::Database<'_>;
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

type Route<DB> = fn(&DB) -> &dyn Container<DB>;

pub trait Container<DB: ?Sized> {
    fn new(element: ElementId) -> Self
    where
        Self: Sized;

    fn element(&self) -> ElementId;

    fn last_change(&self, db: &DB, slot: SlotId) -> Option<LastChange>;
}

pub trait WithElement<E: Element + ?Sized>: Storage {
    fn container(&self) -> &E::Container;
    fn container_mut(&mut self) -> &mut E::Container;
}

pub trait Element {
    type Storage: WithElement<Self>;
    type Container;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ElementId(u16);

pub type ElementDb<'a, T> = <<T as Element>::Storage as Storage>::Database<'a>;

pub trait Query: Element {
    type Arguments: Clone + Eq + 'static;
    type Output: Eq + 'static;
    type View<'a>;

    /// Amount of stack space required by the query.
    const REQUIRED_STACK: usize = 512 * 1024;

    /// Determines if this is an input query. If `true` this query cannot invoke any other queries.
    const IS_INPUT: bool = false;

    fn execute(db: &ElementDb<Self>, args: Self::Arguments) -> Self::Output;

    fn view(output: &Self::Output) -> Self::View<'_>;
}

pub trait Input: Query {}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ElementPath {
    pub(crate) element: ElementId,
    pub(crate) slot: SlotId,
}

impl std::fmt::Debug for ElementPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.element.0, self.slot.index())
    }
}

pub trait Intern: Element {
    type Value: 'static;

    fn from_id(id: InternId) -> Self;
    fn id(self) -> InternId;
}

pub trait DatabaseExt: Database {
    #[inline]
    fn query<'a, Q: Query>(&'a self, args: Q::Arguments) -> &Q::Output
    where
        Self: WithStorage<Q::Storage>,
        Q: 'a,
        Q::Container: Borrow<QueryCache<Q>> + 'a,
        Q::Arguments: Eq + std::hash::Hash,
    {
        let storage = self.storage();
        let container = storage.container();
        container
            .borrow()
            .get_or_execute(self.cast_database(), args)
    }

    #[inline]
    fn spawn<Q: Query>(&self, args: Q::Arguments) -> QueryHandle<Q>
    where
        Self: WithStorage<Q::Storage>,
        Q::Container: Borrow<QueryCache<Q>>,
        Q::Arguments: Eq + std::hash::Hash,
    {
        let storage = self.storage();
        let container = storage.container();
        container.borrow().spawn(self.cast_database(), args)
    }

    #[inline]
    fn set<I: Input>(&mut self, args: I::Arguments, value: I::Output, durability: Durability)
    where
        Self: WithStorage<I::Storage>,
        I::Container: BorrowMut<QueryCache<I>>,
        I::Arguments: Eq + std::hash::Hash,
    {
        assert!(I::IS_INPUT);
        let (storage, runtime) = self.storage_mut();
        let container = storage.container_mut();
        container.borrow_mut().set(runtime, args, value, durability);
    }

    #[inline]
    fn invalidate<I: Input>(&mut self, args: I::Arguments)
    where
        Self: WithStorage<I::Storage>,
        I::Container: Borrow<QueryCache<I>> + BorrowMut<QueryCache<I>>,
        I::Arguments: Eq + std::hash::Hash,
    {
        assert!(I::IS_INPUT);

        let (output, info) = self.scope(|db| {
            let storage = db.storage();
            let container = storage.container();
            container
                .borrow()
                .execute_input(db.cast_database(), args.clone())
        });

        let (storage, runtime) = self.storage_mut();
        let container = storage.container_mut();
        container
            .borrow_mut()
            .set(runtime, args, output, info.durability);
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

    fn lookup<'a, T: Intern>(&'a self, interned: T) -> &T::Value
    where
        Self: WithStorage<T::Storage>,
        T::Storage: 'a,
        T::Container: Interner<T::Value> + 'a,
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
    pub fn join(self) -> Q::View<'a> {
        let output = self.slot.wait_output(self.dependency, self.runtime);
        Q::view(output)
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
