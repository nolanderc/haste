use std::{future::Future, pin::Pin};

use crate::{
    revision::Revision, Database, Dependency, DynQueryCache, Runtime, StaticDatabase,
    TransitiveDependencies, WithStorage,
};

/// Stores the containers for all ingredients in a database.
pub trait Storage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized + WithStorage<Self>;

    /// Initialize the storage within some database.
    fn new<DB: WithStorage<Self>>(router: &mut StorageRouter<DB>) -> Self;

    fn begin(&mut self, current: Revision);
    fn end(&mut self);
}

/// Stores the data requried by a single ingredient
pub trait Container<DB: ?Sized>: 'static + Sync {
    fn path(&self) -> ContainerPath;

    fn fmt(&self, id: crate::Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn as_query_cache(&self) -> Option<&dyn DynQueryCache> {
        None
    }

    fn last_change<'a>(&'a self, db: &'a DB, dep: Dependency) -> LastChangeFuture<'a>;
}

#[pin_project::pin_project(project = LastChangeProj)]
pub enum LastChangeFuture<'a> {
    Ready(Change),
    Pending(#[pin] crate::query_cache::ChangeFuture<'a>),
}

#[derive(Clone, Copy)]
pub struct Change {
    pub(crate) changed_at: Option<Revision>,
    pub(crate) transitive: TransitiveDependencies,
}

impl Change {
    pub(crate) const NONE: Self = Self {
        changed_at: None,
        transitive: TransitiveDependencies::CONSTANT,
    };
}

impl Future for LastChangeFuture<'_> {
    type Output = Change;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        match self.project() {
            LastChangeProj::Ready(ready) => std::task::Poll::Ready(*ready),
            LastChangeProj::Pending(future) => future.poll(cx),
        }
    }
}

pub trait StaticContainer {
    fn new(path: ContainerPath) -> Self;

    /// Called at the start of a new revision
    #[allow(unused_variables)]
    fn begin(&mut self, current: Revision) {}

    /// Called at the end of a revision
    fn end(&mut self) {}
}

/// Identifies a single container in a database
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContainerPath {
    pub(crate) index: u16,
}

/// Identifies a single resource in a database
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IngredientPath {
    pub container: ContainerPath,
    pub resource: crate::Id,
}

impl std::fmt::Debug for IngredientPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.container.index, self.resource.raw,)
    }
}

/// Contains all storage that is needed for the database
pub struct DatabaseStorage<DB: StaticDatabase + ?Sized> {
    pub(crate) runtime: Runtime,
    pub(crate) list: DB::StorageList,
    router: StorageRouter<DB>,
}

impl<DB: StaticDatabase + 'static> Default for DatabaseStorage<DB> {
    fn default() -> Self {
        Self::new()
    }
}

impl<DB: StaticDatabase + 'static> DatabaseStorage<DB> {
    pub fn new() -> Self {
        let mut router = StorageRouter::new();
        let list = DB::StorageList::new(&mut router);

        Self {
            runtime: Runtime::new(),
            list,
            router,
        }
    }

    pub fn list(&self) -> &DB::StorageList {
        &self.list
    }

    pub fn list_mut(&mut self) -> &mut DB::StorageList {
        &mut self.list
    }

    pub fn runtime(&self) -> &Runtime {
        &self.runtime
    }

    pub fn get_path<'a>(&self, db: &'a DB, path: ContainerPath) -> &'a dyn Container<DB> {
        self.router.paths[path.index as usize](db)
    }
}

pub trait StorageList<DB> {
    fn new(router: &mut StorageRouter<DB>) -> Self
    where
        Self: Sized;

    fn get_mut<T: 'static>(&mut self) -> Option<&mut T>;

    fn begin(&mut self, current: Revision);
    fn end(&mut self);
}

pub struct StorageRouter<DB: ?Sized> {
    paths: Vec<Route<DB>>,
}

type Route<DB> = fn(&DB) -> &dyn Container<DB>;

impl<DB> StorageRouter<DB> {
    pub(crate) fn new() -> Self {
        Self { paths: Vec::new() }
    }

    pub fn push(&mut self, route: Route<DB>) -> ContainerPath {
        let index = u16::try_from(self.paths.len()).expect("too many containers");
        self.paths.push(route);
        ContainerPath { index }
    }
}

macro_rules! impl_tuple {
    ($($T:ident)*) => {
        #[allow(unused, clippy::unused_unit, non_snake_case)]
        impl<DB, $($T: Storage + 'static),*> StorageList<DB> for ($($T,)*)
            where $( DB: WithStorage<$T> ),*
        {
            fn new(router: &mut StorageRouter<DB>) -> Self {
                $(
                    let $T: $T = $T::new(router);
                )*

                ($($T,)*)
            }

            #[inline]
            fn get_mut<T: 'static>(&mut self) -> Option<&mut T> {
                let ($($T,)*) = self;

                $(
                    if std::any::TypeId::of::<$T>() == std::any::TypeId::of::<T>() {
                        return unsafe { Some(std::mem::transmute::<&mut $T, &mut T>($T)) }
                    }
                )*

                None
            }

            fn begin(&mut self, current: Revision) {
                let ($($T,)*) = self;
                $( $T.begin(current); )*
            }

            fn end(&mut self) {
                let ($($T,)*) = self;
                $( $T.end(); )*
            }
        }
    };
}

impl_tuple!();
impl_tuple!(A);
impl_tuple!(A B);
impl_tuple!(A B C);
impl_tuple!(A B C D);
impl_tuple!(A B C D E);
impl_tuple!(A B C D E F);
impl_tuple!(A B C D E F G);
impl_tuple!(A B C D E F G H);
