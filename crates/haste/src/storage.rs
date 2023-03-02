use crate::{Database, Dependency, DynQueryCache, Revision, Runtime, StaticDatabase, WithStorage};

/// Stores the containers for all ingredients in a database.
pub trait Storage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized + WithStorage<Self>;

    /// Initialize the storage within some database.
    fn new<DB: WithStorage<Self>>(router: &mut StorageRouter<DB>) -> Self;
}

/// Stores the data requried by a single ingredient
pub trait Container<DB: ?Sized>: 'static + Sync {
    fn path(&self) -> ContainerPath;

    fn fmt(&self, id: crate::Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn as_query_cache(&self) -> Option<&dyn DynQueryCache<DB>> {
        None
    }

    fn last_changed(&self, dep: Dependency) -> Option<Revision>;
}

pub trait MakeContainer {
    fn new(path: ContainerPath) -> Self;
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
