use crate::{Database, DynQueryCache, WithStorage};

/// Stores the containers for all ingredients in a database.
pub trait Storage: DynStorage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized + WithStorage<Self>;

    fn new(router: &mut StorageRouter) -> Self;
}

pub trait DynStorage: std::any::Any {
    fn dyn_container_path(&self, path: ContainerPath) -> Option<&dyn DynContainer>;
}

impl dyn DynStorage {
    pub(crate) fn downcast<S: 'static>(&self) -> Option<&S> {
        if self.type_id() == std::any::TypeId::of::<S>() {
            // SAFETY: `self` and `S` are of the same type:
            Some(unsafe { &*(self as *const _ as *const S) })
        } else {
            None
        }
    }
}

/// Stores the data requried by a single ingredient
pub trait Container: DynContainer {
    fn new(path: ContainerPath) -> Self;
}

pub trait DynContainer: 'static {
    fn path(&self) -> ContainerPath;

    fn fmt(&self, id: crate::Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let path = IngredientPath {
            container: self.path(),
            resource: id,
        };
        write!(f, "{:?}", path)
    }

    fn as_query_cache(&self) -> Option<&dyn DynQueryCache> {
        None
    }
}

/// Identifies a single container in a database
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContainerPath {
    pub storage: u8,
    pub container: u8,
}

impl ContainerPath {
    pub(crate) fn encode_u16(self) -> u16 {
        (self.storage as u16) << 8 | (self.container as u16)
    }

    pub(crate) fn decode_u16(x: u16) -> Self {
        Self {
            storage: (x >> 8) as u8,
            container: x as u8,
        }
    }
}

/// Identifies a single resource in a database
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IngredientPath {
    pub container: ContainerPath,
    pub resource: crate::Id,
}

impl std::fmt::Debug for IngredientPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.container.encode_u16(), self.resource.raw,)
    }
}

/// Contains all storage that is needed for the database
pub struct DatabaseStorage<DB: WithStorages> {
    storages: DB::StorageList,
}

pub trait WithStorages {
    /// A type containing all the storages used by a database.
    type StorageList: StorageList;
}

pub trait StorageList {
    fn new(router: &mut StorageRouter) -> Self
    where
        Self: Sized;

    fn get(&self, id: std::any::TypeId) -> Option<&dyn DynStorage>;
    fn get_path(&self, path: ContainerPath) -> Option<&dyn DynStorage>;
}

pub struct StorageRouter {
    max_storages: usize,
    next_path: ContainerPath,
}

impl StorageRouter {
    pub(crate) fn new() -> Self {
        Self {
            max_storages: u8::MAX as usize,
            next_path: ContainerPath {
                storage: 0,
                container: 0,
            },
        }
    }

    pub(crate) fn end_storage(&mut self) {
        if usize::from(self.next_path.storage) >= self.max_storages {
            panic!("routed more storages than there were available");
        }
        self.next_path.storage += 1;
    }

    pub fn next_container(&mut self) -> ContainerPath {
        let id = self.next_path;
        self.next_path.container += 1;
        id
    }
}

impl<DB: WithStorages> Default for DatabaseStorage<DB> {
    fn default() -> Self {
        Self::new()
    }
}

impl<DB: WithStorages> DatabaseStorage<DB> {
    pub fn new() -> Self {
        let mut router = StorageRouter::new();

        Self {
            storages: DB::StorageList::new(&mut router),
        }
    }

    pub fn list(&self) -> &DB::StorageList {
        &self.storages
    }

    pub fn list_mut(&mut self) -> &mut DB::StorageList {
        &mut self.storages
    }
}

macro_rules! impl_tuple {
    ($($T:ident)*) => {
        #[allow(unused, clippy::unused_unit, non_snake_case)]
        impl<$($T: Storage),*> StorageList for ($($T,)*) {
            fn new(router: &mut StorageRouter) -> Self {
                $(
                    let $T: $T = $T::new(router);
                    router.end_storage();
                )*

                ($($T,)*)
            }

            fn get(&self, id: std::any::TypeId) -> Option<&dyn DynStorage> {
                let ($($T,)*) = self;

                $(
                    if std::any::TypeId::of::<$T>() == id {
                        return Some($T)
                    }
                )*

                None
            }

            fn get_path(&self, path: ContainerPath) -> Option<&dyn DynStorage> {
                let ($($T,)*) = self;

                let mut i = 0;

                $(
                    if i == path.storage {
                        return Some($T);
                    }
                    i += 1;
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
