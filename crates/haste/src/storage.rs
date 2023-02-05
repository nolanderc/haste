use crate::{Database, WithStorage};

/// Stores the containers for all ingredients in a database.
pub trait Storage: DynStorage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized + WithStorage<Self>;

    fn new(router: &mut StorageRouter) -> Self;
}

pub trait DynStorage: std::any::Any {}

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
    fn new(path: IngredientPath) -> Self;
}

pub trait DynContainer: 'static {
    fn path(&self) -> IngredientPath;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IngredientPath {
    storage: u8,
    container: u8,
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
    fn get_path(&self, path: IngredientPath) -> Option<&dyn DynStorage>;
}

pub struct StorageRouter {
    max_storages: usize,
    next_path: IngredientPath,
}

impl StorageRouter {
    pub(crate) fn new() -> Self {
        Self {
            max_storages: u8::MAX as usize,
            next_path: IngredientPath {
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

    pub fn next_ingredient(&mut self) -> IngredientPath {
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

            fn get_path(&self, path: IngredientPath) -> Option<&dyn DynStorage> {
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
