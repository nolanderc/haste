use crate::{Database, WithStorage};

/// Stores the containers for all ingredients in a database.
pub trait Storage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized + WithStorage<Self>;

    fn new(router: &mut StorageRouter) -> Self;
}

/// Stores the data requried by a single ingredient
pub trait Container {
    fn new(path: IngredientPath) -> Self;
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
    const LENGTH: usize;
    fn new(router: &mut StorageRouter) -> Self;
}

pub struct StorageRouter {
    max_storages: usize,
    next_path: IngredientPath,
}

impl StorageRouter {
    pub(crate) fn new(max_storages: usize) -> Self {
        Self {
            max_storages,
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
        let mut router = StorageRouter::new(DB::StorageList::LENGTH);

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

macro_rules! ignore {
    ($($tt:tt)*) => {
        ()
    };
}

macro_rules! impl_tuple {
    ($($T:ident)*) => {
        impl<$($T: Storage),*> StorageList for ($($T,)*) {
            const LENGTH: usize = <[()]>::len(&[$(ignore!($T)),*]);

            #[allow(unused, clippy::unused_unit, non_snake_case)]
            fn new(router: &mut StorageRouter) -> Self {
                $(
                    let $T: $T = $T::new(router);
                    router.end_storage();
                )*

                ($($T,)*)
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
