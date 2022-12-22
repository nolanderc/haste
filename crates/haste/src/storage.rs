use crate::Database;

/// Stores the containers for all ingredients in a database.
pub trait Storage {
    /// The trait object used by ingredients in this storage (eg. `dyn crate::Db`).
    type DynDatabase: Database + ?Sized;

    fn new(router: &mut StorageRouter) -> Self;
}

/// Stores the data requried by a single ingredient
pub trait Container {
    fn new(id: IngredientId) -> Self;
    fn id(&self) -> IngredientId;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct IngredientId {
    storage: u8,
    container: u8,
}

/// Contains all storage that is needed for the database
pub struct DatabaseStorage<DB: HasStorages> {
    storages: DB::StorageList,
}

pub trait HasStorages {
    /// A type containing all the storages used by a database.
    type StorageList: StorageList;
}

pub trait StorageList {
    const LENGTH: usize;
    fn new(router: &mut StorageRouter) -> Self;
}

pub struct StorageRouter {
    max_storages: usize,
    next_id: IngredientId,
}

impl StorageRouter {
    pub(crate) fn new(max_storages: usize) -> Self {
        Self {
            max_storages,
            next_id: IngredientId {
                storage: 0,
                container: 8,
            },
        }
    }
    
    pub(crate) fn end_storage(&mut self) {
        if usize::from(self.next_id.storage) >= self.max_storages {
            panic!("routed more storages than there were available");
        }
        self.next_id.storage += 1;
    }

    pub fn next_ingredient(&mut self) -> IngredientId {
        let id = self.next_id;
        self.next_id.container += 1;
        id
    }
}

impl<DB: HasStorages> Default for DatabaseStorage<DB> {
    fn default() -> Self {
        Self::new()
    }
}

impl<DB: HasStorages> DatabaseStorage<DB> {
    pub fn new() -> Self {
        let mut router = StorageRouter::new(DB::StorageList::LENGTH);

        Self {
            storages: DB::StorageList::new(&mut router),
        }
    }

    pub fn list(&self) -> &DB::StorageList {
        &self.storages
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
