use std::{
    any::TypeId,
    cell::Cell,
    fmt::{Debug, Display},
    ptr::NonNull,
};

use crate::{util::CallOnDrop, Database, WithStorage};

/// A type which allows the inner value to be formatted inside some database.
pub struct Adapter<'db, T> {
    db: &'db dyn Database,
    inner: T,
}

thread_local! {
    static FMT_DATABASE: Cell<Option<NonNull<dyn Database + 'static>>> = Cell::new(None);
}

impl<'db, T> Adapter<'db, T> {
    pub fn new(db: &'db dyn Database, inner: T) -> Self {
        Self { db, inner }
    }

    fn enter(&self, f: impl FnOnce() -> std::fmt::Result) -> std::fmt::Result {
        let dyn_db: &dyn Database = self.db;
        let dyn_db: &(dyn Database + 'static) = unsafe { std::mem::transmute(dyn_db) };

        FMT_DATABASE.with(|db| {
            let previous = db.replace(Some(NonNull::from(dyn_db)));
            let _restore_guard = CallOnDrop(|| db.set(previous));
            f()
        })
    }
}

impl<'db, T> Debug for Adapter<'db, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.enter(|| self.inner.fmt(f))
    }
}

impl<'db, T> Display for Adapter<'db, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.enter(|| self.inner.fmt(f))
    }
}

pub struct FmtDatabase<'db, S> {
    raw: &'db dyn Database,
    storage: &'db S,
}

impl<'db, S> Database for FmtDatabase<'db, S>
where
    S: Sync,
{
    fn as_dyn(&self) -> &dyn Database {
        self
    }

    fn runtime(&self) -> &crate::Runtime {
        self.raw.runtime()
    }

    fn storage_list(&self) -> &dyn crate::DynStorageList {
        self.raw.storage_list()
    }

    fn last_changed(&self, dep: crate::Dependency) -> Option<crate::Revision> {
        self.raw.last_changed(dep)
    }
}

impl<'db, S> WithStorage<S> for FmtDatabase<'db, S>
where
    S: crate::Storage + Sync,
{
    fn cast_dyn(&self) -> &<S as crate::Storage>::DynDatabase {
        panic!("cannot cast `FmtDatabase` as another `DynDatabase`")
    }

    fn storage(&self) -> &S {
        self.storage
    }
}

pub fn with_storage<S>(
    f: impl FnOnce(Option<&FmtDatabase<'_, S>>) -> std::fmt::Result,
) -> std::fmt::Result
where
    S: crate::Storage,
{
    FMT_DATABASE.with(|db| {
        let db = db.get().and_then(|ptr| {
            let db = unsafe { ptr.as_ref() };
            let storage = db.dyn_storage(TypeId::of::<S>())?.downcast::<S>()?;
            Some(FmtDatabase { raw: db, storage })
        });
        f(db.as_ref())
    })
}
