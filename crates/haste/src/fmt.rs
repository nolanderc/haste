use std::{
    cell::Cell,
    fmt::{Debug, Display},
    ptr::NonNull,
};

use crate::{util::CallOnDrop, Database, LastChangeFuture, WithStorage};

/// A type which allows the inner value to be formatted inside some database.
pub struct Adapter<'db, T> {
    db: &'db dyn Database,
    inner: T,
}

thread_local! {
    static FMT_DATABASE: Cell<Option<NonNull<dyn Database>>> = Cell::new(None);
}

/// Enter a scope within which it is possible access the database through `with_storage`
pub fn scope<T>(db: &dyn Database, f: impl FnOnce() -> T) -> T {
    // temporarily extend the lifetime of the database
    //
    // SAFETY: we make sure that the reference does not outlive this function.
    let dyn_db: &(dyn Database + 'static) = unsafe { std::mem::transmute(db) };

    FMT_DATABASE.with(|db| {
        let previous = db.replace(Some(NonNull::from(dyn_db)));
        let _restore_guard = CallOnDrop(|| db.set(previous));
        f()
    })
}

impl<'db, T> Adapter<'db, T> {
    pub fn new(db: &'db dyn Database, inner: T) -> Self {
        Self { db, inner }
    }

    fn enter(&self, f: impl FnOnce() -> std::fmt::Result) -> std::fmt::Result {
        scope(self.db, f)
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

pub fn wrap(
    db: &dyn Database,
    f: &mut std::fmt::Formatter<'_>,
    func: impl Fn(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
) -> std::fmt::Result {
    let adapter = Adapter::new(db, crate::util::fmt::from_fn(func));
    Display::fmt(&adapter, f)
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

    fn last_change(&self, dep: crate::Dependency) -> LastChangeFuture {
        self.raw.last_change(dep)
    }

    fn cycle_strategy(&self, path: crate::ContainerPath) -> crate::CycleStrategy {
        self.raw.cycle_strategy(path)
    }

    fn set_cycle(&self, path: crate::IngredientPath, cycle: crate::Cycle) {
        self.raw.set_cycle(path, cycle)
    }

    fn fmt_index(
        &self,
        path: crate::IngredientPath,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.raw.fmt_index(path, f)
    }

    fn get_info(&self, path: crate::IngredientPath) -> Option<crate::IngredientInfo> {
        self.raw.get_info(path)
    }

    fn get_storage_any(&self, id: std::any::TypeId) -> Option<&dyn std::any::Any> {
        self.raw.get_storage_any(id)
    }
}

impl<'db, S> WithStorage<S> for FmtDatabase<'db, S>
where
    S: crate::Storage + Sync,
{
    fn cast_dyn(&self) -> &S::DynDatabase {
        unimplemented!(
            "cannot cast `FmtDatabase` to the required `{}`",
            std::any::type_name::<S::DynDatabase>()
        )
    }

    fn storage(&self) -> (&S, &crate::Runtime) {
        (self.storage, self.raw.runtime())
    }

    fn storage_with_db(&self) -> (&S, &crate::Runtime, &S::DynDatabase) {
        (self.storage, self.raw.runtime(), self.cast_dyn())
    }

    fn storage_mut(&mut self) -> (&mut S, &mut crate::Runtime) {
        unreachable!()
    }
}

pub fn with_storage<S>(
    f: impl FnOnce(Option<&dyn WithStorage<S>>) -> std::fmt::Result,
) -> std::fmt::Result
where
    S: crate::Storage + Sync + 'static,
{
    FMT_DATABASE.with(|db| {
        let db = db.get().and_then(|raw| {
            let raw = unsafe { raw.as_ref() };
            let storage = raw.get_storage::<S>()?;
            Some(FmtDatabase { raw, storage })
        });
        f(db.as_ref().map(|db| db as &_))
    })
}
