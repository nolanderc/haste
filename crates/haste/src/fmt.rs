mod impls;

pub trait DebugWith<DB: ?Sized> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    fn debug<'a>(&'a self, db: &'a DB) -> DebugAdapter<'a, Self, DB>
    where
        Self: Sized,
    {
        DebugAdapter { value: self, db }
    }
}

pub trait DisplayWith<DB: ?Sized> {
    fn fmt(&self, db: &DB, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
    fn display<'a>(&'a self, db: &'a DB) -> DisplayAdapter<'a, Self, DB> {
        DisplayAdapter { value: self, db }
    }
}

pub struct DebugAdapter<'a, T: ?Sized, DB: ?Sized> {
    value: &'a T,
    db: &'a DB,
}

impl<'a, T, DB> std::fmt::Debug for DebugAdapter<'a, T, DB>
where
    T: DebugWith<DB> + ?Sized,
    DB: ?Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(self.db, f)
    }
}

pub struct DisplayAdapter<'a, T: ?Sized, DB: ?Sized> {
    value: &'a T,
    db: &'a DB,
}

impl<'a, T, DB> std::fmt::Display for DisplayAdapter<'a, T, DB>
where
    T: DisplayWith<DB> + ?Sized,
    DB: ?Sized,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(self.db, f)
    }
}

/// Uses method/trait priority to call [`std::fmt::Debug`] if a field does not implement
/// [`DebugWith`].
#[doc(hidden)]
pub mod macro_helper {
    use std::marker::PhantomData;

    pub trait DebugFallback<T: std::fmt::Debug, DB: ?Sized> {
        fn haste_debug<'a, 'b: 'a>(value: &'a T, _db: &'b DB) -> &'a dyn std::fmt::Debug {
            value
        }
    }

    impl<T: std::fmt::Debug, DB: ?Sized, A> DebugFallback<T, DB> for A {}

    pub struct HasteDebug<T, DB: ?Sized>(PhantomData<(T, DB)>);

    impl<T, DB: ?Sized> HasteDebug<T, DB>
    where
        T: super::DebugWith<DB>,
    {
        pub fn haste_debug<'a, 'b: 'a>(value: &'a T, db: &'a DB) -> super::DebugAdapter<'a, T, DB> {
            value.debug(db)
        }
    }
}
