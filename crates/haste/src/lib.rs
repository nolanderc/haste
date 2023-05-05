mod arena;
mod cache;

use std::borrow::Borrow;

pub use cache::QueryCache;

pub trait Database {
    fn runtime(&self) -> &Runtime;
}

pub trait Storage: 'static {
    type Database: Database + ?Sized;
}

pub trait WithStorage<S: Storage>: Database {
    fn storage(&self) -> &S;
    fn cast_database(&self) -> &S::Database;
}

pub trait Container: 'static {}

pub trait WithContainer<C: Container>: Storage {
    fn container(&self) -> &C;
}

pub trait Element: 'static {
    type Storage: WithContainer<Self::Container>;
    type Container: Container;
}

pub type ElementDb<T> = <<T as Element>::Storage as Storage>::Database;

pub trait Query: Element {
    type Input: Clone;
    type Output: Clone;

    /// Amount of stack space required by the
    const REQUIRED_STACK: usize = 512 * 1024;

    fn execute(db: &ElementDb<Self>, input: Self::Input) -> Self::Output;
}

pub trait DatabaseExt: Database {
    #[inline]
    fn query<'a, Q: Query>(&'a self, input: Q::Input) -> &'a Q::Output
    where
        Self: WithStorage<Q::Storage>,
        Q::Container: Borrow<QueryCache<Q>>,
        Q::Input: Eq + std::hash::Hash,
    {
        let container = self.storage().container();
        container
            .borrow()
            .get_or_execute(self.cast_database(), input)
    }
}

impl<DB> DatabaseExt for DB where DB: Database {}

#[derive(Default)]
pub struct Runtime {}

impl Runtime {
    const MIN_STACK: usize = 32 * 1024 * 1024;

    #[inline]
    fn execute<Q: Query>(&self, db: &ElementDb<Q>, input: Q::Input) -> Q::Output {
        stacker::maybe_grow(
            Q::REQUIRED_STACK,
            usize::max(Q::REQUIRED_STACK, Self::MIN_STACK),
            || Q::execute(db, input),
        )
    }
}
