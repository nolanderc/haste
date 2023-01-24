#![feature(type_alias_impl_trait)]

use std::num::NonZeroU32;

mod token;

pub trait Db: haste::Database + haste::WithStorage<Storage> + Sync {}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: haste::DatabaseStorage<Self>,
}

impl Db for Database {}

#[haste::storage]
pub struct Storage(Text, fib, Person, smallest_factor, factors);

#[haste::intern(Text)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TextData(String);

#[haste::intern(Person)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PersonData {
    #[clone]
    name: Text,
    #[clone]
    age: u32,
}

#[haste::query]
async fn fib(db: &dyn crate::Db, n: u64) -> u64 {
    if n < 2 {
        return n;
    }

    fib::prefetch(db, n - 1);
    fib::prefetch(db, n - 2);

    let a = Box::pin(fib(db, n - 1));
    let b = Box::pin(fib(db, n - 2));

    let out = a.await + b.await;
    out
}

#[haste::query]
async fn smallest_factor(_db: &dyn crate::Db, n: u32) -> Option<NonZeroU32> {
    let mut i = 2;
    // we intentionally made this an `O(n)` algorithm
    while i * i <= n {
        if n % i == 0 {
            return NonZeroU32::new(i as u32);
        }
        i += 1;
    }
    None
}

#[haste::query]
async fn factors(db: &dyn crate::Db, n: u32) -> Vec<u32> {
    let mut rest = n;
    let mut factors = Vec::with_capacity(4);
    while let Some(factor) = smallest_factor(db, rest).await {
        rest /= factor.get();
        factors.push(factor.get());
    }
    if rest > 1 {
        factors.push(rest);
    }
    factors
}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();

    // a scope is a region of code within which we can safely spawn tasks
    haste::scope(&mut db, |db| {
        let max = 1_000_000;
        for i in 0..max {
            factors::prefetch(db, i);
        }

        let mut factorings = Vec::with_capacity(max as usize);
        for i in 0..max {
            let out = db.runtime.block_on(factors(db, i));
            factorings.push((i, out));
        }
    });

    let duration = start.elapsed();
    dbg!(duration);

    let a = Text::new(&db, TextData("hello".into()));
    let b = Text::new(&db, TextData("hello".into()));
    assert_eq!(a, b);
    assert_eq!(a.get(&db).0, "hello");
    assert_eq!(b.get(&db).0, "hello");

    let name = Text::new(&db, TextData("John".into()));
    let person = Person::new(&db, PersonData { name, age: 37 });
    assert_eq!(person.name(&db), name);
    assert_eq!(person.age(&db), 37);

    eprintln!("done");
}
