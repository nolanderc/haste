#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]

use std::num::NonZeroU32;

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: haste::DatabaseStorage<Self>,
}

impl Db for Database {}

#[haste::storage]
pub struct Storage(
    Text,
    fib,
    Person,
    smallest_factor,
    factors,
    next_prime,
    cyclic,
    partner,
);

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
    fib(db, n - 1).await + fib(db, n - 2).await
}

#[haste::query]
async fn smallest_factor(_db: &dyn crate::Db, n: u32) -> Option<NonZeroU32> {
    let mut i = 2;
    // we intentionally made this an `O(n)` algorithm
    while i * i <= n {
        if n % i == 0 {
            return NonZeroU32::new(i);
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

#[haste::query]
#[clone]
async fn next_prime(db: &dyn crate::Db, n: u32) -> u32 {
    next_prime::prefetch(db, n + 1);

    if smallest_factor(db, n + 1).await.is_none() {
        return n + 1;
    }

    next_prime(db, n + 1).await
}

#[haste::query]
#[clone]
#[cycle(cyclic_cycle)]
async fn cyclic(db: &dyn crate::Db, n: u32) -> u32 {
    match n {
        0..=3 => partner(db, n).await,
        _ => cyclic(db, 0).await,
    }
}

async fn cyclic_cycle(_db: &dyn crate::Db, _cycle: haste::Cycle, _n: u32) -> u32 {
    123
}

#[haste::query]
#[clone]
async fn partner(db: &dyn crate::Db, n: u32) -> u32 {
    cyclic(db, n + 1).await + 1
}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();

    // a scope is a region of code within which we can safely spawn tasks
    haste::scope(&mut db, |scope, db| {
        // let max = 10;
        //
        // std::thread::scope(|threads| {
        //     let signal = haste::util::DropSignal::new();
        //
        //     for _ in 0..8 {
        //         let signal = signal.wait();
        //         threads.spawn(|| scope.block_on(signal));
        //     }
        //
        //     scope.block_on(async {
        //         for i in 0..max {
        //             next_prime(db, i).await;
        //         }
        //     });
        // })

        dbg!(scope.block_on(partner(db, 5)));
    });

    let duration = start.elapsed();
    eprintln!("time: {duration:?}");

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
