#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![allow(clippy::uninlined_format_args)]

use haste::Durability;

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    storage: haste::DatabaseStorage<Self>,
}

impl crate::Db for Database {}

#[haste::storage]
pub struct Storage(Text, fib, Person, cyclic, file, digit_sum, product);

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
#[clone]
async fn fib(db: &dyn crate::Db, n: u64) -> u64 {
    if n < 2 {
        return n;
    }

    let a = fib(db, n - 1);
    let b = fib(db, n - 2);
    a.await.wrapping_add(b.await)
}

#[haste::query]
#[clone]
#[cycle(cyclic_cycle)]
async fn cyclic(db: &dyn crate::Db, n: u32) -> u32 {
    match n {
        0..=100 => cyclic(db, n + 1).await,
        _ => cyclic(db, 0).await,
    }
}

async fn cyclic_cycle(_db: &dyn crate::Db, _cycle: haste::Cycle, _n: u32) -> u32 {
    123
}

#[haste::query]
#[input]
async fn file(_db: &dyn crate::Db, path: &'static str) -> String {
    panic!("file not found: {:?}", path)
}

#[haste::query]
async fn digit_sum(db: &dyn crate::Db, path: &'static str) -> u32 {
    let source = file(db, path).await;
    source.bytes().map(|byte| (byte - b'0') as u32).sum()
}

#[haste::query]
#[clone]
async fn product(db: &dyn crate::Db, files: [&'static str; 2]) -> u32 {
    let a = digit_sum(db, files[0]).await;
    let b = digit_sum(db, files[1]).await;
    a * b
}

fn time<T>(f: impl FnOnce() -> T)
where
    T: std::fmt::Debug,
{
    let start = std::time::Instant::now();
    let output = f();
    let duration = start.elapsed();
    eprintln!("time: {:?} = {:?}", duration, output);
}

#[allow(clippy::disallowed_names)]
async fn run(db: &dyn crate::Db) -> (&String, u32, u32, u32) {
    let foo = file(db, "foo");
    let foo_foo = product(db, ["foo", "foo"]);
    let bar_bar = product(db, ["bar", "bar"]);
    let foo_bar = product(db, ["foo", "bar"]);
    (foo.await, foo_foo.await, bar_bar.await, foo_bar.await)
}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();

    file::set(&mut db, "foo", "123".into(), Durability::LOW);
    file::set(&mut db, "bar", "345".into(), Durability::HIGH);
    haste::scope(&mut db, |scope, db| time(|| scope.block_on(run(db))));

    file::set(&mut db, "foo", "321".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| time(|| scope.block_on(run(db))));

    file::set(&mut db, "foo", "123".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| time(|| scope.block_on(run(db))));

    file::set(&mut db, "foo", "1234".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| time(|| scope.block_on(run(db))));

    eprintln!("total time: {:?}", start.elapsed());

    let a = Text::insert(&db, TextData("hello".into()));
    let b = Text::insert(&db, TextData("hello".into()));
    assert_eq!(a, b);
    assert_eq!(a.lookup(&db).0, "hello");
    assert_eq!(b.lookup(&db).0, "hello");

    let name = Text::insert(&db, TextData("John".into()));
    let person = Person::insert(&db, PersonData { name, age: 37 });
    assert_eq!(person.name(&db), name);
    assert_eq!(person.age(&db), 37);

    eprintln!("done");
}
