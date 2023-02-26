#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![allow(clippy::uninlined_format_args)]

use std::sync::Arc;

use haste::DatabaseExt;

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    storage: haste::DatabaseStorage<Self>,
}

impl Db for Database {}

#[haste::storage]
pub struct Storage(Text, fib, Person, cyclic, file, digit_sum);

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
#[clone]
#[cycle(cyclic_cycle)]
async fn cyclic(db: &dyn crate::Db, n: u32) -> u32 {
    match n {
        0..=3 => cyclic(db, n + 1).await,
        _ => cyclic(db, 0).await,
    }
}

async fn cyclic_cycle(_db: &dyn crate::Db, _cycle: haste::Cycle, _n: u32) -> u32 {
    123
}

#[haste::query]
#[input]
async fn file(_db: &dyn crate::Db, path: Arc<str>) -> String {
    panic!("file not found: {:?}", path)
}

#[haste::query]
async fn digit_sum(db: &dyn crate::Db, path: Arc<str>) -> u32 {
    let source = file(db, path).await;
    source.bytes().map(|byte| (byte - b'0') as u32).sum()
}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();

    db.set_input::<file>("foo".into(), "123".into());
    haste::scope(&mut db, |scope, db| {
        scope.block_on(async {
            dbg!(file(db, "foo".into()).await);
            dbg!(digit_sum(db, "foo".into()).await);
        })
    });

    db.set_input::<file>("foo".into(), "124".into());
    haste::scope(&mut db, |scope, db| {
        scope.block_on(async {
            dbg!(file(db, "foo".into()).await);
            dbg!(digit_sum(db, "foo".into()).await);
        })
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
