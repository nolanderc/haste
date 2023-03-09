#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]
#![allow(clippy::uninlined_format_args)]

use haste::{DatabaseExt, Durability};

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
    fib(db, n - 1).await.wrapping_add(fib(db, n - 2).await)
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
async fn file(_db: &dyn crate::Db, path: &'static str) -> String {
    panic!("file not found: {:?}", path)
}

#[haste::query]
async fn digit_sum(db: &dyn crate::Db, path: &'static str) -> u32 {
    let source = file(db, path).await;
    source.bytes().map(|byte| (byte - b'0') as u32).sum()
}

#[haste::query]
async fn product(db: &dyn crate::Db, files: [&'static str; 2]) -> u32 {
    let a = digit_sum(db, files[0]).await;
    let b = digit_sum(db, files[1]).await;
    a * b
}

fn main() {
    tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .without_time()
        .with_target(false)
        .init();

    let mut db = Database::default();

    let start = std::time::Instant::now();

    db.set_input::<file>("bar", "345".into(), Durability::HIGH);
    db.set_input::<file>("foo", "123".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| {
        scope.block_on(async {
            dbg!(file(db, "foo").await);
            dbg!(product(db, ["foo", "foo"]).await);
            dbg!(product(db, ["bar", "bar"]).await);
        })
    });
    
    db.set_input::<file>("foo", "321".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| {
        scope.block_on(async {
            dbg!(file(db, "foo").await);
            dbg!(product(db, ["foo", "foo"]).await);
            dbg!(product(db, ["bar", "bar"]).await);
        })
    });
    
    db.set_input::<file>("foo", "123".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| {
        scope.block_on(async {
            dbg!(file(db, "foo").await);
            dbg!(product(db, ["foo", "foo"]).await);
            dbg!(product(db, ["bar", "bar"]).await);
        })
    });
    
    db.set_input::<file>("foo", "1234".into(), Durability::LOW);
    haste::scope(&mut db, |scope, db| {
        scope.block_on(async {
            dbg!(file(db, "foo").await);
            dbg!(product(db, ["foo", "foo"]).await);
            dbg!(product(db, ["bar", "bar"]).await);
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
