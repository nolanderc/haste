#![feature(type_alias_impl_trait)]
#![feature(trivial_bounds)]

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: haste::DatabaseStorage<Self>,
}

impl Db for Database {}

#[haste::storage]
pub struct Storage(Text, fib, Person, cyclic, cyclic_partner);

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
        0..=3 => cyclic_partner(db, n).await,
        _ => cyclic(db, 0).await,
    }
}

async fn cyclic_cycle(_db: &dyn crate::Db, _cycle: haste::Cycle, _n: u32) -> u32 {
    123
}

#[haste::query]
#[clone]
async fn cyclic_partner(db: &dyn crate::Db, n: u32) -> u32 {
    cyclic(db, n + 1).await + 1
}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();

    // a scope is a region of code within which we can safely spawn tasks
    haste::scope(&mut db, |scope, db| {
        dbg!(scope.block_on(cyclic_partner(db, 5)));
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
