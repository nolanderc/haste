#![feature(type_alias_impl_trait)]

mod token;

pub trait Db: haste::Database + haste::WithStorage<Storage> {}

#[haste::database(Storage)]
#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: haste::DatabaseStorage<Self>,
}

impl Db for Database {}

#[haste::storage]
pub struct Storage(Text, fib, Person);

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

    let a = Box::pin(fib(db, n - 1));
    let b = Box::pin(fib(db, n - 2));
    a.await + b.await
}

fn main() {
    let db = Database::default();

    for i in 0..20 {
        eprintln!("fib {} = {}", i, pollster::block_on(fib(&db, i)));
    }

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
