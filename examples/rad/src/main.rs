pub trait Db: haste::Database + haste::HasStorage<Storage> {}

#[derive(Default)]
pub struct Database {
    runtime: haste::Runtime,
    storage: Storage,
}

impl haste::Database for Database {
    fn runtime(&self) -> &haste::Runtime {
        &self.runtime
    }
}

impl Db for Database {}
impl haste::HasStorage<Storage> for Database {
    #[inline(always)]
    fn storage(&self) -> &Storage {
        &self.storage
    }

    #[inline(always)]
    fn as_dyn(&self) -> &<Storage as haste::Storage>::DynDatabase {
        self
    }
}

#[haste::storage]
#[derive(Default)]
pub struct Storage(Text, fib, Person, fact);

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
fn fib(db: &dyn crate::Db, n: u64) -> u64 {
    if n < 2 {
        return n;
    }
    fib(db, n - 1) + fib(db, n - 2)
}

fn main() {
    let db = Database::default();

    for i in 0..10 {
        eprintln!("fib {} = {}", i, fib(&db, i));
    }

    let a = Text::new(&db, TextData("hello".into()));
    let b = Text::new(&db, TextData("hello".into()));
    assert_eq!(a, b);
    assert_eq!(a.get(&db), "hello");
    assert_eq!(b.get(&db), "hello");

    let name = Text::new(&db, TextData("John".into()));
    let person = Person::new(&db, PersonData { name, age: 37 });
    assert_eq!(person.name(&db), name);
    assert_eq!(person.age(&db), 37);

    eprintln!("done");
}

#[haste::query]
fn fact(db: &dyn crate::Db, n: u64) -> u64 {
    if n == 0 {
        return 1;
    }
    fact(db, n - 1) * n
}
