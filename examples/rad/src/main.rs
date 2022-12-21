use haste::{DatabaseExt, Query};

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
pub struct Storage(Text, Fib, Person);

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

struct Fib;

impl haste::Ingredient for Fib {
    type Container = haste::query_cache::HashQueryCache<Self>;

    type Storage = crate::Storage;

    type Database = dyn crate::Db;
}

impl haste::Query for Fib {
    type Input = u64;

    type Output = u64;

    #[allow(clippy::only_used_in_recursion)]
    fn execute(db: &Self::Database, input: Self::Input) -> Self::Output {
        if input < 2 {
            return input;
        }
        db.execute_cached::<Fib>(input - 1) + db.execute_cached::<Fib>(input - 2)
    }
}

fn main() {
    let db = Database::default();

    for i in 0..30 {
        let result = Fib::execute(&db, i);
        eprintln!("fib {} = {}", i, result);
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
