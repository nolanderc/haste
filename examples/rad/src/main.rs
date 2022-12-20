use haste::Query;

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
pub struct Storage(Text, Fib);

#[haste::intern]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Text(String);

struct Fib;

impl haste::Ingredient for Fib {
    type Container = ();

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

        Fib::execute(db, input - 1) + Fib::execute(db, input - 2)
    }
}

fn main() {
    let db = Database::default();

    for i in 0..10 {
        eprintln!("fib {:2} = {}", i, Fib::execute(&db, i));
    }

    let a = Text::new(&db, "hello".into());
    let b = Text::new(&db, "hello".into());
    assert_eq!(a, b);
    assert_eq!(a.get(&db), "hello");
    assert_eq!(b.get(&db), "hello");

    eprintln!("done");
}
