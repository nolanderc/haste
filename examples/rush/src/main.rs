use haste::DatabaseExt;

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

impl haste::WithStorage<Storage> for Database {
    fn storage(&self) -> &Storage {
        &self.storage
    }

    fn cast_database(&self) -> &<Storage as haste::Storage>::Database {
        self
    }
}

fn main() {
    let db = Database::default();

    let start = std::time::Instant::now();
    let count = 100000;
    for i in (0..=count).rev() {
        db.query::<Fib>(i as _);
    }
    let duration = start.elapsed();
    eprintln!("real: {:?} ({:?})", duration, duration / count as u32);
}

#[derive(Default)]
struct Storage {
    fib: <Fib as haste::Element>::Container,
}

impl haste::Storage for Storage {
    type Database = Database;
}

impl haste::WithContainer<<Fib as haste::Element>::Container> for Storage {
    fn container(&self) -> &<Fib as haste::Element>::Container {
        &self.fib
    }
}

struct Fib;

impl haste::Element for Fib {
    type Storage = Storage;
    type Container = haste::QueryCache<Self>;
}

impl haste::Query for Fib {
    type Input = u64;
    type Output = u64;

    fn execute(db: &haste::ElementDb<Self>, input: Self::Input) -> Self::Output {
        if input < 2 {
            return input;
        }

        db.query::<Fib>(input - 1)
            .wrapping_add(*db.query::<Fib>(input - 2))
    }
}
