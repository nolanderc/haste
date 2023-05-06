use haste::DatabaseExt;

#[derive(Default)]
struct Database {
    storage: haste::DatabaseStorage<Self>,
}

impl haste::StaticDatabase for Database {
    type StorageList = (Storage,);
}

impl haste::Database for Database {
    fn runtime(&self) -> &haste::Runtime {
        self.storage.runtime()
    }

    fn runtime_mut(&mut self) -> &mut haste::Runtime {
        self.storage.runtime_mut()
    }
}

impl haste::WithStorage<Storage> for Database {
    fn storage(&self) -> &Storage {
        &self.storage.storages().0
    }

    fn cast_database(&self) -> &<Storage as haste::Storage>::Database {
        self
    }
}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();
    let count = 100000;
    db.scope(|db| {
        for i in (0..=count).rev() {
            db.query::<Fib>(i as _);
        }
    });
    let duration = start.elapsed();
    eprintln!("real: {:?} (avg: {:?})", duration, duration / count as u32);
}

struct Storage {
    fib: <Fib as haste::Element>::Container,
}

impl haste::Storage for Storage {
    type Database = Database;

    fn new<DB>(router: &mut haste::StorageRouter<DB>) -> Self
    where
        DB: haste::WithStorage<Self>,
    {
        Self {
            fib: <<Fib as haste::Element>::Container as haste::Container>::new(
                router.push(|db| &db.storage().fib),
            ),
        }
    }
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

        let a = *db.query::<Fib>(input - 1);
        let b = *db.query::<Fib>(input - 2);
        a.wrapping_add(b)
    }
}
