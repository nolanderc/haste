use haste::DatabaseExt as _;

#[haste::database(Storage)]
#[derive(Default)]
struct Database {
    storage: haste::DatabaseStorage<Self>,
}

trait Db: haste::WithStorage<Storage> {}

impl Db for Database {}

fn main() {
    let mut db = Database::default();

    let start = std::time::Instant::now();
    let count = 100000;
    db.scope(|db| {
        for i in (0..=count).rev() {
            fib(db, i as _);
        }
    });
    let duration = start.elapsed();
    eprintln!("real: {:?} (avg: {:?})", duration, duration / count as u32);
}

#[haste::storage]
struct Storage(fib, Text);

#[haste::query]
fn fib(db: &dyn Db, n: u64) -> u64 {
    if n < 2 {
        return n;
    }

    let a = fib(db, n - 1);
    let b = fib(db, n - 2);
    a.wrapping_add(b)
}

#[haste::intern(Text)]
#[derive(Debug, PartialEq, Eq, Hash)]
struct TextData(String);
