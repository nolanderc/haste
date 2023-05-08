use std::sync::atomic::AtomicU32;

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
    db.scope(|db| {
        let n = 2000;
        binom(db, n, n / 2);
    });
    let duration = start.elapsed();
    let count = COUNT.load(std::sync::atomic::Ordering::Relaxed);
    eprintln!(
        "real: {:?} (avg: {:?}, count: {})",
        duration,
        duration / count,
        count
    );
}

#[haste::storage]
struct Storage(fib, binom, Text);

#[haste::query]
fn fib(db: &dyn Db, n: u64) -> u64 {
    COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    if n < 2 {
        return n;
    }

    let a = fib(db, n - 1);
    let b = fib(db, n - 2);
    a.wrapping_add(b)
}

static COUNT: AtomicU32 = AtomicU32::new(0);

#[haste::query]
fn binom(db: &dyn Db, n: u64, k: u64) -> u64 {
    COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    if k == 0 || k >= n {
        return 1;
    }

    let a = binom(db, n - 1, k);
    let b = binom(db, n - 1, k - 1);
    a.wrapping_add(b)
}

#[haste::intern(Text)]
#[derive(Debug, PartialEq, Eq, Hash)]
struct TextData(String);
