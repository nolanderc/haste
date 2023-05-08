use std::sync::atomic::AtomicU32;

use haste::{DatabaseExt as _, DebugWith};

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
        let text = Text::insert(db, TextData("hello".into()));
        assert_eq!(format!("{:?}", text.debug(db)), "\"hello\"");

        let n = 2000;
        let threads = 8;

        std::thread::scope(|scope| {
            scope.spawn(|| {
                for _ in 0..threads {
                    binom(db, n, n / 2);
                }
            });
        });
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

#[haste::query(clone)]
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

#[haste::query(clone)]
fn binom(db: &dyn Db, n: u64, k: u64) -> u64 {
    COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

    if k == 0 || k >= n {
        return 1;
    }

    let a = binom::spawn(db, n - 1, k);
    let b = binom::spawn(db, n - 1, k - 1);
    a.join().wrapping_add(b.join())
}

#[haste::intern(Text)]
#[derive(PartialEq, Eq, Hash)]
struct TextData(String);

impl std::fmt::Debug for TextData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(haste::DebugWith)]
struct Foo {
    a: u32,
    b: Text,
}
