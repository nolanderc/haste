use std::sync::{
    atomic::{AtomicU64, Ordering::Relaxed},
    Mutex, MutexGuard,
};

use hashbrown::raw::RawTable;

pub struct ShardLookup {
    shards: Vec<Mutex<Shard>>,
    indices: IndexAllocator,
}

struct IndexAllocator {
    next: AtomicU64,
}

impl IndexAllocator {
    fn allocate(&self, count: u64) -> std::ops::Range<u32> {
        let start = self.next.fetch_add(count, Relaxed);
        let end = start + count;

        let max = u64::from(u32::MAX);
        if end > max {
            self.next.store(max + 1, Relaxed);
            panic!("exhausted IDs")
        }

        start as u32..end as u32
    }
}

struct Shard {
    entries: RawTable<u32>,
    reserved: std::ops::Range<u32>,
}

impl Default for ShardLookup {
    fn default() -> Self {
        let thread_count = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        let shard_count = (4 * thread_count).next_power_of_two();

        let mut shards = Vec::new();
        shards.resize_with(shard_count, || Mutex::new(Shard::new()));

        Self {
            shards,
            indices: IndexAllocator {
                next: AtomicU64::new(0),
            },
        }
    }
}

impl Shard {
    fn new() -> Self {
        Self {
            entries: RawTable::new(),
            reserved: 0..0,
        }
    }
}

impl ShardLookup {
    /// Get the index of a value, possibly by inserting it into some other collection.
    ///
    /// `eq` determines if the inserted value is equal to the one at the given index. The index is
    /// guaranteed to be protected by a read lock.
    ///
    /// `hasher` determines the hash of the value at the given index. The index is guaranteed to be
    /// protected by a write lock.
    pub fn get_or_insert(
        &self,
        hash: u64,
        eq: impl Fn(u32) -> bool,
        hasher: impl Fn(u32) -> u64,
    ) -> ShardResult {
        let shards = &self.shards;

        let shard = &shards[shard_index(hash, shards.len())];
        let mut shard = shard.lock().unwrap();

        if let Some(&old) = shard.entries.get(hash, |index| eq(*index)) {
            return ShardResult::Cached(old);
        }

        let index = if let Some(index) = shard.reserved.next() {
            index
        } else {
            shard.reserved = self.indices.allocate(1024);
            shard.reserved.next().unwrap()
        };

        shard.entries.insert(hash, index, |index| hasher(*index));

        ShardResult::Insert(index, WriteGuard(shard))
    }
}

pub enum ShardResult<'a> {
    Cached(u32),
    Insert(u32, WriteGuard<'a>),
}

pub struct WriteGuard<'a>(MutexGuard<'a, Shard>);

fn shard_index(hash: u64, shard_count: usize) -> usize {
    let shard_bits = shard_count.trailing_zeros();
    // hashbrown uses the top 7 bits
    let top_bits = hash >> (64 - 7 - shard_bits);
    (top_bits as usize) & (shard_count - 1)
}
