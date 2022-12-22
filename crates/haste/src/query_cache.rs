use std::{cell::UnsafeCell, hash::Hash, mem::MaybeUninit};

use parking_lot::RwLockUpgradableReadGuard;

use crate::{arena::RawArena, shard_map::ShardMap, Database, Dependency, Id, IngredientId, Query};

pub trait QueryCache<Q: Query> {
    fn get_or_execute<'a>(&'a self, db: &Q::Database, input: Q::Input) -> &'a Q::Output;
}

pub struct HashQueryCache<Q: Query> {
    id: IngredientId,
    entries: ShardMap<Q::Input, InputSlot>,
    outputs: RawArena<UnsafeCell<MaybeUninit<OutputSlot<Q::Output>>>>,
}

enum InputSlot {
    Progress(QueryProgress),
    Done(Id),
}

struct OutputSlot<T> {
    value: T,
    dependencies: Vec<Dependency>,
}

struct QueryProgress {}

impl QueryProgress {
    fn new() -> Self {
        Self {}
    }
}

impl<Q: Query> crate::Container for HashQueryCache<Q> {
    fn new(id: IngredientId) -> Self {
        Self {
            id,
            entries: Default::default(),
            outputs: Default::default(),
        }
    }

    fn id(&self) -> IngredientId {
        self.id
    }
}

impl<Q: Query> QueryCache<Q> for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn get_or_execute<'a>(
        &'a self,
        db: &<Q>::Database,
        input: <Q as Query>::Input,
    ) -> &'a <Q as Query>::Output {
        let runtime = db.runtime();

        // only hash the input once:
        let hash = self.entries.hash(&input);

        let id = match self.get_or_reserve_slot(input, hash) {
            // the query has run before, so we reuse the cached output
            Ok(id) => id,
            // this is the first time we encounter this query, so execute it from scratch
            Err(input) => self.execute_query(db, input, hash),
        };

        runtime.register_dependency(Dependency {
            ingredient: self.id,
            resource: id,
        });

        unsafe { &self.output(id).value }
    }
}

impl<Q: Query> HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn get_or_reserve_slot(&self, input: Q::Input, hash: u64) -> Result<Id, Q::Input> {
        let shard = self.entries.shard(hash);

        // check if the query has already executed previously, and return that result
        let table = shard.raw().upgradable_read();
        if let Some(entry) = table.get(hash, self.entries.eq_fn(&input)) {
            match &entry.value {
                InputSlot::Done(id) => return Ok(*id),
                InputSlot::Progress(_) => todo!("handle cycle"),
            }
        }

        // otherwise, we need to reserve a slot ourselves: take a write lock on the table
        let mut table = RwLockUpgradableReadGuard::upgrade(table);

        // avoid a race condition where the slot was reserved while we upgraded the lock
        if let Some(entry) = table.get(hash, self.entries.eq_fn(&input)) {
            match &entry.value {
                InputSlot::Done(id) => return Ok(*id),
                InputSlot::Progress(_) => todo!("handle cycle"),
            }
        }

        // take ownership of the slot, by marking it as being in progress by us
        let slot = InputSlot::Progress(QueryProgress::new());
        table.insert_entry(
            hash,
            crate::shard_map::Entry::new(input.clone(), slot),
            self.entries.hash_fn(),
        );

        Err(input)
    }

    fn execute_query(&self, db: &Q::Database, input: Q::Input, hash: u64) -> Id {
        let result = db.runtime().execute_query::<Q>(db, input.clone());

        let index = self.outputs.push_zeroed();
        let id = Id::try_from_usize(index).expect("exhausted query IDs");

        // SAFETY: no other thread will read or write to/from this index as we have not made it
        // available yet, so we have exclusive access to this slot.
        unsafe {
            (*self.outputs.get_unchecked(index).get()).write(OutputSlot {
                value: result.output,
                dependencies: result.dependencies,
            })
        };

        // make the value available for other threads
        let mut shard = self.entries.shard(hash).raw().write();
        let entry = shard.get_mut(hash, self.entries.eq_fn(&input)).unwrap();
        entry.value = InputSlot::Done(id);

        id
    }
}

impl<Q: Query> HashQueryCache<Q> {
    /// # Safety
    ///
    /// The caller must ensure that the output slot associated with the given `id` has been
    /// initialized.
    unsafe fn output(&self, id: Id) -> &OutputSlot<Q::Output> {
        let slot = self.outputs.get_unchecked(id.raw.get() as usize);
        (*slot.get()).assume_init_ref()
    }
}
