use std::{cell::UnsafeCell, hash::Hash, mem::MaybeUninit};

use parking_lot::RwLockUpgradableReadGuard;

use crate::{arena::RawArena, shard_map::ShardMap, Id, Query};

pub struct HashQueryCache<Q: Query> {
    entries: ShardMap<Q::Input, InputSlot>,
    outputs: RawArena<UnsafeCell<MaybeUninit<OutputSlot<Q::Output>>>>,
}

impl<Q: Query> Default for HashQueryCache<Q> {
    fn default() -> Self {
        Self {
            entries: ShardMap::default(),
            outputs: RawArena::new(),
        }
    }
}

enum InputSlot {
    Progress(QueryProgress),
    Done(Id),
}

struct OutputSlot<T> {
    value: T,
}

struct QueryProgress {}

impl QueryProgress {
    fn new() -> Self {
        Self {}
    }
}

impl<Q: Query> crate::QueryCache<Q> for HashQueryCache<Q>
where
    Q::Input: Hash + Eq + Clone,
{
    fn get_or_execute<'a>(
        &'a self,
        db: &<Q>::Database,
        input: <Q as Query>::Input,
    ) -> &'a <Q as Query>::Output {
        let hash = self.entries.hash(&input);
        let shard = self.entries.shard(hash);

        {
            // check if the query has already executed previously, and return that result
            let table = shard.raw().upgradable_read();
            if let Some(entry) = table.get(hash, self.entries.eq_fn(&input)) {
                match &entry.value {
                    InputSlot::Done(id) => return unsafe { &self.output(*id).value },
                    InputSlot::Progress(_) => todo!("handle cycle"),
                }
            }

            // otherwise, we need to reserve a slot ourselves: take a write lock on the table
            let mut table = RwLockUpgradableReadGuard::upgrade(table);

            // avoid a race condition where the slot was reserved while we upgraded the lock
            if let Some(entry) = table.get(hash, self.entries.eq_fn(&input)) {
                match &entry.value {
                    InputSlot::Done(id) => return unsafe { &self.output(*id).value },
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
        }

        // we are now responsible for computing the output of the query.
        let output = Q::execute(db, input.clone());
        let index = self.outputs.push_zeroed();
        let id = Id::try_from_usize(index).expect("exhausted query IDs");

        let output_slot: &OutputSlot<_> = unsafe {
            &*(*self.outputs.get_unchecked(index).get()).write(OutputSlot { value: output })
        };

        shard
            .raw()
            .write()
            .get_mut(hash, self.entries.eq_fn(&input))
            .unwrap()
            .value = InputSlot::Done(id);

        &output_slot.value
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
