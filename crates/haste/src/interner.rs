use std::{
    cell::UnsafeCell,
    hash::Hash,
    mem::MaybeUninit,
    num::NonZeroU32,
    sync::atomic::{
        AtomicBool,
        Ordering::{Acquire, Release},
    },
};

use crate::{arena::Arena, shard::ShardLookup};

pub trait Interner<T: ?Sized> {
    fn insert(&self, value: T) -> InternId
    where
        T: Sized;

    fn lookup(&self, id: InternId) -> Option<&T>;
}

pub trait RefInterner<T: ?Sized>: Interner<T> {
    fn insert_ref(&self, value: &T) -> InternId;
}

pub struct InternId(NonZeroU32);

impl InternId {
    fn new(index: u32) -> Option<Self> {
        Some(Self(NonZeroU32::new(index.wrapping_add(1))?))
    }

    fn index(&self) -> u32 {
        self.0.get().wrapping_sub(1)
    }
}

pub struct ValueInterner<T> {
    lookup: ShardLookup,
    arena: Arena<ValueCell<T>>,
}

impl<T> Default for ValueInterner<T> {
    fn default() -> Self {
        Self {
            lookup: ShardLookup::default(),
            arena: Arena::with_capacity(1 << 32),
        }
    }
}

impl<T> Interner<T> for ValueInterner<T>
where
    T: Hash + Eq,
{
    fn insert(&self, value: T) -> InternId {
        unsafe fn get_value<T>(arena: &Arena<ValueCell<T>>, index: u32) -> &T {
            arena.get_unchecked(index as usize).get_unchecked()
        }

        let arena = &self.arena;

        let result = self.lookup.get_or_insert(
            fxhash::hash64(&value),
            |index| unsafe { get_value(arena, index) == &value },
            |index| unsafe { fxhash::hash64(get_value(arena, index)) },
        );

        let index = match result {
            crate::shard::LookupResult::Cached(index) => index,
            crate::shard::LookupResult::Insert(index, guard) => {
                unsafe { arena.get_or_allocate(index as usize).init(value) };
                drop(guard);
                index
            }
        };

        InternId::new(index).expect("exhausted intern IDs")
    }

    fn lookup(&self, id: InternId) -> Option<&T> {
        let index = id.index() as usize;
        self.arena.get(index)?.get()
    }
}

struct ValueCell<T> {
    initialized: AtomicBool,
    value: UnsafeCell<MaybeUninit<T>>,
}

unsafe impl<T> bytemuck::Zeroable for ValueCell<T> {}

impl<T> ValueCell<T> {
    unsafe fn init(&self, value: T) {
        self.value.get().write(MaybeUninit::new(value));
        self.initialized.store(true, Release);
    }

    fn get(&self) -> Option<&T> {
        if self.initialized.load(Acquire) {
            Some(unsafe { self.get_unchecked() })
        } else {
            None
        }
    }

    unsafe fn get_unchecked(&self) -> &T {
        (*self.value.get()).assume_init_ref()
    }
}
