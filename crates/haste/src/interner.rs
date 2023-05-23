use crate::{
    arena::{Arena, RawArena},
    integer::NonMaxU32,
    shard_map::ShardLookup,
    Change, ContainerPath, LastChangeFuture,
};

use std::hash::Hash;

pub struct ArenaInterner<T> {
    path: ContainerPath,
    values: Arena<T>,
    entries: ShardLookup,
}

impl<T: Send + Sync + 'static> crate::StaticContainer for ArenaInterner<T> {
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            values: Arena::new(),
            entries: ShardLookup::default(),
        }
    }
}

impl<DB: ?Sized, T> crate::Container<DB> for ArenaInterner<T>
where
    T: std::fmt::Debug + Send + Sync + 'static,
{
    fn path(&self) -> ContainerPath {
        self.path
    }

    fn fmt(&self, id: crate::Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.get(id.raw).unwrap().fmt(f)
    }

    fn last_change(&self, _db: &DB, _dep: crate::Dependency) -> LastChangeFuture {
        // Interned values are constant, so can never change
        LastChangeFuture::Ready(Change::NONE)
    }

    fn info(&self, _id: crate::Id) -> Option<crate::IngredientInfo> {
        Some(crate::IngredientInfo {
            dependencies: &[],
            poll_count: 0,
            poll_nanos: 0,
        })
    }
}

impl<T> crate::ElementContainer for ArenaInterner<T>
where
    T: Eq + Hash + Send + Sync + 'static,
{
    type Value = T;

    type Ref<'a> = &'a T
    where
        Self: 'a;

    fn insert(&self, value: T) -> crate::Id {
        crate::Id::new(self.intern(value))
    }

    fn get_untracked(&self, id: crate::Id) -> Self::Ref<'_> {
        self.get(id.raw).unwrap()
    }
}

impl<T> ArenaInterner<T> {
    /// Get a value in the interner.
    ///
    /// Returns `None` if the index has not previously been returned by [`Self::intern`].
    pub fn get(&self, index: NonMaxU32) -> Option<&T> {
        self.values.get(index.get() as usize)
    }

    /// Insert a new value into the interner, returning its index
    pub fn intern(&self, value: T) -> NonMaxU32
    where
        T: Hash + Eq,
    {
        let hash = fxhash::hash64(&value);
        let result = self.entries.get_or_insert(
            hash,
            |index| self.values.get(index as usize).unwrap() == &value,
            |index| fxhash::hash64(self.values.get(index as usize).unwrap()),
        );

        let index = match result {
            crate::shard_map::ShardResult::Cached(index) => index,
            crate::shard_map::ShardResult::Insert(index, _write_guard) => {
                unsafe { self.values.write_unique(index as usize, value) };
                index
            }
        };

        NonMaxU32::new(index).unwrap()
    }
}

pub struct StringInterner {
    path: ContainerPath,
    bytes: RawArena<u8>,
    ranges: Arena<StringRange>,
    entries: ShardLookup,
}

unsafe impl Sync for StringInterner {}

#[repr(C)]
union StringRange {
    heap: ByteRange,
    inline: InlineString,
}

/// The string is allocated in the `StringInterner`'s arena.
#[repr(C)]
#[derive(Clone, Copy)]
struct ByteRange {
    start: u32,
    length: u32,
    padding: [u8; 7],
    inline_len: u8,
}

/// Represents the string within the bytes of the struct itself.
#[repr(C)]
#[derive(Clone, Copy)]
struct InlineString {
    /// The bytes of an UTF-8 encoded string.
    ///
    /// To encode the length, we abuse the fact that the last byte of a UTF-8 encoded codepoint
    /// will always be in the range `0x00 ..= 0xBF`. If the final byte of the string is within this
    /// range, we know the length is `MAX_LENGTH`. Otherwise, we store the length in the final byte
    /// as `0xff - length`. We can support lengths in the range `0 .. 63` using this encoding, as
    /// we still need to represent a heap-allocated string using the bit-pattern `0xC0`.
    bytes: [u8; Self::MAX_LENGTH],
}

impl StringRange {
    fn heap(start: u32, length: u32) -> Self {
        Self {
            heap: ByteRange {
                start,
                length,
                padding: [0; 7],
                inline_len: InlineString::HEAP,
            },
        }
    }

    fn inline(inline: InlineString) -> Self {
        Self { inline }
    }

    /// Return the inline string, if possible
    fn get_inline(&self) -> Option<&str> {
        // SAFETY: all variants have a `u8` as their final field, and this is the only field read
        // by `get`. We make sure to initialize `heap::inline_len` as an invalid value for an
        // inline string
        unsafe { self.inline.get() }
    }
}

impl InlineString {
    const MAX_UTF8: u8 = 0xBF;
    const HEAP: u8 = Self::MAX_UTF8 + 1;
    const MAX_LENGTH: usize = std::mem::size_of::<ByteRange>();

    fn new(text: &str) -> Option<Self> {
        let mut bytes = [0u8; Self::MAX_LENGTH];
        bytes
            .get_mut(..text.len())?
            .copy_from_slice(text.as_bytes());
        if text.len() < Self::MAX_LENGTH {
            bytes[Self::MAX_LENGTH - 1] = 0xff - text.len() as u8;
        }
        Some(Self { bytes })
    }

    fn get(&self) -> Option<&str> {
        let last = self.bytes[Self::MAX_LENGTH - 1];

        let len = if last <= Self::MAX_UTF8 {
            Self::MAX_LENGTH
        } else {
            0xff - last as usize
        };

        let bytes = self.bytes.get(..len)?;

        // SAFETY: We only initialize new strings using `Self::new`, which are always valid UTF-8
        unsafe { Some(std::str::from_utf8_unchecked(bytes)) }
    }
}

impl crate::StaticContainer for StringInterner {
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            bytes: RawArena::new(),
            ranges: Arena::new(),
            entries: ShardLookup::default(),
        }
    }
}

impl<DB: ?Sized> crate::Container<DB> for StringInterner {
    fn path(&self) -> ContainerPath {
        self.path
    }

    fn fmt(&self, id: crate::Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.get(id.raw.get()).unwrap())
    }

    fn last_change(&self, _db: &DB, _dep: crate::Dependency) -> LastChangeFuture {
        // Interned values are constant, so can never change
        LastChangeFuture::Ready(Change::NONE)
    }

    fn info(&self, _id: crate::Id) -> Option<crate::IngredientInfo> {
        Some(crate::IngredientInfo {
            dependencies: &[],
            poll_count: 0,
            poll_nanos: 0,
        })
    }
}

impl crate::ElementContainer for StringInterner {
    type Value = str;

    type Ref<'a> = &'a str
    where
        Self: 'a;

    fn insert(&self, _value: str) -> crate::Id
    where
        str: Sized,
    {
        unreachable!("str can not be passed by value")
    }

    fn get_untracked(&self, id: crate::Id) -> Self::Ref<'_> {
        self.get(id.raw.get()).unwrap()
    }
}

impl crate::ElementContainerRef for StringInterner {
    fn insert_ref(&self, value: &Self::Value) -> crate::Id {
        crate::Id::new(self.insert(value))
    }
}

impl StringInterner {
    fn get(&self, index: u32) -> Option<&str> {
        let range = self.ranges.get(index as usize)?;
        if let Some(inline) = range.get_inline() {
            return Some(inline);
        }

        // SAFETY: the string was not inline, so it must be allocated on the heap
        let heap = unsafe { range.heap };

        // SAFETY: we only initialize valid heap ranges
        unsafe {
            let ptr = self.bytes.get_raw(heap.start as usize);
            let bytes = std::slice::from_raw_parts(ptr, heap.length as usize);
            Some(std::str::from_utf8_unchecked(bytes))
        }
    }

    fn insert(&self, string: &str) -> NonMaxU32 {
        assert!(
            string.len() < u32::MAX as usize,
            "string exceeds maximum length"
        );

        let hash = fxhash::hash64(string);
        let result = self.entries.get_or_insert(
            hash,
            |index| self.get(index).unwrap() == string,
            |index| fxhash::hash64(self.get(index).unwrap()),
        );

        let index = match result {
            crate::shard_map::ShardResult::Cached(index) => index,
            crate::shard_map::ShardResult::Insert(index, _write_guard) => {
                let range = self.allocate_range(string);
                unsafe { self.ranges.write_unique(index as usize, range) };
                index
            }
        };

        NonMaxU32::new(index).unwrap()
    }

    fn allocate_range(&self, string: &str) -> StringRange {
        match InlineString::new(string) {
            Some(inline) => StringRange::inline(inline),
            None => {
                let offset = self.bytes.reserve_zeroed(string.len());

                // SAFETY: we just allocated this region, and no other thread has access to the
                // same region since we have not made it public yet. This write is synchronized
                // when inserting the range in an entry
                unsafe {
                    let ptr = self.bytes.get_raw(offset);
                    ptr.copy_from_nonoverlapping(string.as_ptr(), string.len());
                }

                StringRange::heap(offset as u32, string.len() as u32)
            }
        }
    }
}
