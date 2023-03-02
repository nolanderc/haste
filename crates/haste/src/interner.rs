use crate::{
    arena::{Arena, RawArena},
    non_max::NonMaxU32,
    shard_map::ShardMap,
    ContainerPath,
};

use std::hash::Hash;

pub struct ArenaInterner<T> {
    path: ContainerPath,
    values: Arena<T>,
    entries: ShardMap<NonMaxU32>,
}

impl<T: Send + Sync + 'static> crate::MakeContainer for ArenaInterner<T> {
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            values: Arena::new(),
            entries: ShardMap::new(),
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

    fn last_changed(&self, _dep: crate::Dependency) -> Option<crate::Revision> {
        // Interned values are constant, so can never change
        None
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
    fn eq_fn<'a>(&'a self, value: &'a T) -> impl Fn(&NonMaxU32) -> bool + 'a
    where
        T: Eq,
    {
        move |entry| self.get(*entry).unwrap() == value
    }

    fn hash_fn(&self) -> impl Fn(&NonMaxU32) -> u64 + '_
    where
        T: Hash,
    {
        move |entry| self.entries.hash(self.get(*entry).unwrap())
    }

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
        let hash = self.entries.hash(&value);
        let shard = self.entries.shard(hash);

        // check if the value already exists in the interner
        let table = shard.read().unwrap();
        if let Some(old) = table.get(hash, self.eq_fn(&value)) {
            return *old;
        }

        let len_before = table.len();
        drop(table);
        let mut table = shard.write().unwrap();
        let len_after = table.len();

        if len_before != len_after {
            if let Some(old) = table.get(hash, self.eq_fn(&value)) {
                return *old;
            }
        }

        // add the value into the interner, returing its key
        let index = self.values.push(value);
        let key = NonMaxU32::new(index.try_into().unwrap()).expect("interner memory");
        table.insert_entry(hash, key, self.hash_fn());
        key
    }
}

pub struct StringInterner {
    path: ContainerPath,
    bytes: RawArena<u8>,
    ranges: Arena<StringRange>,
    entries: ShardMap<NonMaxU32>,
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
    padding: [u8; 3],
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
                padding: [0; 3],
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

impl crate::MakeContainer for StringInterner {
    fn new(path: ContainerPath) -> Self {
        Self {
            path,
            bytes: RawArena::new(),
            ranges: Arena::new(),
            entries: ShardMap::new(),
        }
    }
}

impl<DB: ?Sized> crate::Container<DB> for StringInterner {
    fn path(&self) -> ContainerPath {
        self.path
    }

    fn fmt(&self, id: crate::Id, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.get(id.raw).unwrap())
    }

    fn last_changed(&self, _dep: crate::Dependency) -> Option<crate::Revision> {
        // Interned values are constant, so can never change
        None
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
        self.get(id.raw).unwrap()
    }
}

impl crate::ElementContainerRef for StringInterner {
    fn insert_ref(&self, value: &Self::Value) -> crate::Id {
        crate::Id::new(self.insert(value))
    }
}

impl StringInterner {
    fn get(&self, raw: NonMaxU32) -> Option<&str> {
        let range = self.ranges.get(raw.get() as usize)?;
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

        let hash = self.entries.hash(string);
        let shard = self.entries.shard(hash);

        // check if the value already exists in the interner
        let table = shard.read().unwrap();
        if let Some(old) = table.get(hash, self.eq_fn(string)) {
            return *old;
        }

        let len_before = table.len();
        drop(table);
        let mut table = shard.write().unwrap();
        let len_after = table.len();

        if len_before != len_after {
            if let Some(old) = table.get(hash, self.eq_fn(string)) {
                return *old;
            }
        }

        // add the value into the interner, returing its key
        let range = self.allocate_range(string);
        let index = self.ranges.push(range);
        let key = NonMaxU32::new(index.try_into().unwrap()).expect("interner memory");
        table.insert_entry(hash, key, self.hash_fn());
        key
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

    fn eq_fn<'a>(&'a self, value: &'a str) -> impl Fn(&NonMaxU32) -> bool + 'a {
        move |entry| self.get(*entry) == Some(value)
    }

    fn hash_fn(&self) -> impl Fn(&NonMaxU32) -> u64 + '_ {
        move |entry| self.entries.hash(self.get(*entry).unwrap())
    }
}
