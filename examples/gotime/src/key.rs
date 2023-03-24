use std::marker::PhantomData;

use haste::integer::NonMaxU32;

/// Like `Vec<T>`, but can only be indexed by a specific type.
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct KeyVec<K, T> {
    _phantom: PhantomData<K>,
    inner: Vec<T>,
}

/// Like `[T]`, but can only be indexed by a specific type.
#[repr(transparent)]
#[derive(PartialEq, Eq, Hash)]
pub struct KeySlice<K, T> {
    _phantom: PhantomData<K>,
    data: [T],
}

impl<K, T> std::fmt::Debug for KeyVec<K, T>
where
    K: std::fmt::Debug + KeyOps,
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<K, T> std::fmt::Debug for KeySlice<K, T>
where
    K: std::fmt::Debug + KeyOps,
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map = f.debug_map();
        for (i, value) in self.data.iter().enumerate() {
            let key = K::from_index(i);
            map.entry(
                &crate::util::display_fn(move |f| write!(f, "{:?}", key)),
                value,
            );
        }
        map.finish()
    }
}

impl<K, T> std::ops::Deref for KeyVec<K, T> {
    type Target = KeySlice<K, T>;

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<K, T> std::ops::DerefMut for KeyVec<K, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<K, T> From<Vec<T>> for KeyVec<K, T> {
    fn from(inner: Vec<T>) -> Self {
        Self {
            inner,
            _phantom: PhantomData,
        }
    }
}

impl<K, T> From<KeyVec<K, T>> for Box<KeySlice<K, T>> {
    fn from(vec: KeyVec<K, T>) -> Self {
        Self::from(vec.inner)
    }
}

impl<K, T> From<Vec<T>> for Box<KeySlice<K, T>> {
    fn from(vec: Vec<T>) -> Self {
        // SAFETY: `KeySlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(vec.into_boxed_slice()) }
    }
}

impl<K, T> Clone for Box<KeySlice<K, T>>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        // SAFETY: `KeySlice` is a `repr(transparent)` wrapper around `[T]`
        #[allow(clippy::borrowed_box)]
        let slice: &Box<[T]> = unsafe { std::mem::transmute(self) };

        let clone: Box<[T]> = slice.clone();

        // SAFETY: `KeySlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(clone) }
    }
}

impl<K: KeyOps, T> Default for KeyVec<K, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, T> KeyVec<K, T> {
    pub const fn new() -> Self {
        Self {
            _phantom: PhantomData,
            inner: Vec::new(),
        }
    }

    pub fn as_slice(&self) -> &KeySlice<K, T> {
        // SAFETY: `KeySlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(self.inner.as_slice()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut KeySlice<K, T> {
        // SAFETY: `KeySlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(self.inner.as_mut_slice()) }
    }

    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }
}

impl<K: KeyOps, T> KeyVec<K, T> {
    pub fn push(&mut self, value: T) -> K {
        let key = K::from_index(self.inner.len());
        self.inner.push(value);
        key
    }

    pub fn split_off(&mut self, key: K) -> KeyVec<K, T> {
        self.inner.split_off(key.index()).into()
    }
}

impl<K, T> KeySlice<K, T> {
    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter()
    }
}

impl<K: KeyOps, T> KeySlice<K, T> {
    pub fn get(&self, id: K) -> Option<&T> {
        self.data.get(id.index())
    }

    pub fn get_mut(&mut self, id: K) -> Option<&mut T> {
        self.data.get_mut(id.index())
    }
}

impl<K: KeyOps, T> std::ops::Index<K> for KeySlice<K, T> {
    type Output = T;

    fn index(&self, index: K) -> &Self::Output {
        &self.data[index.index()]
    }
}

impl<K: KeyOps, T> std::ops::IndexMut<K> for KeySlice<K, T> {
    fn index_mut(&mut self, id: K) -> &mut Self::Output {
        &mut self.data[id.index()]
    }
}

impl<K: KeyOps, T> std::ops::Index<std::ops::Range<K>> for KeySlice<K, T> {
    type Output = [T];

    fn index(&self, range: std::ops::Range<K>) -> &Self::Output {
        &self.data[range.start.index()..range.end.index()]
    }
}

impl<K: KeyOps, T> std::ops::IndexMut<std::ops::Range<K>> for KeySlice<K, T> {
    fn index_mut(&mut self, range: std::ops::Range<K>) -> &mut Self::Output {
        &mut self.data[range.start.index()..range.end.index()]
    }
}

pub trait KeyOps {
    fn from_index(index: usize) -> Self;
    fn index(self) -> usize;
}

pub struct Key<T> {
    raw: NonMaxU32,
    _phantom: PhantomData<*const T>,
}

unsafe impl<T> Send for Key<T> {}
unsafe impl<T> Sync for Key<T> {}

impl<T> Copy for Key<T> {}
impl<T> Clone for Key<T> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw,
            _phantom: PhantomData,
        }
    }
}

impl<T> PartialEq for Key<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl<T> Eq for Key<T> {}

impl<T> std::hash::Hash for Key<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state)
    }
}

impl<T> std::fmt::Debug for Key<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.raw.get().fmt(f)
    }
}

impl<T> KeyOps for Key<T> {
    fn index(self) -> usize {
        self.raw.get() as usize
    }

    fn from_index(index: usize) -> Self {
        Self {
            raw: NonMaxU32::new(index as u32).unwrap(),
            _phantom: PhantomData,
        }
    }
}

/// The origin to which some `Relative<K>` refers to
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Base<K>(K);

/// An offset from `Base<K>`, which together form a `K`
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Relative<K>(K);

impl<K: std::fmt::Debug> std::fmt::Debug for Base<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Base({:?})", self.0)
    }
}

impl<K: std::fmt::Debug> std::fmt::Debug for Relative<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Relative({:?})", self.0)
    }
}

impl<K: KeyOps> Default for Base<K> {
    fn default() -> Self {
        Self::origin()
    }
}

impl<K> Base<K>
where
    K: KeyOps,
{
    pub fn origin() -> Self {
        Self(K::from_index(0))
    }

    pub fn at(base: K) -> Self {
        Self(base)
    }

    pub fn offset(self, relative: Relative<K>) -> K {
        K::from_index(self.0.index() + relative.0.index())
    }

    pub fn relative_to(self, k: K) -> Relative<K> {
        Relative(K::from_index(k.index() - self.0.index()))
    }
}

impl<K> Relative<K> {
    pub fn from_offset(offset: K) -> Relative<K> {
        Relative(offset)
    }

    pub fn into_offset(self) -> K {
        self.0
    }
}
