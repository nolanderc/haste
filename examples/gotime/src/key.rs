use std::marker::PhantomData;

use haste::non_max::NonMaxU32;

/// Like `Vec<T>`, but can only be indexed by a specific type.
pub struct KeyVec<K, T> {
    _phantom: PhantomData<K>,
    inner: Vec<T>,
}

/// Like `[T]`, but can only be indexed by a specific type.
#[repr(transparent)]
pub struct KeySlice<K, T> {
    _phantom: PhantomData<K>,
    data: [T],
}

impl<K, T> std::ops::Deref for KeyVec<K, T> {
    type Target = KeySlice<K, T>;

    fn deref(&self) -> &Self::Target {
        // SAFETY: `KdSlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(self.inner.as_slice()) }
    }
}

impl<K, T> std::ops::DerefMut for KeyVec<K, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: `KdSlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(self.inner.as_mut_slice()) }
    }
}

impl<K, T> From<KeyVec<K, T>> for Box<KeySlice<K, T>> {
    fn from(vec: KeyVec<K, T>) -> Self {
        // SAFETY: `KdSlice` is a `repr(transparent)` wrapper around `[T]`
        unsafe { std::mem::transmute(vec.inner.into_boxed_slice()) }
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

pub trait KeyOps {
    fn from_index(index: usize) -> Self;
    fn index(self) -> usize;
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Key<T> {
    raw: NonMaxU32,
    _phantom: PhantomData<*const T>,
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
pub struct Base<K>(K);

/// An offset from `Base<K>`, which together form a `K`
pub struct Relative<K>(K);

impl<K> Base<K>
where
    K: KeyOps,
{
    pub fn origin() -> Self {
        Self(K::from_index(0))
    }

    pub fn offset(self, relative: Relative<K>) -> K {
        K::from_index(self.0.index() + relative.0.index())
    }
}
