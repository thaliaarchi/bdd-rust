#![allow(dead_code)]

mod iter;

pub use iter::*;

use std::{
    cell::UnsafeCell,
    fmt::{self, Debug, Formatter},
    hash::{BuildHasher, Hash},
    marker::PhantomData,
    ops::Deref,
};

use hashbrown::{DefaultHashBuilder, HashTable};

/// Bidirectional hash map, which monotonically grows and uses an index as the
/// key.
pub struct IndexMap<K, V, S = DefaultHashBuilder> {
    // SAFETY: No references to fields are returned, which could be invalidated
    // by mutation. Values are only accessed by cloning or stable dereferences.
    inner: UnsafeCell<IndexMapInner<K, V, S>>,
}

unsafe impl<K: Send, V: Send, S: Send> Send for IndexMap<K, V, S> {}

struct IndexMapInner<K, V, S> {
    /// Key-to-value table.
    values: Vec<V>,
    /// Value-to-key map, which references the value in `self.values` by index.
    keys: HashTable<K>,
    hash_builder: S,
}

/// Key identifying values in `IndexMap`, which is represented by `usize`.
pub trait IndexKey {
    fn from_usize(index: usize) -> Self;

    fn as_usize(&self) -> usize;
}

/// A type which dereferences to a fixed address, which remains valid when its
/// container is moved.
pub unsafe trait StableDeref: Deref {}

impl<K, V, S: Default> IndexMap<K, V, S> {
    /// Constructs a new, empty `IndexMap`.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Constructs a new, empty `IndexMap` with at least the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        IndexMap {
            inner: UnsafeCell::new(IndexMapInner {
                values: Vec::with_capacity(capacity),
                keys: HashTable::with_capacity(capacity),
                hash_builder: S::default(),
            }),
        }
    }
}

impl<K, V, S: Default> Default for IndexMap<K, V, S> {
    fn default() -> Self {
        IndexMap::new()
    }
}

impl<K: Clone, V: Clone, S: Clone> Clone for IndexMap<K, V, S> {
    fn clone(&self) -> Self {
        let inner = self.inner();
        IndexMap {
            inner: UnsafeCell::new(IndexMapInner {
                values: inner.values.clone(),
                keys: inner.keys.clone(),
                hash_builder: inner.hash_builder.clone(),
            }),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        let inner = self.inner.get_mut();
        let source = source.inner();
        inner.values.clone_from(&source.values);
        inner.keys.clone_from(&source.keys);
        inner.hash_builder.clone_from(&source.hash_builder);
    }
}

impl<K, V, S> IndexMap<K, V, S> {
    #[inline]
    fn inner(&self) -> &IndexMapInner<K, V, S> {
        // SAFETY: See `IndexMap::inner`.
        unsafe { &*self.inner.get() }
    }

    #[inline]
    fn inner_mut(&self) -> &mut IndexMapInner<K, V, S> {
        // SAFETY: See `IndexMap::inner`.
        unsafe { &mut *self.inner.get() }
    }

    /// Returns the number of values in this map.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner().values.len()
    }

    /// Returns whether this map has no values.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<K: IndexKey + Copy, V: PartialEq + Hash, S: BuildHasher> IndexMap<K, V, S> {
    /// Gets or inserts a value into the map and returns its key.
    pub fn insert(&self, value: V) -> K {
        let inner = self.inner_mut();
        let hash = inner.hash_builder.hash_one(&value);
        *inner
            .keys
            .entry(
                hash,
                |key| &inner.values[key.as_usize()] == &value,
                |key| inner.hash_builder.hash_one(&inner.values[key.as_usize()]),
            )
            .or_insert_with(|| {
                let id = K::from_usize(inner.values.len());
                inner.values.push(value);
                id
            })
            .get()
    }
}

impl<K: IndexKey, V, S> IndexMap<K, V, S> {
    /// Returns an iterator for keys in the map.
    #[inline]
    pub fn iter_keys(&self) -> KeyIter<K> {
        KeyIter {
            range: 0..self.inner().values.len(),
            marker: PhantomData,
        }
    }
}

impl<K: IndexKey, V: Clone, S> IndexMap<K, V, S> {
    /// Gets the value at the given key in the map and clones it.
    #[inline]
    pub fn get_cloned(&self, key: K) -> V {
        self.inner().values[key.as_usize()].clone()
    }

    /// Gets the value at the given key in the map, without checking that it is
    /// in range, and clones it.
    #[inline]
    pub unsafe fn get_cloned_unchecked(&self, key: K) -> V {
        unsafe { self.inner().values.get_unchecked(key.as_usize()) }.clone()
    }

    #[inline]
    fn get_kv_cloned(&self, index: usize) -> (K, V) {
        let value = unsafe { self.inner().values.get_unchecked(index) };
        (K::from_usize(index), value.clone())
    }

    /// Returns an iterator for key-value pairs in the map, which clones the
    /// values.
    #[inline]
    pub fn iter_cloned(&self) -> ClonedIter<'_, K, V, S> {
        ClonedIter {
            map: self,
            range: 0..self.inner().values.len(),
        }
    }
}

impl<K: IndexKey, V: StableDeref, S> IndexMap<K, V, S> {
    /// Gets the value at the given key in the map and dereferences it.
    #[inline]
    pub fn get_deref(&self, key: K) -> &V::Target {
        &*self.inner().values[key.as_usize()]
    }

    /// Gets the value at the given key in the map, without checking that it is
    /// in range, and dereferences it.
    #[inline]
    pub unsafe fn get_deref_unchecked(&self, key: K) -> &V::Target {
        &*unsafe { self.inner().values.get_unchecked(key.as_usize()) }
    }

    #[inline]
    fn get_kv_deref(&self, index: usize) -> (K, &V::Target) {
        let value = unsafe { self.inner().values.get_unchecked(index) };
        (K::from_usize(index), &*value)
    }

    /// Returns an iterator for key-value pairs in the map, which dereferences
    /// the values.
    #[inline]
    pub fn iter_deref(&self) -> DerefIter<'_, K, V, S> {
        DerefIter {
            map: self,
            range: 0..self.inner().values.len(),
        }
    }
}

impl<K: IndexKey + Debug, V: Debug, S> Debug for IndexMap<K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for (i, value) in self.inner().values.iter().enumerate() {
            map.entry(&K::from_usize(i), value);
        }
        map.finish()
    }
}

impl<K, V: PartialEq, S> PartialEq for IndexMap<K, V, S> {
    fn eq(&self, other: &Self) -> bool {
        self.inner().values.eq(&other.inner().values)
    }
}

impl<K, V: Eq, S> Eq for IndexMap<K, V, S> {}

impl<K, V: PartialEq, S> PartialEq<[V]> for IndexMap<K, V, S> {
    fn eq(&self, other: &[V]) -> bool {
        self.inner().values.eq(&other)
    }
}

unsafe impl StableDeref for String {}
unsafe impl<T> StableDeref for Vec<T> {}
