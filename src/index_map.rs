#![allow(dead_code)]

use std::{
    cell::UnsafeCell,
    fmt::{self, Debug, Formatter},
    hash::{BuildHasher, Hash},
    ops::{Deref, Range},
};

use hashbrown::{hash_map::DefaultHashBuilder, raw::RawTable};

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
    keys: RawTable<K>,
    hash_builder: S,
}

/// Iterator for key-value pairs in an `IndexMap`, which clones the values.
pub struct IndexMapClonedIter<'a, K, V, A = DefaultHashBuilder> {
    map: &'a IndexMap<K, V, A>,
    range: Range<usize>,
}

/// Iterator for key-value pairs in an `IndexMap`, which dereferences the
/// values.
pub struct IndexMapDerefIter<'a, K, V, A = DefaultHashBuilder> {
    map: &'a IndexMap<K, V, A>,
    range: Range<usize>,
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
                keys: RawTable::with_capacity(capacity),
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
    fn inner(&self) -> &IndexMapInner<K, V, S> {
        // SAFETY: See `IndexMap::inner`.
        unsafe { &*self.inner.get() }
    }

    fn inner_mut(&self) -> &mut IndexMapInner<K, V, S> {
        // SAFETY: See `IndexMap::inner`.
        unsafe { &mut *self.inner.get() }
    }
}

impl<K: IndexKey + Copy, V: PartialEq + Hash, S: BuildHasher> IndexMap<K, V, S> {
    /// Gets or inserts a value into the map and returns its key.
    pub fn insert(&self, value: V) -> K {
        let inner = self.inner_mut();
        let hash = inner.hash_builder.hash_one(&value);
        match inner.keys.find_or_find_insert_slot(
            hash,
            |key| &inner.values[key.as_usize()] == &value,
            |key| inner.hash_builder.hash_one(&inner.values[key.as_usize()]),
        ) {
            Ok(bucket) => {
                // SAFETY: The value in the bucket is copied, so does not
                // outlive the table.
                *unsafe { bucket.as_ref() }
            }
            Err(slot) => {
                let id = K::from_usize(inner.values.len());
                inner.values.push(value);
                // SAFETY: The slot has not been mutated before this call.
                unsafe { inner.keys.insert_in_slot(hash, slot, id) };
                id
            }
        }
    }
}

impl<K: IndexKey, V: Clone, S> IndexMap<K, V, S> {
    pub fn get_cloned(&self, key: K) -> V {
        self.get_index_cloned(key.as_usize())
    }

    fn get_index_cloned(&self, index: usize) -> V {
        self.inner().values[index].clone()
    }

    pub fn iter_cloned(&self) -> IndexMapClonedIter<'_, K, V, S> {
        IndexMapClonedIter {
            map: self,
            range: 0..self.inner().values.len(),
        }
    }
}

impl<K: IndexKey, V: StableDeref, S> IndexMap<K, V, S> {
    pub fn get_deref(&self, key: K) -> &V::Target {
        self.get_index_deref(key.as_usize())
    }

    fn get_index_deref(&self, index: usize) -> &V::Target {
        &*self.inner().values[index]
    }

    pub fn iter_deref(&self) -> IndexMapDerefIter<'_, K, V, S> {
        IndexMapDerefIter {
            map: self,
            range: 0..self.inner().values.len(),
        }
    }
}

impl<'a, K: IndexKey, V: Clone, S> Iterator for IndexMapClonedIter<'a, K, V, S> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.range.next()?;
        Some((K::from_usize(index), self.map.get_index_cloned(index)))
    }
}

impl<'a, K: IndexKey, V: StableDeref, S> Iterator for IndexMapDerefIter<'a, K, V, S> {
    type Item = (K, &'a V::Target);

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.range.next()?;
        Some((K::from_usize(index), self.map.get_index_deref(index)))
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
