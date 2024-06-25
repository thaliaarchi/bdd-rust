#![allow(dead_code)]

use std::{
    fmt::{self, Debug, Formatter},
    hash::{BuildHasher, Hash},
    marker::PhantomData,
    ops::Index,
    slice,
};

use hashbrown::{hash_map::DefaultHashBuilder, raw::RawTable};

/// Bidirectional hash map, which stores values uniquely and uses an index as
/// the key.
pub(crate) struct IndexMap<K, V, S = DefaultHashBuilder> {
    /// Key-to-value table.
    values: Vec<V>,
    /// Value-to-key map, which references the value in `self.values` by index.
    keys: RawTable<K>,
    hash_builder: S,
}

/// Key identifying values in `IndexMap`, which is represented by `usize`.
pub(crate) trait IndexKey {
    fn from_usize(index: usize) -> Self;
    fn as_usize(&self) -> usize;
}

/// Iterator for values in `IndexMap`.
pub(crate) struct IndexMapIter<'a, K, V> {
    values: slice::Iter<'a, V>,
    index: usize,
    marker: PhantomData<K>,
}

impl<K: IndexKey + Copy, V: PartialEq + Hash> IndexMap<K, V> {
    /// Constructs a new, empty `IndexMap`.
    pub(crate) fn new() -> Self {
        IndexMap {
            values: Vec::new(),
            keys: RawTable::new(),
            hash_builder: DefaultHashBuilder::default(),
        }
    }

    /// Constructs a new, empty `IndexMap` with at least the specified capacity.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        IndexMap {
            values: Vec::with_capacity(capacity),
            keys: RawTable::with_capacity(capacity),
            hash_builder: DefaultHashBuilder::default(),
        }
    }

    /// Gets or inserts a value into the map and returns its key.
    pub(crate) fn insert(&mut self, value: V) -> K {
        let hash = self.hash_builder.hash_one(&value);
        match self.keys.find_or_find_insert_slot(
            hash,
            |key| &self.values[key.as_usize()] == &value,
            |key| self.hash_builder.hash_one(&self.values[key.as_usize()]),
        ) {
            Ok(bucket) => {
                // SAFETY: The value in the bucket is copied, so does not
                // outlive the table.
                *unsafe { bucket.as_ref() }
            }
            Err(slot) => {
                let id = K::from_usize(self.values.len());
                self.values.push(value);
                // SAFETY: The slot has not been mutated before this call.
                unsafe { self.keys.insert_in_slot(hash, slot, id) };
                id
            }
        }
    }

    /// Returns the values in the map.
    pub(crate) fn values(&mut self) -> &[V] {
        &self.values
    }
}

impl<K: IndexKey, V> Index<K> for IndexMap<K, V> {
    type Output = V;

    fn index(&self, index: K) -> &Self::Output {
        &self.values[index.as_usize() as usize]
    }
}

impl<K: IndexKey + Clone, V: Clone, S: Clone> Clone for IndexMap<K, V, S> {
    fn clone(&self) -> Self {
        IndexMap {
            values: self.values.clone(),
            keys: self.keys.clone(),
            hash_builder: self.hash_builder.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.values.clone_from(&source.values);
        self.keys.clone_from(&source.keys);
        self.hash_builder.clone_from(&source.hash_builder);
    }
}

impl<K: IndexKey + Debug, V: Debug, S> Debug for IndexMap<K, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for (i, value) in self.values.iter().enumerate() {
            map.entry(&K::from_usize(i), value);
        }
        map.finish()
    }
}

impl<K, V: PartialEq, S> PartialEq for IndexMap<K, V, S> {
    fn eq(&self, other: &Self) -> bool {
        self.values.eq(&other.values)
    }
}

impl<K, V: Eq, S> Eq for IndexMap<K, V, S> {}

impl<'a, K: IndexKey, V> IntoIterator for &'a IndexMap<K, V> {
    type Item = (K, &'a V);
    type IntoIter = IndexMapIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IndexMapIter {
            values: self.values.iter(),
            index: 0,
            marker: PhantomData,
        }
    }
}

impl<'a, K: IndexKey, V> Iterator for IndexMapIter<'a, K, V> {
    type Item = (K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let value = self.values.next()?;
        let key = K::from_usize(self.index);
        self.index += 1;
        Some((key, value))
    }
}
