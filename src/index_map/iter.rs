use std::{iter::FusedIterator, marker::PhantomData, ops::Range};

use hashbrown::hash_map::DefaultHashBuilder;

use super::{IndexKey, IndexMap, StableDeref};

/// Iterator for keys in an `IndexMap`.
pub struct KeyIter<K> {
    pub(super) range: Range<usize>,
    pub(super) marker: PhantomData<K>,
}

/// Iterator for key-value pairs in an `IndexMap`, which clones the values.
pub struct ClonedIter<'a, K, V, A = DefaultHashBuilder> {
    pub(super) map: &'a IndexMap<K, V, A>,
    pub(super) range: Range<usize>,
}

/// Iterator for key-value pairs in an `IndexMap`, which dereferences the
/// values.
pub struct DerefIter<'a, K, V, A = DefaultHashBuilder> {
    pub(super) map: &'a IndexMap<K, V, A>,
    pub(super) range: Range<usize>,
}

impl<K: IndexKey> Iterator for KeyIter<K> {
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(K::from_usize(self.range.next()?))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.range.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.range.nth(n).map(K::from_usize)
    }
}

impl<'a, K: IndexKey, V: Clone, S> Iterator for ClonedIter<'a, K, V, S> {
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.range.next().map(|index| self.map.get_kv_cloned(index))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.range.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.range.nth(n).map(|index| self.map.get_kv_cloned(index))
    }
}

impl<'a, K: IndexKey, V: StableDeref, S> Iterator for DerefIter<'a, K, V, S> {
    type Item = (K, &'a V::Target);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.range.next().map(|index| self.map.get_kv_deref(index))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.range.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.range.nth(n).map(|index| self.map.get_kv_deref(index))
    }
}

impl<K: IndexKey> DoubleEndedIterator for KeyIter<K> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range.next_back().map(K::from_usize)
    }
}

impl<K: IndexKey, V: Clone, S> DoubleEndedIterator for ClonedIter<'_, K, V, S> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range
            .next_back()
            .map(|index| self.map.get_kv_cloned(index))
    }
}

impl<K: IndexKey, V: StableDeref, S> DoubleEndedIterator for DerefIter<'_, K, V, S> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range
            .next_back()
            .map(|index| self.map.get_kv_deref(index))
    }
}

impl<K: IndexKey> ExactSizeIterator for KeyIter<K> {
    #[inline]
    fn len(&self) -> usize {
        self.range.len()
    }
}

impl<K: IndexKey, V: Clone, S> ExactSizeIterator for ClonedIter<'_, K, V, S> {
    #[inline]
    fn len(&self) -> usize {
        self.range.len()
    }
}

impl<K: IndexKey, V: StableDeref, S> ExactSizeIterator for DerefIter<'_, K, V, S> {
    #[inline]
    fn len(&self) -> usize {
        self.range.len()
    }
}

impl<K: IndexKey> FusedIterator for KeyIter<K> {}
impl<K: IndexKey, V: Clone, S> FusedIterator for ClonedIter<'_, K, V, S> {}
impl<K: IndexKey, V: StableDeref, S> FusedIterator for DerefIter<'_, K, V, S> {}
