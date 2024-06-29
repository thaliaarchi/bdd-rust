use crate::{Bdd, BddId, BddManager};

/// A set of BDDs.
pub struct BddSet<'mgr> {
    bdds: Vec<BddId>,
    mgr: &'mgr BddManager,
}

impl<'mgr> BddSet<'mgr> {
    /// Constructs a new `BddSet` containing the items of the iterator.
    pub fn new(mut bdds: impl Iterator<Item = Bdd<'mgr>>) -> Self {
        let (len, _) = bdds.size_hint();
        let Some(first) = bdds.next() else {
            panic!("empty iterator");
        };
        let mgr = first.mgr;
        let mut ids = Vec::with_capacity(len);
        ids.push(first.id());
        ids.extend(bdds.map(|bdd| {
            Bdd::assert_manager(mgr, &bdd.mgr);
            bdd.id()
        }));
        BddSet { bdds: ids, mgr }
    }

    /// Constructs a new, empty `BddSet`.
    pub fn empty(mgr: &'mgr BddManager) -> Self {
        BddSet {
            bdds: Vec::new(),
            mgr,
        }
    }

    /// Computes the property that exactly one value can be set at once.
    #[inline]
    pub fn unique(&self) -> Bdd<'mgr> {
        self.mgr.wrap(self.mgr.unique(&self.bdds))
    }
}
