use std::ops::Range;

use crate::{Bdd, BddId, BddManager};

/// An integer, which bounded to a range and counted in unary. Alternatively, an
/// enum.
#[derive(Clone, Debug)]
pub struct Unary<'mgr> {
    values: Vec<BddId>,
    bounds: Range<i64>,
    unique: BddId,
    mgr: &'mgr BddManager,
}

impl<'mgr> Unary<'mgr> {
    /// Constructs a new `Unary` number in the manager with the given name and
    /// bounds.
    pub fn new(mgr: &'mgr BddManager, ident: &str, bounds: Range<i64>) -> Self {
        let len = Unary::index(bounds.start, bounds.end);
        let mut values = Vec::with_capacity(len);
        for value in bounds.clone() {
            values.push(mgr.insert_var(format!("{ident}{value}")).id());
        }
        let unique = unique(mgr, &values);
        Unary {
            values,
            bounds,
            unique,
            mgr,
        }
    }

    pub fn get(&self, other: i64) -> Bdd<'mgr> {
        self.mgr
            .wrap(self.values[Unary::index(self.bounds.start, other)])
    }

    pub fn value(&self) -> Bdd<'_> {
        self.mgr.wrap(self.unique)
    }

    fn index(start: i64, value: i64) -> usize {
        value
            .checked_sub(start)
            .and_then(|len| len.try_into().ok())
            .unwrap()
    }
}

/// Computes the property that exactly one value can be set at once.
fn unique(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = mgr.zero();
    for &v in values {
        unique |= mgr.wrap(v);
    }
    for &v1 in values {
        for &v2 in values {
            if v1 != v2 {
                unique &= !mgr.wrap(v1) | !mgr.wrap(v2);
            }
        }
    }
    unique.id()
}

#[cfg(test)]
mod tests {
    use super::*;

    const UNIQUE_ALGS: [(
        &'static str,
        fn(mgr: &BddManager, values: &[BddId]) -> BddId,
    ); 3] = [
        ("unique", unique),
        ("unique_alt2", unique_alt2),
        ("unique_alt3", unique_alt3),
    ];

    fn unique_alt2(mgr: &BddManager, values: &[BddId]) -> BddId {
        let mut unique = mgr.zero();
        for &v1 in values {
            let mut only_v1 = mgr.one();
            for &v2 in values {
                let v = mgr.wrap(v2);
                only_v1 &= if v1 == v2 { v } else { !v };
            }
            unique |= only_v1;
        }
        unique.id()
    }

    fn unique_alt3(mgr: &BddManager, values: &[BddId]) -> BddId {
        let mut unique = mgr.zero();
        for &v1 in values {
            let mut only_v1 = mgr.wrap(v1);
            for &v2 in values {
                if v2 != v1 {
                    only_v1 &= !mgr.wrap(v2);
                }
            }
            unique |= only_v1;
        }
        unique.id()
    }

    fn insert_vars(mgr: &BddManager, n_vars: usize) -> Vec<BddId> {
        let mut values = Vec::with_capacity(n_vars);
        for var in 0..n_vars {
            values.push(mgr.insert_var(format!("v{var}")).id());
        }
        values
    }

    #[test]
    fn unique_algs_node_count() {
        for n_vars in [0, 1, 5, 16] {
            let mut ids = Vec::with_capacity(UNIQUE_ALGS.len());
            for (name, unique_fn) in UNIQUE_ALGS {
                let mgr = BddManager::new();
                let unique = unique_fn(&mgr, &insert_vars(&mgr, n_vars));
                ids.push((name, unique));
            }
            let mut sorted = ids.clone();
            sorted.sort_by_key(|&(_, id)| id);
            assert_eq!(ids, sorted);
        }
    }

    #[test]
    fn unique_algs_equivalence() {
        for n_vars in [0, 1, 5, 16] {
            let mgr = BddManager::new();
            let values = insert_vars(&mgr, n_vars);
            let id = (UNIQUE_ALGS[0].1)(&mgr, &values);
            assert!(
                n_vars != 0 && !id.is_const() || n_vars == 0 && id == BddId::ZERO,
                "unique computed an unexpected value with {n_vars} variables: {id:?}",
            );
            for (name, unique_fn) in &UNIQUE_ALGS[1..] {
                let id2 = unique_fn(&mgr, &values);
                assert_eq!(id, id2, "{name} differs with {n_vars} variables");
            }
        }
    }
}
