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
            values.push(mgr.variable(format!("{ident}{value}")).id());
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

    pub fn equals(&self, rhs: &Unary<'mgr>) -> Bdd<'mgr> {
        Bdd::assert_manager(self.mgr, rhs.mgr);
        assert_eq!(self.bounds, rhs.bounds, "unimplemented");
        let mut equal = self.mgr.zero();
        let mut none = self.mgr.one();
        for (&lv, &rv) in self.values.iter().zip(&rhs.values).rev() {
            let (lv, rv) = (self.mgr.wrap(lv), self.mgr.wrap(rv));
            let neither = !lv & !rv;
            equal = (neither & equal) | (lv & rv & none);
            none &= neither;
        }
        equal
    }

    pub fn lt(&self, rhs: &Unary<'mgr>) -> Bdd<'mgr> {
        Bdd::assert_manager(self.mgr, rhs.mgr);
        assert_eq!(self.bounds, rhs.bounds, "unimplemented");
        let mut compare = self.mgr.zero();
        let mut only_lhs = self.mgr.zero();
        let mut none = self.mgr.one();
        for (&lv, &rv) in self.values.iter().zip(&rhs.values) {
            let (lv, rv) = (self.mgr.wrap(lv), self.mgr.wrap(rv));
            let neither = !lv & !rv;
            compare = (neither & compare) | (!lv & rv & only_lhs);
            only_lhs = (neither & only_lhs) | (lv & !rv & none);
            none &= neither;
        }
        compare
    }

    pub fn le(&self, rhs: &Unary<'mgr>) -> Bdd<'mgr> {
        self.lt(rhs) | self.equals(rhs)
    }

    pub fn gt(&self, rhs: &Unary<'mgr>) -> Bdd<'mgr> {
        rhs.lt(self)
    }

    pub fn ge(&self, rhs: &Unary<'mgr>) -> Bdd<'mgr> {
        self.gt(rhs) | self.equals(rhs)
    }

    pub fn equals_const(&self, rhs: i64) -> Bdd<'mgr> {
        let index = Self::index(self.bounds.start, rhs);
        let mut equal = BddId::ONE;
        for (i, &v) in self.values.iter().enumerate().rev() {
            let var = self.mgr.get_node(v).as_var();
            equal = if i == index {
                self.mgr.insert_node(var, equal, BddId::ZERO)
            } else {
                self.mgr.insert_node(var, BddId::ZERO, equal)
            };
        }
        self.mgr.wrap(equal)
    }

    pub fn lt_const(&self, rhs: i64) -> Bdd<'mgr> {
        self.compare_const_index(rhs, |i, j| i < j)
    }

    pub fn le_const(&self, rhs: i64) -> Bdd<'mgr> {
        self.compare_const_index(rhs, |i, j| i <= j)
    }

    pub fn gt_const(&self, rhs: i64) -> Bdd<'mgr> {
        self.compare_const_index(rhs, |i, j| i > j)
    }

    pub fn ge_const(&self, rhs: i64) -> Bdd<'mgr> {
        self.compare_const_index(rhs, |i, j| i >= j)
    }

    pub fn even(&self) -> Bdd<'mgr> {
        self.compare_const(|i| i & 1 == 0)
    }

    pub fn odd(&self) -> Bdd<'mgr> {
        self.compare_const(|i| i & 1 == 1)
    }

    fn compare_const_index<F: Fn(usize, usize) -> bool>(
        &self,
        rhs: i64,
        cmp_index: F,
    ) -> Bdd<'mgr> {
        let index = Self::index(self.bounds.start, rhs);
        self.compare_const(|i| cmp_index(i, index))
    }

    fn compare_const<F: Fn(usize) -> bool>(&self, cmp_index: F) -> Bdd<'mgr> {
        let mut equal = BddId::ZERO;
        let mut none = BddId::ONE;
        for (i, &v) in self.values.iter().enumerate().rev() {
            let var = self.mgr.get_node(v).as_var();
            if cmp_index(i) {
                equal = self.mgr.insert_node(var, none, equal);
            } else if equal != BddId::ZERO {
                equal = self.mgr.insert_node(var, BddId::ZERO, equal);
            }
            none = self.mgr.insert_node(var, BddId::ZERO, none);
        }
        self.mgr.wrap(equal)
    }

    fn index(start: i64, value: i64) -> usize {
        value
            .checked_sub(start)
            .and_then(|len| len.try_into().ok())
            .unwrap()
    }
}

/// Computes the property that exactly one value can be set at once. This
/// construction is optimal in that no superfluous nodes are inserted. The given
/// values must be variable nodes and in sort order.
fn unique(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = BddId::ZERO;
    let mut none = BddId::ONE;
    for &v in values.iter().rev() {
        let var = mgr.get_node(v).as_var();
        unique = mgr.insert_node(var, none, unique);
        none = mgr.insert_node(var, BddId::ZERO, none);
    }
    unique
}

#[cfg(test)]
mod tests {
    use std::mem;

    use super::*;

    #[test]
    fn compare() {
        let mgr = BddManager::new();
        let a = Unary::new(&mgr, "a", 1..6);
        let b = Unary::new(&mgr, "b", 1..6);
        let found_a_unique = a.value();
        let found_b_unique = b.value();
        let found_eq = a.equals(&b);
        let found_lt = a.lt(&b);
        let found_gt = a.gt(&b);
        let found_le = a.le(&b);
        let found_ge = a.ge(&b);

        let a1 = mgr.variable("a1");
        let a2 = mgr.variable("a2");
        let a3 = mgr.variable("a3");
        let a4 = mgr.variable("a4");
        let a5 = mgr.variable("a5");
        let b1 = mgr.variable("b1");
        let b2 = mgr.variable("b2");
        let b3 = mgr.variable("b3");
        let b4 = mgr.variable("b4");
        let b5 = mgr.variable("b5");
        let a_unique = (a1 & !a2 & !a3 & !a4 & !a5)
            | (!a1 & a2 & !a3 & !a4 & !a5)
            | (!a1 & !a2 & a3 & !a4 & !a5)
            | (!a1 & !a2 & !a3 & a4 & !a5)
            | (!a1 & !a2 & !a3 & !a4 & a5);
        let b_unique = (b1 & !b2 & !b3 & !b4 & !b5)
            | (!b1 & b2 & !b3 & !b4 & !b5)
            | (!b1 & !b2 & b3 & !b4 & !b5)
            | (!b1 & !b2 & !b3 & b4 & !b5)
            | (!b1 & !b2 & !b3 & !b4 & b5);
        let a_eq_b = (a1 & b1) | (a2 & b2) | (a3 & b3) | (a4 & b4) | (a5 & b5);
        let a_lt_b =
            (a1 & (b2 | b3 | b4 | b5)) | (a2 & (b3 | b4 | b5)) | (a3 & (b4 | b5)) | (a4 & b5);
        let a_gt_b =
            (a2 & b1) | (a3 & (b1 | b2)) | (a4 & (b1 | b2 | b3)) | (a5 & (b1 | b2 | b3 | b4));
        let a_le_b = (a1 & (b1 | b2 | b3 | b4 | b5))
            | (a2 & (b2 | b3 | b4 | b5))
            | (a3 & (b3 | b4 | b5))
            | (a4 & (b4 | b5))
            | (a5 & b5);
        let a_ge_b = (a1 & b1)
            | (a2 & (b1 | b2))
            | (a3 & (b1 | b2 | b3))
            | (a4 & (b1 | b2 | b3 | b4))
            | (a5 & (b1 | b2 | b3 | b4 | b5));
        let expected_eq = a_eq_b & a_unique & b_unique;
        let expected_lt = a_lt_b & a_unique & b_unique;
        let expected_gt = a_gt_b & a_unique & b_unique;
        let expected_le = a_le_b & a_unique & b_unique;
        let expected_ge = a_ge_b & a_unique & b_unique;

        assert_eq!(found_a_unique, a_unique, "unique");
        assert_eq!(found_b_unique, b_unique, "unique");
        assert_eq!(found_eq, expected_eq, "eq");
        assert_eq!(found_lt, expected_lt, "lt");
        assert_eq!(found_le, expected_le, "le");
        assert_eq!(found_gt, expected_gt, "gt");
        assert_eq!(found_ge, expected_ge, "ge");
    }

    const UNIQUE_ALGS: [(
        &'static str,
        fn(mgr: &BddManager, values: &[BddId]) -> BddId,
    ); 7] = [
        ("unique", unique),
        ("unique_direct_ite", unique_direct_ite),
        ("unique_direct_or", unique_direct_or),
        ("unique_dynamic", unique_dynamic),
        ("unique_squared_pairs", unique_squared_pairs),
        ("unique_squared_grid", unique_squared_grid),
        ("unique_squared_grid2", unique_squared_grid2),
    ];

    fn unique_direct_ite(mgr: &BddManager, values: &[BddId]) -> BddId {
        let mut unique = BddId::ZERO;
        let mut none = BddId::ONE;
        for &v in values.iter().rev() {
            let not_v = mgr.not(v);
            unique = mgr.ite(v, none, unique);
            none = mgr.and(not_v, none);
        }
        unique
    }

    fn unique_direct_or(mgr: &BddManager, values: &[BddId]) -> BddId {
        let mut unique = BddId::ZERO;
        let mut none = BddId::ONE;
        for &v in values.iter().rev() {
            let not_v = mgr.not(v);
            unique = mgr.or(mgr.and(v, none), mgr.and(not_v, unique));
            none = mgr.and(not_v, none);
        }
        unique
    }

    fn unique_dynamic(mgr: &BddManager, values: &[BddId]) -> BddId {
        // Construct the expression from the bottom up, grouping values in
        // increasing powers of 2 and reusing subexpressions (dynamic
        // programming).
        if values.is_empty() {
            return BddId::ZERO;
        }
        let mut values = values.iter().map(|&v| (mgr.not(v), v)).collect::<Vec<_>>();
        let mut values2 = Vec::with_capacity((values.len() + 1) / 2);
        while values.len() > 1 {
            let mut chunks = values.chunks_exact(2);
            values2.clear();
            values2.extend(chunks.by_ref().map(|chunk| {
                let [(l0, l1), (r0, r1)] = chunk.try_into().unwrap();
                (mgr.and(l0, r0), mgr.or(mgr.and(l0, r1), mgr.and(l1, r0)))
            }));
            values2.extend(chunks.remainder());
            mem::swap(&mut values, &mut values2);
        }
        values[0].1
    }

    fn unique_squared_pairs(mgr: &BddManager, values: &[BddId]) -> BddId {
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

    fn unique_squared_grid(mgr: &BddManager, values: &[BddId]) -> BddId {
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

    fn unique_squared_grid2(mgr: &BddManager, values: &[BddId]) -> BddId {
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

    fn insert_variables(mgr: &BddManager, n_vars: usize) -> Vec<BddId> {
        let mut values = Vec::with_capacity(n_vars);
        for var in 0..n_vars {
            values.push(mgr.variable(format!("v{var}")).id());
        }
        values
    }

    #[test]
    fn unique_algs_node_count() {
        for n_vars in [0, 1, 5, 16] {
            let mut ids = Vec::with_capacity(UNIQUE_ALGS.len());
            for (name, unique_fn) in UNIQUE_ALGS {
                let mgr = BddManager::new();
                let id = unique_fn(&mgr, &insert_variables(&mgr, n_vars));
                ids.push((name, id));
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
            let values = insert_variables(&mgr, n_vars);
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
