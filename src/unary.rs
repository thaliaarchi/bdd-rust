use std::ops::Range;

use crate::{Bdd, BddId, BddManager};

/// An integer, which bounded to a range and counted in unary. Alternatively, an
/// enum.
#[derive(Clone, Debug)]
pub struct Unary<'mgr> {
    values: Vec<BddId>,
    bounds: Range<i64>,
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
        Unary {
            values,
            bounds,
            mgr,
        }
    }

    pub fn get(&self, other: i64) -> Bdd<'mgr> {
        self.mgr
            .wrap(self.values[Unary::index(self.bounds.start, other)])
    }

    /// Computes the property that exactly one value can be set at once.
    pub fn value(&self) -> Bdd<'_> {
        self.mgr.wrap(self.mgr.unique_vars(&self.values))
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

#[cfg(test)]
mod tests {
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
}
