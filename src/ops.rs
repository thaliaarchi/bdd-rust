use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Sub, SubAssign,
};

use crate::{Bdd, BddId, BddManager, VarReplaceMap};

impl BddManager {
    /// Computes Boolean NOT.
    pub(crate) fn not(&self, x: BddId) -> BddId {
        self.ite(x, BddId::ZERO, BddId::ONE)
    }

    /// Computes Boolean AND.
    pub(crate) fn and(&self, x: BddId, y: BddId) -> BddId {
        self.ite(x, y, BddId::ZERO)
    }

    /// Computes Boolean OR.
    pub(crate) fn or(&self, x: BddId, y: BddId) -> BddId {
        self.ite(x, BddId::ONE, y)
    }

    /// Computes Boolean XOR.
    pub(crate) fn xor(&self, x: BddId, y: BddId) -> BddId {
        self.ite(x, self.not(y), y)
    }

    /// Computes Boolean difference.
    pub(crate) fn sub(&self, x: BddId, y: BddId) -> BddId {
        self.ite(y, BddId::ZERO, x)
    }

    /// Computes Boolean implication.
    pub(crate) fn imply(&self, x: BddId, y: BddId) -> BddId {
        self.ite(x, y, BddId::ONE)
    }

    /// Computes Boolean bidirectional implication.
    pub(crate) fn equals(&self, x: BddId, y: BddId) -> BddId {
        self.ite(x, y, self.not(y))
    }

    /// Computes single-bit addition with carry, i.e., a half adder. Returns sum
    /// and carry bits.
    pub(crate) fn add_carry(&self, x: BddId, y: BddId) -> (BddId, BddId) {
        (self.xor(x, y), self.and(x, y))
    }

    /// Computes single-bit addition with carry in and out, i.e., a full adder.
    /// Returns sum and carry bits.
    pub(crate) fn add_carry_in(&self, x: BddId, y: BddId, c: BddId) -> (BddId, BddId) {
        let xy = self.xor(x, y);
        let z = self.xor(xy, c);
        let c = self.or(self.and(xy, c), self.and(x, y));
        (z, c)
    }

    /// Computes the property that exactly one value is true.
    pub(crate) fn unique(&self, values: &[BddId]) -> BddId {
        let mut unique = BddId::ZERO;
        let mut none = BddId::ONE;
        for &v in values.iter().rev() {
            unique = self.ite(v, none, unique);
            none = self.ite(v, BddId::ZERO, none);
        }
        unique
    }

    /// Computes the property that exactly one value is true. The given values
    /// must be variable nodes. This construction is optimal when the BDDs are
    /// variable nodes in increasing `Var` order.
    pub(crate) fn unique_vars(&self, vars: &[BddId]) -> BddId {
        let mut unique = BddId::ZERO;
        let mut none = BddId::ONE;
        for &v in vars.iter().rev() {
            let var = self.get_node(v).as_var();
            unique = self.insert_node(var, none, unique);
            none = self.insert_node(var, BddId::ZERO, none);
        }
        unique
    }
}

impl<'mgr> Bdd<'mgr> {
    /// Computes an if-then-else expression.
    #[inline]
    pub fn ite(&self, e_then: Self, e_else: Self) -> Self {
        Self::assert_manager(self.mgr, e_then.mgr);
        Self::assert_manager(self.mgr, e_else.mgr);
        self.mgr.wrap(self.mgr.ite(self.id, e_then.id, e_else.id))
    }

    /// Computes implication.
    #[inline]
    pub fn imply(&self, rhs: Self) -> Self {
        Self::assert_manager(self.mgr, rhs.mgr);
        self.mgr.wrap(self.mgr.imply(self.id, rhs.id))
    }

    /// Computes bidirectional implication.
    #[inline]
    pub fn equals(&self, rhs: Self) -> Self {
        Self::assert_manager(self.mgr, rhs.mgr);
        self.mgr.wrap(self.mgr.equals(self.id, rhs.id))
    }

    /// Computes single-bit addition with carry, i.e., a half adder. Returns sum
    /// and carry bits.
    #[inline]
    pub fn add_carry(&self, rhs: Self) -> (Self, Self) {
        Self::assert_manager(self.mgr, rhs.mgr);
        let (sum, carry) = self.mgr.add_carry(self.id, rhs.id);
        (self.mgr.wrap(sum), self.mgr.wrap(carry))
    }

    /// Computes single-bit addition with carry in and out, i.e., a full adder.
    /// Returns sum and carry bits.
    #[inline]
    pub fn add_carry_in(&self, rhs: Self, carry_in: Self) -> (Self, Self) {
        Self::assert_manager(self.mgr, rhs.mgr);
        Self::assert_manager(self.mgr, carry_in.mgr);
        let (sum, carry) = self.mgr.add_carry_in(self.id, rhs.id, carry_in.id);
        (self.mgr.wrap(sum), self.mgr.wrap(carry))
    }

    /// Creates a BDD isomorphic to self with the variables replaced according
    /// to this mapping.
    #[inline]
    pub fn replace(&self, map: &VarReplaceMap<'mgr>) -> Self {
        Self::assert_manager(self.mgr, map.mgr);
        self.mgr.wrap(self.mgr.replace(self.id, &map.replace))
    }
}

macro_rules! unop(($Op:ident $op:ident => $compute:ident) => {
    impl<'mgr> $Op for Bdd<'mgr> {
        type Output = Self;

        #[inline]
        fn $op(self) -> Self::Output {
            self.mgr.wrap(self.mgr.$compute(self.id))
        }
    }
});

macro_rules! binop(($Op:ident $op:ident, $OpAssign:ident $op_assign:ident => $compute:ident) => {
    impl<'mgr> $Op for Bdd<'mgr> {
        type Output = Self;

        #[inline]
        fn $op(self, rhs: Self) -> Self::Output {
            Self::assert_manager(self.mgr, rhs.mgr);
            self.mgr.wrap(self.mgr.$compute(self.id, rhs.id))
        }
    }

    impl<'mgr> $OpAssign for Bdd<'mgr> {
        #[inline]
        fn $op_assign(&mut self, rhs: Self) {
            Self::assert_manager(self.mgr, rhs.mgr);
            self.id = self.mgr.$compute(self.id, rhs.id);
        }
    }
});

unop!(Not not => not);
binop!(Sub sub, SubAssign sub_assign => sub);
binop!(BitAnd bitand, BitAndAssign bitand_assign => and);
binop!(BitOr bitor, BitOrAssign bitor_assign => or);
binop!(BitXor bitxor, BitXorAssign bitxor_assign => xor);
