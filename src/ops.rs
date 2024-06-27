use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

use crate::{Bdd, BddId, BddManager, VarReplaceMap};

impl BddManager {
    /// Gets or inserts the BDD for a NOT expression.
    pub(crate) fn not(&self, e: BddId) -> BddId {
        self.ite(e, BddId::ZERO, BddId::ONE)
    }

    /// Gets or inserts the BDD for an AND expression.
    pub(crate) fn and(&self, e1: BddId, e2: BddId) -> BddId {
        self.ite(e1, e2, BddId::ZERO)
    }

    /// Gets or inserts the BDD for an OR expression.
    pub(crate) fn or(&self, e1: BddId, e2: BddId) -> BddId {
        self.ite(e1, BddId::ONE, e2)
    }

    /// Gets or inserts the BDD for an XOR expression.
    pub(crate) fn xor(&self, e1: BddId, e2: BddId) -> BddId {
        self.ite(e1, self.not(e2), e2)
    }

    /// Gets or inserts the BDD for an implication expression.
    pub(crate) fn imply(&self, e1: BddId, e2: BddId) -> BddId {
        self.ite(self.not(e1), BddId::ONE, e2)
    }

    /// Gets or inserts the BDD for a bidirectional implication expression.
    pub(crate) fn equals(&self, e1: BddId, e2: BddId) -> BddId {
        self.or(self.and(e1, e2), self.and(self.not(e1), self.not(e2)))
    }
}

impl<'mgr> Bdd<'mgr> {
    /// Gets or inserts the BDD for an if-then-else expression.
    #[inline]
    pub fn ite(&self, e_then: Bdd<'mgr>, e_else: Bdd<'mgr>) -> Bdd<'mgr> {
        self.assert_manager(e_then.mgr);
        self.assert_manager(e_else.mgr);
        self.mgr.wrap(self.mgr.ite(self.id, e_then.id, e_else.id))
    }

    /// Gets or inserts the BDD for an implication expression.
    #[inline]
    pub fn imply(&self, rhs: Bdd<'mgr>) -> Bdd<'mgr> {
        self.assert_manager(rhs.mgr);
        self.mgr.wrap(self.mgr.imply(self.id, rhs.id))
    }

    /// Gets or inserts the BDD for a bidirectional implication expression.
    #[inline]
    pub fn equals(&self, rhs: Bdd<'mgr>) -> Bdd<'mgr> {
        self.assert_manager(rhs.mgr);
        self.mgr.wrap(self.mgr.equals(self.id, rhs.id))
    }

    /// Creates a BDD isomorphic to self with the variables replaced according
    /// to this mapping.
    #[inline]
    pub fn replace(&self, map: &VarReplaceMap<'mgr>) -> Bdd<'mgr> {
        self.assert_manager(map.mgr);
        self.mgr
            .wrap(self.mgr.replace(self.id, &map.replace))
    }
}

macro_rules! unop(($Op:ident $op:ident => $insert:ident) => {
    impl<'mgr> $Op for Bdd<'mgr> {
        type Output = Self;

        #[inline]
        fn $op(self) -> Self::Output {
            self.mgr.wrap(self.mgr.$insert(self.id))
        }
    }
});

macro_rules! binop(($Op:ident $op:ident, $OpAssign:ident $op_assign:ident => $insert:ident) => {
    impl<'mgr> $Op for Bdd<'mgr> {
        type Output = Self;

        #[inline]
        fn $op(self, rhs: Self) -> Self::Output {
            self.assert_manager(rhs.mgr);
            self.mgr.wrap(self.mgr.$insert(self.id, rhs.id))
        }
    }

    impl<'mgr> $OpAssign for Bdd<'mgr> {
        #[inline]
        fn $op_assign(&mut self, rhs: Self) {
            self.assert_manager(rhs.mgr);
            self.id = self.mgr.$insert(self.id, rhs.id);
        }
    }
});

unop!(Not not => not);
binop!(BitAnd bitand, BitAndAssign bitand_assign => and);
binop!(BitOr bitor, BitOrAssign bitor_assign => or);
binop!(BitXor bitxor, BitXorAssign bitxor_assign => xor);
