use std::ops::{BitAnd, BitOr, BitXor, Not};

use crate::{Bdd, BddId, BddManager};

impl BddManager {
    /// Gets or inserts the BDD for a NOT expression.
    fn insert_not(&self, e: BddId) -> BddId {
        self.insert_ite(e, BddId::ZERO, BddId::ONE)
    }

    /// Gets or inserts the BDD for an AND expression.
    fn insert_and(&self, e1: BddId, e2: BddId) -> BddId {
        self.insert_ite(e1, e2, BddId::ZERO)
    }

    /// Gets or inserts the BDD for an OR expression.
    fn insert_or(&self, e1: BddId, e2: BddId) -> BddId {
        self.insert_ite(e1, BddId::ONE, e2)
    }

    /// Gets or inserts the BDD for an XOR expression.
    fn insert_xor(&self, e1: BddId, e2: BddId) -> BddId {
        let not_e2 = self.insert_not(e2);
        self.insert_ite(e1, not_e2, e2)
    }
}

macro_rules! unop(($Op:ident, $op:ident, $insert:ident) => {
    impl<'mgr> $Op for Bdd<'mgr> {
        type Output = Self;

        fn $op(self) -> Self::Output {
            self.manager().wrap(self.manager().$insert(self.id()))
        }
    }
});

macro_rules! binop(($Op:ident, $op:ident, $insert:ident) => {
    impl<'mgr> $Op for Bdd<'mgr> {
        type Output = Self;

        fn $op(self, rhs: Self) -> Self::Output {
            self.assert_manager(rhs);
            self.manager().wrap(self.manager().$insert(self.id(), rhs.id()))
        }
    }
});

unop!(Not, not, insert_not);
binop!(BitAnd, bitand, insert_and);
binop!(BitOr, bitor, insert_or);
binop!(BitXor, bitxor, insert_xor);