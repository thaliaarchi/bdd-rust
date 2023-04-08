use std::collections::{hash_map::Entry, HashMap};
use std::fmt::{self, Debug, Display, Formatter};

use crate::{Exp, Var};

/// A reduced ordered binary decision diagram (ROBDD).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bdd {
    by_id: Vec<BddNode>,
    by_node: HashMap<BddNode, BddId>,
}

/// A sub-graph of a `Bdd`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BddId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BddNode {
    var: Var,
    high: BddId,
    low: BddId,
}

impl BddId {
    pub const ZERO: BddId = BddId(0);
    pub const ONE: BddId = BddId(1);

    #[inline]
    fn new(id: usize) -> Self {
        BddId(id)
    }

    #[inline]
    fn as_usize(&self) -> usize {
        self.0
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 1
    }
}

impl BddNode {
    #[inline]
    fn new(var: Var, high: BddId, low: BddId) -> Self {
        BddNode { var, high, low }
    }

    fn cofactor(&self, self_id: BddId, var: Var) -> (BddId, BddId) {
        if self.var == var {
            (self.high, self.low)
        } else {
            (self_id, self_id)
        }
    }
}

impl Bdd {
    /// Create a `Bdd` initialized with the variables in the range `0..vars`.
    pub fn new(vars: usize) -> Self {
        let mut by_id = Vec::with_capacity(vars.checked_add(2).unwrap());
        by_id.push(BddNode::new(Var::ZERO, BddId::ZERO, BddId::ZERO));
        by_id.push(BddNode::new(Var::ONE, BddId::ONE, BddId::ONE));
        for i in 0..vars {
            by_id.push(BddNode::new(Var::new(i), BddId::ONE, BddId::ZERO));
        }
        let mut by_node = HashMap::with_capacity(by_id.len());
        for (i, &node) in by_id.iter().enumerate() {
            by_node.insert(node, BddId(i));
        }
        Bdd { by_id, by_node }
    }

    /// Get or insert the BDD for a node.
    pub fn insert_node(&mut self, node: BddNode) -> BddId {
        match self.by_node.entry(node) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = BddId::new(self.by_id.len());
                self.by_id.push(node);
                entry.insert(id);
                id
            }
        }
    }

    /// Get or insert the BDD for a variable.
    #[inline]
    pub fn insert_var(&mut self, var: Var) -> BddId {
        self.insert_node(BddNode::new(var, BddId::ONE, BddId::ZERO))
    }

    /// Get or insert the BDD for a NOT expression.
    #[inline]
    pub fn insert_not(&mut self, bdd_e: BddId) -> BddId {
        self.insert_ite(bdd_e, BddId::ZERO, BddId::ONE)
    }

    /// Get or insert the BDD for an AND expression.
    #[inline]
    pub fn insert_and(&mut self, bdd_e1: BddId, bdd_e2: BddId) -> BddId {
        self.insert_ite(bdd_e1, bdd_e2, BddId::ZERO)
    }

    /// Get or insert the BDD for an OR expression.
    #[inline]
    pub fn insert_or(&mut self, bdd_e1: BddId, bdd_e2: BddId) -> BddId {
        self.insert_ite(bdd_e1, BddId::ONE, bdd_e2)
    }

    /// Get or insert the BDD for an if-then-else expression.
    pub fn insert_ite(&mut self, bdd_if: BddId, bdd_then: BddId, bdd_else: BddId) -> BddId {
        // Terminal cases
        if bdd_then.is_one() && bdd_else.is_zero() {
            return bdd_if;
        } else if bdd_if.is_one() || bdd_then == bdd_else {
            return bdd_then;
        } else if bdd_if.is_zero() {
            return bdd_else;
        }

        let node_if = self.by_id[bdd_if.as_usize()];
        let node_then = self.by_id[bdd_then.as_usize()];
        let node_else = self.by_id[bdd_else.as_usize()];

        // Cofactor each sub-function by the minimum variable
        let var = node_if.var.min(node_then.var).min(node_else.var);
        let (co1_if, co0_if) = node_if.cofactor(bdd_if, var);
        let (co1_then, co0_then) = node_then.cofactor(bdd_then, var);
        let (co1_else, co0_else) = node_else.cofactor(bdd_else, var);

        // Recurse on the cofactors until every variable has been expanded
        let co1 = self.insert_ite(co1_if, co1_then, co1_else);
        let co0 = self.insert_ite(co0_if, co0_then, co0_else);

        // Insert the resulting node
        self.insert_node(BddNode::new(var, co1, co0))
    }

    /// Get or insert the BDD for an expression.
    pub fn insert_exp(&mut self, e: &Exp) -> BddId {
        match e {
            Exp::Var(var) => self.insert_var(*var),
            Exp::Not(e) => {
                let bdd_e = self.insert_exp(e);
                self.insert_not(bdd_e)
            }
            Exp::And(e1, e2) => {
                let bdd_e1 = self.insert_exp(e1);
                let bdd_e2 = self.insert_exp(e2);
                self.insert_and(bdd_e1, bdd_e2)
            }
            Exp::Or(e1, e2) => {
                let bdd_e1 = self.insert_exp(e1);
                let bdd_e2 = self.insert_exp(e2);
                self.insert_or(bdd_e1, bdd_e2)
            }
        }
    }
}

impl Display for Bdd {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "| Var | High | Low | Id |\n")?;
        write!(f, "| --- | ---- | --- | -- |\n")?;
        for (id, &BddNode { var, high, low }) in self.by_id.iter().enumerate() {
            write!(f, "| {var} | {} | {} | {id} |\n", high.0, low.0)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_exp() {
        let f = Exp::or(
            Exp::or(
                Exp::and(Exp::var(0), Exp::var(1)),
                Exp::and(Exp::not(Exp::var(0)), Exp::var(2)),
            ),
            Exp::and(Exp::and(Exp::var(1), Exp::not(Exp::var(2))), Exp::var(3)),
        );
        let mut bdd = Bdd::new(4);
        bdd.insert_exp(&f);
        let expected = vec![
            BddNode::new(Var::ZERO, BddId::ZERO, BddId::ZERO),
            BddNode::new(Var::ONE, BddId::ONE, BddId::ONE),
            BddNode::new(Var::new(0), BddId::new(1), BddId::new(0)),
            BddNode::new(Var::new(1), BddId::new(1), BddId::new(0)),
            BddNode::new(Var::new(2), BddId::new(1), BddId::new(0)),
            BddNode::new(Var::new(3), BddId::new(1), BddId::new(0)),
            BddNode::new(Var::new(0), BddId::new(3), BddId::new(0)),
            BddNode::new(Var::new(0), BddId::new(0), BddId::new(1)),
            BddNode::new(Var::new(0), BddId::new(0), BddId::new(4)),
            BddNode::new(Var::new(0), BddId::new(3), BddId::new(4)),
            BddNode::new(Var::new(2), BddId::new(0), BddId::new(1)),
            BddNode::new(Var::new(1), BddId::new(10), BddId::new(0)),
            BddNode::new(Var::new(2), BddId::new(0), BddId::new(5)),
            BddNode::new(Var::new(1), BddId::new(12), BddId::new(0)),
            BddNode::new(Var::new(2), BddId::new(1), BddId::new(5)),
            BddNode::new(Var::new(1), BddId::new(14), BddId::new(4)),
            BddNode::new(Var::new(0), BddId::new(3), BddId::new(15)),
        ];
        assert_eq!(expected, bdd.by_id);
    }
}
