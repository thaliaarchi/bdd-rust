use std::collections::{hash_map::Entry, HashMap};
use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt::{self, Debug, Display, Formatter, Write};

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
    pub var: Var,
    pub high: BddId,
    pub low: BddId,
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

    /// Return whether the BDD is either 0 or 1.
    #[inline]
    pub fn is_const(&self) -> bool {
        self.0 <= 1
    }

    /// Return whether the BDD is 0.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    /// Return whether the BDD is 1.
    #[inline]
    pub fn is_one(&self) -> bool {
        self.0 == 1
    }
}

impl BddNode {
    #[inline]
    fn new(var: Var, high: BddId, low: BddId) -> Self {
        BddNode { var, high, low }
    }

    /// Split into expressions `co1`, `co0`, that have `var` factored out, such
    /// that `(var ∧ co1) ∨ (¬var ∧ co0)`.
    #[inline]
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

    /// Get the node for the BDD id.
    #[inline]
    pub fn get(&self, id: BddId) -> BddNode {
        self.by_id[id.as_usize()]
    }

    /// Get or insert the BDD for a node.
    fn insert_node(&mut self, node: BddNode) -> BddId {
        if node.high == node.low {
            return node.high;
        }
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

        let node_if = self.get(bdd_if);
        let node_then = self.get(bdd_then);
        let node_else = self.get(bdd_else);

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

    /// Create a new BDD from `id` with the variables replaced according to the
    /// mappings in `replace`.
    pub fn replace(&mut self, id: BddId, replace: &HashMap<Var, Var>) -> BddId {
        if id.is_const() {
            return id;
        }
        let node = self.get(id);
        let var = replace.get(&node.var).copied().unwrap_or(node.var);
        let var = self.insert_var(var);
        let high = self.replace(node.high, replace);
        let low = self.replace(node.low, replace);
        self.insert_ite(var, high, low)
    }

    pub fn post_order(&self, id: BddId) -> Vec<BddId> {
        let mut post_order = Vec::new();
        let mut visited = HashSet::new();
        self.append_post_order(id, &mut post_order, &mut visited);
        post_order
    }

    pub fn append_post_order(
        &self,
        id: BddId,
        post_order: &mut Vec<BddId>,
        visited: &mut HashSet<BddId>,
    ) {
        if visited.insert(id) {
            let node = self.get(id);
            self.append_post_order(node.high, post_order, visited);
            self.append_post_order(node.low, post_order, visited);
            post_order.push(id);
        }
    }

    pub fn reachable(&self, id: BddId) -> BTreeSet<BddId> {
        let mut reachable = BTreeSet::new();
        self.append_reachable(id, &mut reachable);
        reachable
    }

    pub fn append_reachable(&self, id: BddId, reachable: &mut BTreeSet<BddId>) {
        if reachable.insert(id) {
            let node = self.get(id);
            self.append_reachable(node.high, reachable);
            self.append_reachable(node.low, reachable);
        }
    }

    /// Display the BDD as a GraphViz directed graph.
    pub fn digraph(&self, w: &mut (dyn Write), id: BddId) -> fmt::Result {
        let reachable = self.reachable(id);
        let mut ranks = BTreeMap::<Var, Vec<BddId>>::new();
        writeln!(w, "digraph bdd{id} {{")?;
        for id in reachable {
            let node = self.get(id);
            if id.is_const() {
                writeln!(w, "    node{id} [label={id}, shape=square];")?;
            } else {
                writeln!(
                    w,
                    "    node{id} [label={}, xlabel={id}, shape=circle];",
                    node.var
                )?;
                writeln!(w, "    node{id} -> node{};", node.high)?;
                writeln!(w, "    node{id} -> node{} [style=dashed];", node.low)?;
                ranks.entry(node.var).or_default().push(id);
            }
        }
        writeln!(w)?;
        for (_, nodes) in ranks {
            write!(w, "    {{ rank=same; ")?;
            for id in nodes {
                write!(w, "node{id}; ")?;
            }
            writeln!(w, "}}")?;
        }
        writeln!(w, "}}")
    }
}

impl Display for Bdd {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "| Var | High | Low | Id |")?;
        writeln!(f, "| --- | ---- | --- | -- |")?;
        for (id, &BddNode { var, high, low }) in self.by_id.iter().enumerate() {
            writeln!(f, "| {var} | {high} | {low} | {id} |")?;
        }
        Ok(())
    }
}

impl Display for BddId {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_exp_and_replace() {
        const A: usize = 0;
        const B: usize = 1;
        const C: usize = 2;
        const D: usize = 3;
        // (a ∧ b) ∨ (¬a ∧ c) ∨ (b ∧ ¬c ∧ d)
        let f = Exp::or(
            Exp::or(
                Exp::and(Exp::var(A), Exp::var(B)),
                Exp::and(Exp::not(Exp::var(A)), Exp::var(C)),
            ),
            Exp::and(Exp::and(Exp::var(B), Exp::not(Exp::var(C))), Exp::var(D)),
        );
        let mut bdd = Bdd::new(4);
        let id = bdd.insert_exp(&f);
        let mut expected = vec![
            BddNode::new(Var::ZERO, BddId::ZERO, BddId::ZERO), // 0
            BddNode::new(Var::ONE, BddId::ONE, BddId::ONE),    // 1
            BddNode::new(Var::new(A), BddId::new(1), BddId::new(0)), // 2
            BddNode::new(Var::new(B), BddId::new(1), BddId::new(0)), // 3
            BddNode::new(Var::new(C), BddId::new(1), BddId::new(0)), // 4
            BddNode::new(Var::new(D), BddId::new(1), BddId::new(0)), // 5
            BddNode::new(Var::new(A), BddId::new(3), BddId::new(0)), // 6
            BddNode::new(Var::new(A), BddId::new(0), BddId::new(1)), // 7
            BddNode::new(Var::new(A), BddId::new(0), BddId::new(4)), // 8
            BddNode::new(Var::new(A), BddId::new(3), BddId::new(4)), // 9
            BddNode::new(Var::new(C), BddId::new(0), BddId::new(1)), // 10
            BddNode::new(Var::new(B), BddId::new(10), BddId::new(0)), // 11
            BddNode::new(Var::new(C), BddId::new(0), BddId::new(5)), // 12
            BddNode::new(Var::new(B), BddId::new(12), BddId::new(0)), // 13
            BddNode::new(Var::new(C), BddId::new(1), BddId::new(5)), // 14
            BddNode::new(Var::new(B), BddId::new(14), BddId::new(4)), // 15
            BddNode::new(Var::new(A), BddId::new(3), BddId::new(15)), // 16
        ];
        assert_eq!(expected, bdd.by_id);
        assert_eq!(BddId::new(16), id);

        const E: usize = 4;
        const F: usize = 5;
        // (a ∧ b) ∨ (¬a ∧ f) ∨ (b ∧ ¬f ∧ e)
        let mut replace = HashMap::new();
        replace.insert(Var::new(C), Var::new(F));
        replace.insert(Var::new(D), Var::new(E));
        bdd.insert_var(Var::new(E));
        bdd.insert_var(Var::new(F));
        let replaced = bdd.replace(id, &replace);
        expected.extend(&[
            BddNode::new(Var::new(E), BddId::new(1), BddId::new(0)), // 17
            BddNode::new(Var::new(F), BddId::new(1), BddId::new(0)), // 18
            BddNode::new(Var::new(E), BddId::new(1), BddId::new(18)), // 19
            BddNode::new(Var::new(B), BddId::new(19), BddId::new(18)), // 20
            BddNode::new(Var::new(A), BddId::new(3), BddId::new(20)), // 21
        ]);
        assert_eq!(expected, bdd.by_id);
        assert_eq!(BddId::new(21), replaced);
    }
}
