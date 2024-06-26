use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::{self, Debug, Display, Formatter, Write},
};

use crate::index_map::{IndexKey, IndexMap};

/// A reduced ordered binary decision diagram (ROBDD).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bdd {
    nodes: IndexMap<BddId, BddNode>,
    vars: IndexMap<Var, String>,
}

/// A sub-graph of a `Bdd`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BddId(u32);

/// A boolean variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BddNode {
    pub var: Var,
    pub high: BddId,
    pub low: BddId,
}

/// A mapping for replacing variables in a BDD.
#[derive(Debug)]
pub struct VarReplaceMap<'bdd> {
    bdd: &'bdd mut Bdd,
    replace: HashMap<Var, Var>,
}

impl Bdd {
    /// Constructs a new, empty `Bdd`.
    pub fn new() -> Self {
        let mut nodes = IndexMap::new();
        nodes.insert(BddNode::new(Var::ZERO, BddId::ZERO, BddId::ZERO));
        nodes.insert(BddNode::new(Var::ONE, BddId::ONE, BddId::ONE));
        Bdd {
            nodes,
            vars: IndexMap::new(),
        }
    }

    /// Gets the node for the BDD id.
    #[inline]
    pub fn get(&self, id: BddId) -> BddNode {
        self.nodes[id]
    }

    fn get_var(&self, var: Var) -> &str {
        match var.0 {
            0 => "0",
            1 => "1",
            _ => &self.vars[var],
        }
    }

    /// Gets or inserts the BDD for a variable.
    pub fn insert_var<S: Into<String>>(&mut self, ident: S) -> BddId {
        let var = self.vars.insert(ident.into());
        self.insert_var_id(var)
    }

    pub fn insert_var_id(&mut self, var: Var) -> BddId {
        self.nodes
            .insert(BddNode::new(var, BddId::ONE, BddId::ZERO))
    }

    /// Gets or inserts the BDD for a NOT expression.
    #[inline]
    pub fn insert_not(&mut self, bdd_e: BddId) -> BddId {
        self.insert_ite(bdd_e, BddId::ZERO, BddId::ONE)
    }

    /// Gets or inserts the BDD for an AND expression.
    #[inline]
    pub fn insert_and(&mut self, bdd_e1: BddId, bdd_e2: BddId) -> BddId {
        self.insert_ite(bdd_e1, bdd_e2, BddId::ZERO)
    }

    /// Gets or inserts the BDD for an OR expression.
    #[inline]
    pub fn insert_or(&mut self, bdd_e1: BddId, bdd_e2: BddId) -> BddId {
        self.insert_ite(bdd_e1, BddId::ONE, bdd_e2)
    }

    /// Gets or inserts the BDD for an XOR expression.
    #[inline]
    pub fn insert_xor(&mut self, bdd_e1: BddId, bdd_e2: BddId) -> BddId {
        let bdd_e2_not = self.insert_not(bdd_e2);
        self.insert_ite(bdd_e1, bdd_e2_not, bdd_e2)
    }

    /// Gets or inserts the BDD for an if-then-else expression.
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
        if co1 == co0 {
            return co1;
        }
        self.nodes.insert(BddNode::new(var, co1, co0))
    }

    /// Creates a map, which can be used to replace variables in this BDD.
    pub fn replace_vars(&mut self) -> VarReplaceMap<'_> {
        VarReplaceMap {
            bdd: self,
            replace: HashMap::new(),
        }
    }

    /// Creates a new BDD from `id` with the variables replaced according to the
    /// mappings in `replace`.
    fn insert_replace(&mut self, id: BddId, replace: &HashMap<Var, Var>) -> BddId {
        if id.is_const() {
            return id;
        }
        let node = self.get(id);
        let var = replace.get(&node.var).copied().unwrap_or(node.var);
        let var = self.insert_var_id(var);
        let high = self.insert_replace(node.high, replace);
        let low = self.insert_replace(node.low, replace);
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

    /// Displays the BDD as a GraphViz directed graph.
    pub fn digraph(&self, w: &mut dyn Write, id: BddId) -> fmt::Result {
        let reachable = self.reachable(id);
        let mut ranks = BTreeMap::<Var, Vec<BddId>>::new();
        writeln!(w, "digraph bdd{} {{", id.0)?;
        for id in reachable {
            let node = self.get(id);
            if id.is_const() {
                writeln!(w, "    node{} [label={}, shape=square];", id.0, id.0)?;
            } else {
                writeln!(
                    w,
                    "    node{} [label={}, xlabel={}, shape=circle];",
                    id.0,
                    self.get_var(node.var),
                    id.0,
                )?;
                writeln!(w, "    node{} -> node{};", id.0, node.high.0)?;
                writeln!(w, "    node{} -> node{} [style=dashed];", id.0, node.low.0)?;
                ranks.entry(node.var).or_default().push(id);
            }
        }
        if !ranks.is_empty() {
            writeln!(w)?;
        }
        for (_, nodes) in ranks {
            write!(w, "    {{ rank=same; ")?;
            for id in nodes {
                write!(w, "node{}; ", id.0)?;
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
        for (id, &BddNode { var, high, low }) in &self.nodes {
            writeln!(
                f,
                "| {} | {} | {} | {} |",
                self.get_var(var),
                high.0,
                low.0,
                id.0,
            )?;
        }
        Ok(())
    }
}

impl BddId {
    pub const ZERO: BddId = BddId(0);
    pub const ONE: BddId = BddId(1);

    #[cfg(test)]
    #[inline]
    fn new(id: usize) -> Self {
        BddId::from_usize(id)
    }

    /// Returns whether the BDD is either 0 or 1.
    #[inline]
    pub fn is_const(&self) -> bool {
        self.0 <= 1
    }

    /// Returns whether the BDD is 0.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }

    /// Returns whether the BDD is 1.
    #[inline]
    pub fn is_one(&self) -> bool {
        self.0 == 1
    }
}

impl IndexKey for BddId {
    #[inline]
    fn from_usize(index: usize) -> Self {
        BddId(index as u32)
    }

    #[inline]
    fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

impl Var {
    pub const ZERO: Var = Var(0);
    pub const ONE: Var = Var(1);
}

impl IndexKey for Var {
    fn from_usize(index: usize) -> Self {
        Var(index as u32 + 2)
    }

    fn as_usize(&self) -> usize {
        self.0 as usize - 2
    }
}

impl PartialOrd for Var {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Var {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        // Order variables first, then 0, then 1
        self.0.wrapping_sub(2).cmp(&other.0.wrapping_sub(2))
    }
}

impl BddNode {
    #[inline]
    fn new(var: Var, high: BddId, low: BddId) -> Self {
        BddNode { var, high, low }
    }

    /// Splits into expressions `co1`, `co0`, that have `var` factored out, such
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

impl<'bdd> VarReplaceMap<'bdd> {
    /// Inserts a mapping from `original` to `replacement`.
    pub fn insert<S: Into<String>>(&mut self, original: S, replacement: S) {
        let original = self.bdd.vars.insert(original.into());
        let replacement = self.bdd.vars.insert(replacement.into());
        self.replace.insert(original, replacement);
    }

    /// Creates a new BDD from `id` with the variables replaced according to
    /// this mapping.
    pub fn replace(&mut self, id: BddId) -> BddId {
        self.bdd.insert_replace(id, &mut self.replace)
    }
}

#[cfg(test)]
mod tests {
    use crate::Exp;

    use super::*;

    #[test]
    fn insert_exp_and_replace() {
        let a = Exp::var("a");
        let b = Exp::var("b");
        let c = Exp::var("c");
        let d = Exp::var("d");
        // (a ∧ b) ∨ (¬a ∧ c) ∨ (b ∧ ¬c ∧ d)
        let f = Exp::or(
            Exp::or(
                Exp::and(a.clone(), b.clone()),
                Exp::and(Exp::not(a), c.clone()),
            ),
            Exp::and(Exp::and(b, Exp::not(c)), d),
        );
        let mut bdd = Bdd::new();
        let id = bdd.insert_exp(&f);
        let a = Var::from_usize(0);
        let b = Var::from_usize(1);
        let c = Var::from_usize(2);
        let d = Var::from_usize(3);
        let mut expected = vec![
            BddNode::new(Var::ZERO, BddId::ZERO, BddId::ZERO), // 0
            BddNode::new(Var::ONE, BddId::ONE, BddId::ONE),    // 1
            BddNode::new(a, BddId::new(1), BddId::new(0)),     // 2
            BddNode::new(b, BddId::new(1), BddId::new(0)),     // 3
            BddNode::new(a, BddId::new(3), BddId::new(0)),     // 4
            BddNode::new(a, BddId::new(0), BddId::new(1)),     // 5
            BddNode::new(c, BddId::new(1), BddId::new(0)),     // 6
            BddNode::new(a, BddId::new(0), BddId::new(6)),     // 7
            BddNode::new(a, BddId::new(3), BddId::new(6)),     // 8
            BddNode::new(c, BddId::new(0), BddId::new(1)),     // 9
            BddNode::new(b, BddId::new(9), BddId::new(0)),     // 10
            BddNode::new(d, BddId::new(1), BddId::new(0)),     // 11
            BddNode::new(c, BddId::new(0), BddId::new(11)),    // 12
            BddNode::new(b, BddId::new(12), BddId::new(0)),    // 13
            BddNode::new(c, BddId::new(1), BddId::new(11)),    // 14
            BddNode::new(b, BddId::new(14), BddId::new(6)),    // 15
            BddNode::new(a, BddId::new(3), BddId::new(15)),    // 16
        ];
        assert_eq!(bdd.nodes.values(), expected);
        assert_eq!(id, BddId::new(16));

        // (a ∧ b) ∨ (¬a ∧ f) ∨ (b ∧ ¬f ∧ e)
        let mut map = bdd.replace_vars();
        map.insert("d", "e");
        map.insert("c", "f");
        let e = Var::from_usize(4);
        let f = Var::from_usize(5);
        let replaced = map.replace(id);
        expected.extend(&[
            BddNode::new(f, BddId::new(1), BddId::new(0)),   // 17
            BddNode::new(e, BddId::new(1), BddId::new(0)),   // 18
            BddNode::new(e, BddId::new(1), BddId::new(17)),  // 19
            BddNode::new(b, BddId::new(19), BddId::new(17)), // 20
            BddNode::new(a, BddId::new(3), BddId::new(20)),  // 21
        ]);
        assert_eq!(bdd.nodes.values(), expected);
        assert_eq!(replaced, BddId::new(21));
    }
}
