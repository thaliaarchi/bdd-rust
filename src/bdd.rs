use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::{self, Debug, Display, Formatter},
};

use crate::index_map::{IndexKey, IndexMap};

/// A manager of binary decision diagrams.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BddManager {
    nodes: IndexMap<BddId, BddIte>,
    vars: IndexMap<Var, String>,
}

/// A binary decision diagram (specifically, reduced ordered binary decision
/// diagram (ROBDD)).
#[derive(Clone, Copy)]
pub struct Bdd<'mgr> {
    id: BddId,
    mgr: &'mgr BddManager,
}

/// A binary decision diagram in a `BddManager`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BddId(u32);

/// A boolean variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BddIte {
    pub var: Var,
    pub high: BddId,
    pub low: BddId,
}

/// A mapping for replacing variables in a BDD.
#[derive(Debug)]
pub struct VarReplaceMap<'bdd> {
    bdd: &'bdd BddManager,
    replace: HashMap<Var, Var>,
}

impl BddManager {
    /// Constructs a new, empty `BddManager`.
    pub fn new() -> Self {
        let nodes = IndexMap::new();
        nodes.insert(BddIte::new(Var::ZERO, BddId::ZERO, BddId::ZERO));
        nodes.insert(BddIte::new(Var::ONE, BddId::ONE, BddId::ONE));
        BddManager {
            nodes,
            vars: IndexMap::new(),
        }
    }

    /// Gets the node for the BDD id.
    #[inline]
    fn get_node(&self, id: BddId) -> BddIte {
        self.nodes.get_cloned(id)
    }

    #[inline]
    pub unsafe fn get_unchecked(&self, id: BddId) -> Bdd<'_> {
        Bdd { id, mgr: self }
    }

    fn get_var(&self, var: Var) -> &str {
        match var.0 {
            0 => "0",
            1 => "1",
            _ => self.vars.get_deref(var),
        }
    }

    /// Gets or inserts the BDD for a variable.
    pub fn insert_var<S: Into<String>>(&self, ident: S) -> Bdd<'_> {
        let var = self.vars.insert(ident.into());
        self.wrap(self.insert_var_id(var))
    }

    fn insert_var_id(&self, var: Var) -> BddId {
        self.nodes.insert(BddIte::new(var, BddId::ONE, BddId::ZERO))
    }

    /// Gets or inserts the BDD for an if-then-else expression.
    pub fn insert_ite(&self, e_if: BddId, e_then: BddId, e_else: BddId) -> BddId {
        // Terminal cases
        if e_then.is_one() && e_else.is_zero() {
            return e_if;
        } else if e_if.is_one() || e_then == e_else {
            return e_then;
        } else if e_if.is_zero() {
            return e_else;
        }

        let node_if = self.get_node(e_if);
        let node_then = self.get_node(e_then);
        let node_else = self.get_node(e_else);

        // Cofactor each sub-function by the minimum variable
        let var = node_if.var.min(node_then.var).min(node_else.var);
        let (co1_if, co0_if) = node_if.cofactor(e_if, var);
        let (co1_then, co0_then) = node_then.cofactor(e_then, var);
        let (co1_else, co0_else) = node_else.cofactor(e_else, var);

        // Recurse on the cofactors until every variable has been expanded
        let co1 = self.insert_ite(co1_if, co1_then, co1_else);
        let co0 = self.insert_ite(co0_if, co0_then, co0_else);

        // Insert the resulting node
        if co1 == co0 {
            return co1;
        }
        self.nodes.insert(BddIte::new(var, co1, co0))
    }

    /// Creates a map, which can be used to replace variables in this BDD.
    pub fn replace_vars(&self) -> VarReplaceMap<'_> {
        VarReplaceMap {
            bdd: self,
            replace: HashMap::new(),
        }
    }

    /// Creates a new BDD from `id` with the variables replaced according to the
    /// mappings in `replace`.
    fn insert_replace(&self, id: BddId, replace: &HashMap<Var, Var>) -> BddId {
        if id.is_const() {
            return id;
        }
        let node = self.get_node(id);
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
            let node = self.get_node(id);
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
            let node = self.get_node(id);
            self.append_reachable(node.high, reachable);
            self.append_reachable(node.low, reachable);
        }
    }

    #[inline]
    pub(crate) fn wrap(&self, id: BddId) -> Bdd<'_> {
        unsafe { self.get_unchecked(id) }
    }
}

impl Display for BddManager {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "| Var | High | Low | Id |")?;
        writeln!(f, "| --- | ---- | --- | -- |")?;
        for (id, BddIte { var, high, low }) in self.nodes.iter_cloned() {
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

impl<'mgr> Bdd<'mgr> {
    /// Returns the ID for this BDD in the manager.
    pub fn id(&self) -> BddId {
        self.id
    }

    /// Returns the manager for this BDD.
    pub fn manager(&self) -> &'mgr BddManager {
        self.mgr
    }

    /// Returns the ITE node for this BDD.
    pub fn node(&self) -> BddIte {
        unsafe { self.mgr.nodes.get_cloned_unchecked(self.id) }
    }

    pub(crate) fn assert_manager(&self, other: Bdd<'mgr>) {
        assert_eq!(
            self.mgr as *const BddManager, other.mgr as *const BddManager,
            "combining BDDs from different managers",
        );
    }
}

impl Debug for Bdd<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.id, f)
    }
}

/// Displays the BDD as a GraphViz directed graph.
impl Display for Bdd<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let reachable = self.mgr.reachable(self.id);
        let mut ranks = BTreeMap::<Var, Vec<BddId>>::new();
        writeln!(f, "digraph bdd{} {{", self.id.0)?;
        for id in reachable {
            let node = self.mgr.get_node(id);
            if id.is_const() {
                writeln!(f, "    node{} [label={}, shape=square];", id.0, id.0)?;
            } else {
                writeln!(
                    f,
                    "    node{} [label={}, xlabel={}, shape=circle];",
                    id.0,
                    self.mgr.get_var(node.var),
                    id.0,
                )?;
                writeln!(f, "    node{} -> node{};", id.0, node.high.0)?;
                writeln!(f, "    node{} -> node{} [style=dashed];", id.0, node.low.0)?;
                ranks.entry(node.var).or_default().push(id);
            }
        }
        if !ranks.is_empty() {
            writeln!(f)?;
        }
        for (_, nodes) in ranks {
            write!(f, "    {{ rank=same; ")?;
            for id in nodes {
                write!(f, "node{}; ", id.0)?;
            }
            writeln!(f, "}}")?;
        }
        writeln!(f, "}}")
    }
}

impl PartialEq for Bdd<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.mgr as *const BddManager == other.mgr as *const BddManager
    }
}

impl Eq for Bdd<'_> {}

impl BddId {
    pub const ZERO: BddId = BddId(0);
    pub const ONE: BddId = BddId(1);

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

impl BddIte {
    #[inline]
    fn new(var: Var, high: BddId, low: BddId) -> Self {
        BddIte { var, high, low }
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

    /// Creates a new BDD identical to `id` with the variables replaced
    /// according to this mapping.
    pub fn replace(&self, id: BddId) -> BddId {
        self.bdd.insert_replace(id, &self.replace)
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
        let mgr = BddManager::new();
        let bdd = mgr.insert_exp(&f);
        let a = Var::from_usize(0);
        let b = Var::from_usize(1);
        let c = Var::from_usize(2);
        let d = Var::from_usize(3);
        let mut expected = vec![
            BddIte::new(Var::ZERO, BddId::ZERO, BddId::ZERO), // 0
            BddIte::new(Var::ONE, BddId::ONE, BddId::ONE),    // 1
            BddIte::new(a, BddId::from_usize(1), BddId::from_usize(0)), // 2
            BddIte::new(b, BddId::from_usize(1), BddId::from_usize(0)), // 3
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(0)), // 4
            BddIte::new(a, BddId::from_usize(0), BddId::from_usize(1)), // 5
            BddIte::new(c, BddId::from_usize(1), BddId::from_usize(0)), // 6
            BddIte::new(a, BddId::from_usize(0), BddId::from_usize(6)), // 7
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(6)), // 8
            BddIte::new(c, BddId::from_usize(0), BddId::from_usize(1)), // 9
            BddIte::new(b, BddId::from_usize(9), BddId::from_usize(0)), // 10
            BddIte::new(d, BddId::from_usize(1), BddId::from_usize(0)), // 11
            BddIte::new(c, BddId::from_usize(0), BddId::from_usize(11)), // 12
            BddIte::new(b, BddId::from_usize(12), BddId::from_usize(0)), // 13
            BddIte::new(c, BddId::from_usize(1), BddId::from_usize(11)), // 14
            BddIte::new(b, BddId::from_usize(14), BddId::from_usize(6)), // 15
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(15)), // 16
        ];
        assert_eq!(mgr.nodes, *expected);
        assert_eq!(bdd.id(), BddId::from_usize(16));

        // (a ∧ b) ∨ (¬a ∧ f) ∨ (b ∧ ¬f ∧ e)
        let mut map = mgr.replace_vars();
        map.insert("d", "e");
        map.insert("c", "f");
        let e = Var::from_usize(4);
        let f = Var::from_usize(5);
        let replaced = map.replace(bdd.id());
        expected.extend(&[
            BddIte::new(f, BddId::from_usize(1), BddId::from_usize(0)), // 17
            BddIte::new(e, BddId::from_usize(1), BddId::from_usize(0)), // 18
            BddIte::new(e, BddId::from_usize(1), BddId::from_usize(17)), // 19
            BddIte::new(b, BddId::from_usize(19), BddId::from_usize(17)), // 20
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(20)), // 21
        ]);
        assert_eq!(mgr.nodes, *expected);
        assert_eq!(replaced, BddId::from_usize(21));
    }
}
