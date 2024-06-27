use std::cmp::Ordering;

use hashbrown::{HashMap, HashSet};

use crate::index_map::{IndexKey, IndexMap};

/// A manager of binary decision diagrams.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BddManager {
    pub(crate) nodes: IndexMap<BddId, BddIte>,
    pub(crate) vars: IndexMap<Var, String>,
}

/// A binary decision diagram (specifically, reduced ordered binary decision
/// diagram (ROBDD)).
#[derive(Clone, Copy)]
pub struct Bdd<'mgr> {
    pub(crate) id: BddId,
    pub(crate) mgr: &'mgr BddManager,
}

/// A binary decision diagram in a `BddManager`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BddId(pub(crate) u32);

/// A boolean variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(pub(crate) u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BddIte {
    pub var: Var,
    pub high: BddId,
    pub low: BddId,
}

/// A mapping for replacing variables in a BDD.
#[derive(Debug)]
pub struct VarReplaceMap<'bdd> {
    pub(crate) mgr: &'bdd BddManager,
    pub(crate) replace: HashMap<Var, Var>,
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
    pub(crate) fn get_node(&self, id: BddId) -> BddIte {
        self.nodes.get_cloned(id)
    }

    #[inline]
    pub unsafe fn get_unchecked(&self, id: BddId) -> Bdd<'_> {
        Bdd { id, mgr: self }
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
            mgr: self,
            replace: HashMap::new(),
        }
    }

    /// Creates a new BDD isomorphic to `id` with the variables replaced
    /// according to the mappings in `replace`.
    pub(crate) fn insert_replace(&self, id: BddId, replace: &HashMap<Var, Var>) -> BddId {
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

    #[inline]
    pub(crate) fn wrap(&self, id: BddId) -> Bdd<'_> {
        unsafe { self.get_unchecked(id) }
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

    #[inline]
    pub(crate) fn assert_manager(&self, other: &'mgr BddManager) {
        #[inline(never)]
        fn manager_error() -> ! {
            panic!("mixed BDDs from different managers");
        }
        if self.mgr as *const BddManager != other as *const BddManager {
            manager_error();
        }
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
        let original = self.mgr.vars.insert(original.into());
        let replacement = self.mgr.vars.insert(replacement.into());
        self.replace.insert(original, replacement);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_replace() {
        let mgr = BddManager::new();
        // Insert variables first to guarantee order.
        let a = mgr.insert_var("a");
        let b = mgr.insert_var("b");
        let c = mgr.insert_var("c");
        let d = mgr.insert_var("d");
        let bdd = (a & b) | (!a & c) | (b & !c & d);

        let a = Var::from_usize(0);
        let b = Var::from_usize(1);
        let c = Var::from_usize(2);
        let d = Var::from_usize(3);
        let mut expected = vec![
            BddIte::new(Var::ZERO, BddId::ZERO, BddId::ZERO), // 0
            BddIte::new(Var::ONE, BddId::ONE, BddId::ONE),    // 1
            BddIte::new(a, BddId::from_usize(1), BddId::from_usize(0)), // 2
            BddIte::new(b, BddId::from_usize(1), BddId::from_usize(0)), // 3
            BddIte::new(c, BddId::from_usize(1), BddId::from_usize(0)), // 4
            BddIte::new(d, BddId::from_usize(1), BddId::from_usize(0)), // 5
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(0)), // 6
            BddIte::new(a, BddId::from_usize(0), BddId::from_usize(1)), // 7
            BddIte::new(a, BddId::from_usize(0), BddId::from_usize(4)), // 8
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(4)), // 9
            BddIte::new(c, BddId::from_usize(0), BddId::from_usize(1)), // 10
            BddIte::new(b, BddId::from_usize(10), BddId::from_usize(0)), // 11
            BddIte::new(c, BddId::from_usize(0), BddId::from_usize(5)), // 12
            BddIte::new(b, BddId::from_usize(12), BddId::from_usize(0)), // 13
            BddIte::new(c, BddId::from_usize(1), BddId::from_usize(5)), // 14
            BddIte::new(b, BddId::from_usize(14), BddId::from_usize(4)), // 15
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(15)), // 16
        ];
        assert_eq!(mgr.nodes, *expected);
        assert_eq!(bdd.id(), BddId::from_usize(16));

        // (a & b) | (!a & f) | (b & !f & e)
        mgr.insert_var("e");
        mgr.insert_var("f");
        let mut map = mgr.replace_vars();
        map.insert("c", "f");
        map.insert("d", "e");
        let replaced = bdd.replace(&map);

        let e = Var::from_usize(4);
        let f = Var::from_usize(5);
        expected.extend(&[
            BddIte::new(e, BddId::from_usize(1), BddId::from_usize(0)), // 17
            BddIte::new(f, BddId::from_usize(1), BddId::from_usize(0)), // 18
            BddIte::new(e, BddId::from_usize(1), BddId::from_usize(18)), // 19
            BddIte::new(b, BddId::from_usize(19), BddId::from_usize(18)), // 20
            BddIte::new(a, BddId::from_usize(3), BddId::from_usize(20)), // 21
        ]);
        assert_eq!(mgr.nodes, *expected);
        assert_eq!(replaced.id(), BddId::from_usize(21));
    }
}
