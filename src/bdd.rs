use std::{cmp::Ordering, ops::Deref};

use hashbrown::{HashMap, HashSet};

use crate::index_map::{IndexKey, IndexMap};

// TODO:
// - Use BddManager::insert_node in Bdd::iter instead of BddManager::ite.

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

    /// Gets the BDD for constant false.
    #[inline]
    pub fn zero(&self) -> Bdd<'_> {
        self.wrap(BddId::ZERO)
    }

    /// Gets the BDD for constant true.
    #[inline]
    pub fn one(&self) -> Bdd<'_> {
        self.wrap(BddId::ONE)
    }

    /// Gets the BDD for a constant boolean.
    #[inline]
    pub fn bool(&self, b: bool) -> Bdd<'_> {
        self.wrap(BddId::from(b))
    }

    /// Gets the node for the BDD id.
    #[inline]
    pub(crate) fn get_node(&self, id: BddId) -> BddIte {
        debug_assert!(id.as_usize() < self.node_count(), "ID out of bounds");
        unsafe { self.nodes.get_cloned_unchecked(id) }
    }

    #[inline]
    pub unsafe fn get_unchecked(&self, id: BddId) -> Bdd<'_> {
        Bdd { id, mgr: self }
    }

    /// Gets or inserts the BDD for a variable.
    pub fn variable<S: Into<String>>(&self, ident: S) -> Bdd<'_> {
        let var = self.vars.insert(ident.into());
        self.wrap(self.insert_var_id(var))
    }

    fn insert_var_id(&self, var: Var) -> BddId {
        self.nodes.insert(BddIte::new(var, BddId::ONE, BddId::ZERO))
    }

    /// Computes an if-then-else expression.
    #[doc(alias = "mux")]
    pub(crate) fn ite(&self, e_if: BddId, e_then: BddId, e_else: BddId) -> BddId {
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

        let node = if node_if.is_var() && node_if.var < node_then.var.min(node_else.var) {
            // The variables are already ordered; no need to recurse
            BddIte::new(node_if.var, e_then, e_else)
        } else {
            // Cofactor each sub-function by the minimum variable
            let var = node_if.var.min(node_then.var.min(node_else.var));
            let (co1_if, co0_if) = node_if.cofactor(e_if, var);
            let (co1_then, co0_then) = node_then.cofactor(e_then, var);
            let (co1_else, co0_else) = node_else.cofactor(e_else, var);

            // Recurse on the cofactors until every variable has been expanded
            let co1 = self.ite(co1_if, co1_then, co1_else);
            let co0 = self.ite(co0_if, co0_then, co0_else);

            // Insert the resulting node
            if co1 == co0 {
                return co1;
            }
            BddIte::new(var, co1, co0)
        };
        self.nodes.insert(node)
    }

    /// Gets or inserts a node directly. It must already be reduced and ordered.
    pub(crate) fn insert_node(&self, var: Var, high: BddId, low: BddId) -> BddId {
        debug_assert!(
            (var.is_const() || var.as_usize() < self.variable_count())
                && high.as_usize() < self.node_count()
                && low.as_usize() < self.node_count(),
            "ID out of bounds",
        );
        debug_assert!(
            high != low
                && !var.is_const()
                && var < self.get_node(high).var
                && var < self.get_node(low).var,
            "node is not reduced and ordered: {:?}",
            BddIte { var, high, low },
        );
        self.nodes.insert(BddIte { var, high, low })
    }

    /// Creates a map, which can be used to replace variables in this BDD.
    pub fn replace_variables(&self) -> VarReplaceMap<'_> {
        VarReplaceMap {
            mgr: self,
            replace: HashMap::new(),
        }
    }

    /// Creates a BDD isomorphic to `id` with the variables replaced according
    /// to the mappings in `replace`.
    pub(crate) fn replace(&self, id: BddId, replace: &HashMap<Var, Var>) -> BddId {
        if id.is_const() {
            return id;
        }
        let node = self.get_node(id);
        let var = replace.get(&node.var).copied().unwrap_or(node.var);
        let var = self.insert_var_id(var);
        let high = self.replace(node.high, replace);
        let low = self.replace(node.low, replace);
        self.ite(var, high, low)
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
        assert!(id.as_usize() < self.node_count(), "ID out of bounds");
        self.append_post_order_(id, post_order, visited);
    }

    fn append_post_order_(
        &self,
        id: BddId,
        post_order: &mut Vec<BddId>,
        visited: &mut HashSet<BddId>,
    ) {
        if visited.insert(id) {
            let node = self.get_node(id);
            self.append_post_order_(node.high, post_order, visited);
            self.append_post_order_(node.low, post_order, visited);
            post_order.push(id);
        }
    }

    /// Returns the number of nodes in the manager.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the number of variables in the manager.
    pub fn variable_count(&self) -> usize {
        self.vars.len()
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

    /// Computes the number of propositions that would satisfy this BDD.
    pub fn cardinality(&self) -> usize {
        if self.mgr.variable_count() == 0 {
            return 0;
        }
        self.cardinality_(0)
    }

    fn cardinality_(&self, var_index: usize) -> usize {
        if self.id == BddId::ZERO {
            return 0;
        }
        if self.id == BddId::ONE {
            return 1 << (self.mgr.variable_count() - var_index);
        }
        let node = self.node();
        let var_diff = node.var.as_usize() - var_index;
        let var_index = var_index + var_diff + 1;
        let high = self.mgr.wrap(node.high).cardinality_(var_index);
        let low = self.mgr.wrap(node.low).cardinality_(var_index);
        (high + low) << var_diff
    }

    /// Limits the BDD to at most `count` elements.
    pub fn take(&self, count: usize) -> (Bdd<'mgr>, usize) {
        if self.mgr.variable_count() == 0 {
            return (self.mgr.zero(), 0);
        }
        let (id, count) = self.take_(count, 0);
        (self.mgr.wrap(id), count)
    }

    fn take_(&self, count: usize, var_index: usize) -> (BddId, usize) {
        if count == 0 || self.id == BddId::ZERO {
            return (BddId::ZERO, 0);
        }
        if self.id == BddId::ONE && var_index == self.mgr.variable_count() {
            return (BddId::ONE, 1);
        }
        let node = self.node();
        let var = Var::from_usize(var_index);
        let (high, low) = if node.var == var {
            (node.high, node.low)
        } else {
            debug_assert!(node.var > var, "unordered iteration");
            (self.id, self.id)
        };
        let (high, high_size) = self.mgr.wrap(high).take_(count, var_index + 1);
        let (low, low_size) = self.mgr.wrap(low).take_(count - high_size, var_index + 1);
        let id = if high == low {
            high
        } else {
            self.mgr.insert_node(var, high, low)
        };
        (id, high_size + low_size)
    }

    /// Iterates the propositions in this BDD.
    pub fn iter<F: FnMut(Bdd<'mgr>)>(&self, mut each: F) {
        if !self.mgr.vars.is_empty() {
            self.iter_(&mut each, 0, BddId::ONE);
        }
    }

    fn iter_<F: FnMut(Bdd<'mgr>)>(&self, each: &mut F, var_index: usize, acc: BddId) {
        if self.id == BddId::ZERO {
            return;
        }
        let mgr = self.mgr;
        if self.id == BddId::ONE && var_index >= self.mgr.vars.len() {
            debug_assert!(var_index == self.mgr.vars.len());
            each(mgr.wrap(acc));
            return;
        }
        debug_assert!(var_index < self.mgr.vars.len());
        let var = Var::from_usize(var_index);
        let node = self.node();
        let (high, low) = if node.var == var {
            (node.high, node.low)
        } else {
            debug_assert!(node.var > var, "unordered iteration");
            (self.id, self.id)
        };
        let var = mgr.insert_var_id(var);
        let acc_high = mgr.ite(var, acc, BddId::ZERO);
        let acc_low = mgr.ite(var, BddId::ZERO, acc);
        mgr.wrap(high).iter_(each, var_index + 1, acc_high);
        mgr.wrap(low).iter_(each, var_index + 1, acc_low);
    }

    #[inline]
    pub(crate) fn assert_manager(mgr1: &'mgr BddManager, mgr2: &'mgr BddManager) {
        #[inline(never)]
        fn manager_error() -> ! {
            panic!("mixed BDDs from different managers");
        }
        if mgr1 as *const BddManager != mgr2 as *const BddManager {
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

impl Deref for Bdd<'_> {
    type Target = BddId;

    fn deref(&self) -> &Self::Target {
        &self.id
    }
}

impl BddId {
    pub const ZERO: BddId = BddId(0);
    pub const ONE: BddId = BddId(1);

    /// Returns whether the BDD is either 0 or 1.
    #[inline]
    pub fn is_const(&self) -> bool {
        self.0 <= 1
    }

    #[inline]
    pub fn as_const(&self) -> Option<bool> {
        if self.is_const() {
            Some(self.is_one())
        } else {
            None
        }
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

impl From<bool> for BddId {
    fn from(b: bool) -> Self {
        if b {
            BddId::ONE
        } else {
            BddId::ZERO
        }
    }
}

impl Var {
    pub const ZERO: Var = Var(0);
    pub const ONE: Var = Var(1);

    pub fn is_const(&self) -> bool {
        self.0 <= 1
    }

    pub fn as_const(&self) -> Option<bool> {
        if self.is_const() {
            Some(self == &Var::ONE)
        } else {
            None
        }
    }
}

impl IndexKey for Var {
    fn from_usize(index: usize) -> Self {
        Var(index as u32 + 2)
    }

    fn as_usize(&self) -> usize {
        debug_assert!(!self.is_const(), "convert constant to variable index");
        self.0 as usize - 2
    }
}

impl From<bool> for Var {
    fn from(b: bool) -> Self {
        if b {
            Var::ONE
        } else {
            Var::ZERO
        }
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
    /// that `(var & co1) | (!var & co0)`.
    #[inline]
    fn cofactor(&self, self_id: BddId, var: Var) -> (BddId, BddId) {
        if self.var == var {
            (self.high, self.low)
        } else {
            (self_id, self_id)
        }
    }

    #[inline]
    pub(crate) fn as_var(&self) -> Var {
        debug_assert!(self.is_var(), "node is not a variable node");
        self.var
    }

    pub(crate) fn is_var(&self) -> bool {
        !self.var.is_const() && self.high == BddId::ONE && self.low == BddId::ZERO
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
        let a = mgr.variable("a");
        let b = mgr.variable("b");
        let c = mgr.variable("c");
        let d = mgr.variable("d");
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
        assert_eq!(bdd.cardinality(), 9);

        // (a & b) | (!a & f) | (b & !f & e)
        mgr.variable("e");
        mgr.variable("f");
        let mut map = mgr.replace_variables();
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

    #[test]
    fn iter_const_tail_regress() {
        let mgr = BddManager::new();
        let a = mgr.variable("a");
        let b = mgr.variable("b");
        let bdd = a;
        let mut elems = Vec::new();
        bdd.iter(|elem| elems.push(elem));
        assert_eq!(elems, [a & b, a & !b]);
        assert_eq!(bdd.cardinality(), 2);
    }

    #[test]
    fn take() {
        let mgr = BddManager::new();
        let a = mgr.variable("a");
        let b = mgr.variable("b");
        let c = mgr.variable("c");
        let d = mgr.variable("d");
        let bdd = (a & b & c & d)
            | (a & b & c & !d)
            | (a & !b & c & d)
            | (a & !b & !c & d)
            | (!a & b & c & d)
            | (!a & !b & !c & !d);
        let (limited, count) = bdd.take(3);
        let expected = (a & b & c & d) | (a & b & c & !d) | (a & !b & c & d);
        assert_eq!(limited, expected);
        assert_eq!(count, 3);
    }
}
