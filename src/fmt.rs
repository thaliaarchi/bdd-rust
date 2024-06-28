use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Debug, Display, Formatter},
};

use crate::{Bdd, BddId, BddManager, Var};

/// A wrapper for `BddManager`, which displays all nodes in the manager as a
/// table.
#[derive(Clone)]
pub struct DisplayTable<'mgr>(&'mgr BddManager);

/// A wrapper for `BddManager`, which displays all BDDs in the manager as a
/// GraphViz directed graph.
#[derive(Clone)]
pub struct DisplayDigraphAll<'mgr>(&'mgr BddManager);

/// A wrapper for `Bdd`, which displays the BDD as a GraphViz directed graph.
#[derive(Clone)]
pub struct DisplayDigraph<'mgr>(Bdd<'mgr>);

impl BddManager {
    /// Displays all nodes in the manager as a table.
    pub fn table(&self) -> DisplayTable<'_> {
        DisplayTable(self)
    }

    /// Displays all BDDs in the manager as a GraphViz directed graph.
    pub fn digraph_all(&self) -> DisplayDigraphAll<'_> {
        DisplayDigraphAll(self)
    }

    fn get_var(&self, var: Var) -> &str {
        match var.0 {
            0 => "0",
            1 => "1",
            _ => self.vars.get_deref(var),
        }
    }

    fn reachable(&self, id: BddId) -> BTreeSet<BddId> {
        let mut reachable = BTreeSet::new();
        self.append_reachable(id, &mut reachable);
        reachable
    }

    fn append_reachable(&self, id: BddId, reachable: &mut BTreeSet<BddId>) {
        if reachable.insert(id) {
            let node = self.get_node(id);
            self.append_reachable(node.high, reachable);
            self.append_reachable(node.low, reachable);
        }
    }

    fn write_digraph(
        &self,
        f: &mut Formatter<'_>,
        title: &str,
        nodes: &mut dyn Iterator<Item = BddId>,
    ) -> fmt::Result {
        let mut ranks = BTreeMap::<Var, Vec<BddId>>::new();
        writeln!(f, "digraph {title} {{")?;
        for id in nodes {
            let node = self.get_node(id);
            if id.is_const() {
                writeln!(f, "    node{} [label={}, shape=square];", id.0, id.0)?;
            } else {
                writeln!(
                    f,
                    "    node{} [label={}, xlabel={}, shape=circle];",
                    id.0,
                    self.get_var(node.var),
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

impl<'mgr> Bdd<'mgr> {
    /// Displays the BDD as a GraphViz directed graph.
    pub fn digraph(&self) -> DisplayDigraph<'mgr> {
        DisplayDigraph(*self)
    }

    fn write_shannon(&self, f: &mut Formatter<'_>, root: bool) -> fmt::Result {
        let node = self.node();
        let var = self.mgr.get_var(node.var);
        let both = node.high != BddId::ZERO && node.low != BddId::ZERO;
        if both && !root {
            f.write_str("(")?;
        }
        if !node.high.is_const() {
            if both {
                f.write_str("(")?;
            }
            f.write_str(var)?;
            f.write_str(" & ")?;
            self.mgr.wrap(node.high).write_shannon(f, false)?;
            if both {
                f.write_str(")")?;
            }
        } else if node.high == BddId::ONE {
            f.write_str(var)?;
        }
        if both {
            f.write_str(" | ")?;
        }
        if !node.low.is_const() {
            if both {
                f.write_str("(")?;
            }
            f.write_str("!")?;
            f.write_str(var)?;
            f.write_str(" & ")?;
            self.mgr.wrap(node.low).write_shannon(f, false)?;
            if both {
                f.write_str(")")?;
            }
        } else if node.low == BddId::ONE {
            f.write_str("!")?;
            f.write_str(var)?;
        }
        if both && !root {
            f.write_str(")")?;
        }
        Ok(())
    }
}

/// Displays the BDD formatted as its Shannon expansion.
impl Display for Bdd<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.id().is_const() {
            return f.write_str(if self.id() == BddId::ONE { "1" } else { "0" });
        }
        self.write_shannon(f, true)
    }
}

impl Display for DisplayTable<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mgr = self.0;
        writeln!(f, "| Var | High | Low | Id |")?;
        writeln!(f, "| --- | ---- | --- | -- |")?;
        for (id, node) in mgr.nodes.iter_cloned() {
            writeln!(
                f,
                "| {} | {} | {} | {} |",
                mgr.get_var(node.var),
                node.high.0,
                node.low.0,
                id.0,
            )?;
        }
        Ok(())
    }
}

impl Display for DisplayDigraphAll<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0
            .write_digraph(f, "bdd_manager", &mut self.0.nodes.iter_keys())
    }
}

impl Display for DisplayDigraph<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let bdd = self.0;
        let reachable = bdd.mgr.reachable(bdd.id);
        bdd.mgr
            .write_digraph(f, &format!("bdd{}", bdd.id.0), &mut reachable.into_iter())
    }
}

impl Debug for Bdd<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Bdd").field(&self.id.0).finish()
    }
}
