use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Debug, Display, Formatter},
};

use crate::{Bdd, BddId, BddManager, Var};

/// A wrapper for `BddManager`, which displays all nodes in the manager as a
/// table.
#[derive(Clone)]
pub struct DisplayTable<'mgr>(&'mgr BddManager);

/// A wrapper for `BddManager`, which displays a set of BDDs in the manager as a
/// GraphViz directed graph.
#[derive(Clone)]
pub struct DisplayDigraph<'mgr> {
    mgr: &'mgr BddManager,
    title: String,
    nodes: Option<BTreeSet<BddId>>,
}

impl BddManager {
    /// Displays all nodes in the manager as a table.
    pub fn table(&self) -> DisplayTable<'_> {
        DisplayTable(self)
    }

    /// Displays a set of BDDs in the manager as a GraphViz directed graph.
    pub fn digraph<'mgr, I: IntoIterator<Item = Bdd<'mgr>>>(
        &'mgr self,
        nodes: I,
    ) -> DisplayDigraph<'mgr> {
        let mut reachable = BTreeSet::new();
        for node in nodes {
            Bdd::assert_manager(self, &node.mgr);
            self.append_reachable(node.id, &mut reachable);
        }
        DisplayDigraph {
            mgr: self,
            title: "bdds".to_owned(),
            nodes: Some(reachable),
        }
    }

    /// Displays all BDDs in the manager as a GraphViz directed graph.
    pub fn digraph_all(&self) -> DisplayDigraph<'_> {
        DisplayDigraph {
            mgr: self,
            title: "bdd_manager".to_owned(),
            nodes: None,
        }
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
        DisplayDigraph {
            mgr: self.mgr,
            title: format!("bdd{}", self.id.0),
            nodes: Some(self.mgr.reachable(self.id)),
        }
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

/// Displays the BDD formatted as its Shannon expansion, with its ID.
impl Debug for Bdd<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        struct DebugDisplay<T>(T);
        impl<T: Display> Debug for DebugDisplay<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                Display::fmt(&self.0, f)
            }
        }
        f.debug_tuple("Bdd")
            .field(&self.id())
            .field(&DebugDisplay(self))
            .finish()
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

impl Display for DisplayDigraph<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(nodes) = &self.nodes {
            self.mgr
                .write_digraph(f, &self.title, &mut nodes.into_iter().copied())
        } else {
            self.mgr
                .write_digraph(f, &self.title, &mut self.mgr.nodes.iter_keys())
        }
    }
}
