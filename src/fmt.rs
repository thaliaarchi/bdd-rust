use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Debug, Display, Formatter},
};

use crate::{Bdd, BddId, BddIte, BddManager, Var};

impl BddManager {
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
