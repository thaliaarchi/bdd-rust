use std::mem;

use crate::{BddId, BddManager};

const UNIQUE_ALGS: [(
    &'static str,
    fn(mgr: &BddManager, values: &[BddId]) -> BddId,
); 10] = [
    ("unique_vars", BddManager::unique_vars),
    ("unique", BddManager::unique),
    ("unique_direct_ite", unique_direct_ite),
    ("unique_direct_ite2", unique_direct_ite2),
    ("unique_direct_ite3", unique_direct_ite3),
    ("unique_direct_or", unique_direct_or),
    ("unique_dynamic", unique_dynamic),
    ("unique_squared_pairs", unique_squared_pairs),
    ("unique_squared_grid", unique_squared_grid),
    ("unique_squared_grid2", unique_squared_grid2),
];

fn unique_direct_ite(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = BddId::ZERO;
    let mut none = BddId::ONE;
    for &v in values.iter().rev() {
        unique = mgr.ite(v, none, unique);
        none = mgr.ite(v, BddId::ZERO, none);
    }
    unique
}

fn unique_direct_ite2(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = BddId::ZERO;
    let mut none = BddId::ONE;
    for &v in values.iter().rev() {
        unique = mgr.ite(v, none, unique);
        none = mgr.and(mgr.not(v), none);
    }
    unique
}

fn unique_direct_ite3(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = BddId::ZERO;
    let mut none = BddId::ONE;
    for &v in values.iter().rev() {
        let not_v = mgr.not(v);
        unique = mgr.ite(v, none, unique);
        none = mgr.and(not_v, none);
    }
    unique
}

fn unique_direct_or(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = BddId::ZERO;
    let mut none = BddId::ONE;
    for &v in values.iter().rev() {
        let not_v = mgr.not(v);
        unique = mgr.or(mgr.and(v, none), mgr.and(not_v, unique));
        none = mgr.and(not_v, none);
    }
    unique
}

fn unique_dynamic(mgr: &BddManager, values: &[BddId]) -> BddId {
    // Construct the expression from the bottom up, grouping values in
    // increasing powers of 2 and reusing subexpressions (dynamic
    // programming).
    if values.is_empty() {
        return BddId::ZERO;
    }
    let mut values = values.iter().map(|&v| (mgr.not(v), v)).collect::<Vec<_>>();
    let mut values2 = Vec::with_capacity((values.len() + 1) / 2);
    while values.len() > 1 {
        let mut chunks = values.chunks_exact(2);
        values2.clear();
        values2.extend(chunks.by_ref().map(|chunk| {
            let [(l0, l1), (r0, r1)] = chunk.try_into().unwrap();
            (mgr.and(l0, r0), mgr.or(mgr.and(l0, r1), mgr.and(l1, r0)))
        }));
        values2.extend(chunks.remainder());
        mem::swap(&mut values, &mut values2);
    }
    values[0].1
}

fn unique_squared_pairs(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = mgr.zero();
    for &v in values {
        unique |= mgr.wrap(v);
    }
    for &v1 in values {
        for &v2 in values {
            if v1 != v2 {
                unique &= !mgr.wrap(v1) | !mgr.wrap(v2);
            }
        }
    }
    unique.id()
}

fn unique_squared_grid(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = mgr.zero();
    for &v1 in values {
        let mut only_v1 = mgr.one();
        for &v2 in values {
            let v = mgr.wrap(v2);
            only_v1 &= if v1 == v2 { v } else { !v };
        }
        unique |= only_v1;
    }
    unique.id()
}

fn unique_squared_grid2(mgr: &BddManager, values: &[BddId]) -> BddId {
    let mut unique = mgr.zero();
    for &v1 in values {
        let mut only_v1 = mgr.wrap(v1);
        for &v2 in values {
            if v2 != v1 {
                only_v1 &= !mgr.wrap(v2);
            }
        }
        unique |= only_v1;
    }
    unique.id()
}

fn insert_variables(mgr: &BddManager, n_vars: usize) -> Vec<BddId> {
    let mut values = Vec::with_capacity(n_vars);
    for var in 0..n_vars {
        values.push(mgr.variable(format!("v{var}")).id());
    }
    values
}

#[test]
fn unique_algs_node_count() {
    for n_vars in [0, 1, 5, 16] {
        let mut ids = Vec::with_capacity(UNIQUE_ALGS.len());
        for (name, unique_fn) in UNIQUE_ALGS {
            let mgr = BddManager::new();
            let id = unique_fn(&mgr, &insert_variables(&mgr, n_vars));
            ids.push((name, id));
        }
        let mut sorted = ids.clone();
        sorted.sort_by_key(|&(_, id)| id);
        assert_eq!(ids, sorted);
    }
}

#[test]
fn unique_algs_equivalence() {
    for n_vars in [0, 1, 5, 16] {
        let mgr = BddManager::new();
        let values = insert_variables(&mgr, n_vars);
        let id = (UNIQUE_ALGS[0].1)(&mgr, &values);
        assert!(
            n_vars != 0 && !id.is_const() || n_vars == 0 && id == BddId::ZERO,
            "unique computed an unexpected value with {n_vars} variables: {id:?}",
        );
        for (name, unique_fn) in &UNIQUE_ALGS[1..] {
            let id2 = unique_fn(&mgr, &values);
            assert_eq!(id, id2, "{name} differs with {n_vars} variables");
        }
    }
}
