//! Datafun's `fix` over join-semilattices: one combinator, two recursions.
//!
//! - **set-valued** — transitive closure (reachability), the powerset lattice
//!   the Datalog engine uses;
//! - **lattice-valued** — min-plus shortest paths, which plain Datalog needs
//!   aggregation for but a semilattice `fix` does directly.
//!
//! Run:  `cargo run -p covalence-acset --example lfp`

use std::collections::{BTreeMap, BTreeSet};

use covalence_acset::lattice::{JoinSemilattice, MinDist, lfp};

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

fn main() {
    println!("covalence-acset — `fix` over semilattices (the Datafun core)\n");

    // -- set-valued: transitive closure ------------------------------------
    section("set lattice: transitive closure of 0→1→2→3");
    let edges: BTreeSet<(u32, u32)> = [(0, 1), (1, 2), (2, 3)].into_iter().collect();
    let reach = lfp(|r: &BTreeSet<(u32, u32)>| {
        let mut out = edges.clone();
        for &(a, b) in r {
            for &(c, d) in &edges {
                if b == c {
                    out.insert((a, d));
                }
            }
        }
        out
    });
    println!("  {} edges ⇒ {} reachable pairs:", edges.len(), reach.len());
    for (a, b) in &reach {
        let tag = if edges.contains(&(*a, *b)) {
            ""
        } else {
            "  (transitive)"
        };
        println!("    {a} ⇝ {b}{tag}");
    }

    // -- lattice-valued: min-plus shortest paths ---------------------------
    section("min-plus lattice: shortest paths");
    // 0→1 (1), 1→2 (2), 0→2 (5): the cheapest 0→2 is 1+2 = 3, not the direct 5.
    let weighted = [(0u32, 1u32, 1u64), (1, 2, 2), (0, 2, 5)];
    let nodes = [0u32, 1, 2];
    let dist = lfp(|d: &BTreeMap<(u32, u32), MinDist>| {
        let mut out = d.clone();
        let relax = |k: (u32, u32), v: MinDist, out: &mut BTreeMap<(u32, u32), MinDist>| {
            let cur = out.get(&k).copied().unwrap_or(MinDist::INF);
            out.insert(k, cur.join(v));
        };
        for &(u, v, w) in &weighted {
            relax((u, v), MinDist::finite(w), &mut out);
        }
        for &i in &nodes {
            for &(k, j, w) in &weighted {
                if let Some(&dik) = d.get(&(i, k)) {
                    relax((i, j), dik + w, &mut out);
                }
            }
        }
        out
    });
    for &i in &nodes {
        for &j in &nodes {
            if let Some(MinDist(Some(w))) = dist.get(&(i, j)) {
                println!("    {i} → {j} : {w}");
            }
        }
    }
    println!("    (0 → 2 is 3 via 0→1→2, beating the direct edge of 5)");

    section("the point");
    println!("  one `lfp` combinator; the lattice chooses the recursion.");
    println!("  Datalog's `solve` is `lfp` over the powerset lattice — Datafun would");
    println!("  add a typed surface whose monotonicity guarantees this always converges.");
}
