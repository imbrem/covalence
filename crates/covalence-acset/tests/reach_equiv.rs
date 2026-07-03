//! Property test: on random graphs, the recursive Datalog transitive closure
//! (`Instance::solve`) agrees with the generic lattice fixpoint
//! (`lfp` over the powerset lattice). Deterministic LCG, no rng dep.

use std::collections::BTreeSet;

use covalence_acset::lattice::lfp;
use covalence_acset::{Instance, Part, Program, Rule, Schema};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn range(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn graph_schema() -> Schema {
    Schema::builder()
        .object("V")
        .object("E")
        .hom("src", "E", "V")
        .hom("dst", "E", "V")
        .build()
}

fn reachability() -> Program {
    Program::builder()
        .relation("edge", &["V", "V"])
        .relation("reach", &["V", "V"])
        .rule(
            Rule::builder()
                .var("e", "E")
                .var("a", "V")
                .var("b", "V")
                .head("edge", &["a", "b"])
                .hom("e", "src", "a")
                .hom("e", "dst", "b")
                .build(),
        )
        .rule(
            Rule::builder()
                .var("a", "V")
                .var("b", "V")
                .head("reach", &["a", "b"])
                .rel("edge", &["a", "b"])
                .build(),
        )
        .rule(
            Rule::builder()
                .var("a", "V")
                .var("b", "V")
                .var("c", "V")
                .head("reach", &["a", "c"])
                .rel("edge", &["a", "b"])
                .rel("reach", &["b", "c"])
                .build(),
        )
        .build()
}

/// Transitive closure of `edges` over `0..n` via the generic lattice fixpoint.
fn lfp_closure(edges: &BTreeSet<(usize, usize)>) -> BTreeSet<(usize, usize)> {
    lfp(|r: &BTreeSet<(usize, usize)>| {
        let mut out = edges.clone();
        for &(a, b) in r {
            for &(c, d) in edges {
                if b == c {
                    out.insert((a, d));
                }
            }
        }
        out
    })
}

#[test]
fn solve_equals_lfp_on_random_graphs() {
    let prog = reachability();
    let mut lcg = Lcg(0x9E37_79B9);
    for _ in 0..200 {
        let n = 1 + lcg.range(6); // 1..=6 vertices
        let m = lcg.range(n * n + 1); // 0..=n^2 edges
        let edges: BTreeSet<(usize, usize)> =
            (0..m).map(|_| (lcg.range(n), lcg.range(n))).collect();

        // Build the ACSet instance.
        let mut g = Instance::new(graph_schema());
        let vs: Vec<Part> = (0..n).map(|_| g.add_part("V")).collect();
        for &(a, b) in &edges {
            let e = g.add_part("E");
            g.set_hom(e, "src", vs[a]);
            g.set_hom(e, "dst", vs[b]);
        }

        // Datalog solve vs generic lfp closure.
        let sol = g.solve(&prog);
        let from_solve: BTreeSet<(usize, usize)> = sol
            .tuples("reach")
            .map(|t| (t[0].index, t[1].index))
            .collect();
        let from_lfp = lfp_closure(&edges);

        assert_eq!(from_solve, from_lfp, "mismatch on n={n}, edges={edges:?}");
    }
}
