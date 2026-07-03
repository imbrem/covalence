//! Join-semilattices and a generic least-fixpoint combinator — Datafun's `fix`.
//!
//! The [`datalog`](crate::datalog) engine computes the least fixpoint of a
//! monotone map on the *powerset lattice* of tuples. This module exposes that
//! pattern directly: a [`JoinSemilattice`] (a bottom plus an idempotent,
//! commutative, associative `join`) and [`lfp`], which iterates a monotone step
//! from `⊥` to its least fixpoint (Kleene iteration). This is exactly the
//! semantics Datafun's `fix : (L →⁺ L) → L` denotes — here the monotonicity of
//! the step is the caller's obligation (Datafun's type system would discharge
//! it). See `notes/vibes/sketches/acset-datalog-datafun.md`.
//!
//! Because `lfp` is generic over the lattice, the same combinator gives both
//! relational closures (set-valued: reachability) and **lattice-valued**
//! recursion that plain Datalog needs aggregation for (e.g. min-plus shortest
//! paths via [`MinDist`]).

use std::collections::{BTreeMap, BTreeSet};

/// A bounded-below join-semilattice: a least element and an idempotent,
/// commutative, associative least-upper-bound.
pub trait JoinSemilattice: Clone + PartialEq {
    /// The least element `⊥`.
    fn bottom() -> Self;
    /// Least upper bound `self ⊔ other`.
    fn join(self, other: Self) -> Self;
}

/// Least fixpoint of `step` above `⊥`, by Kleene iteration.
///
/// Each round takes `x ↦ x ⊔ step(x)`, so the sequence is ascending regardless
/// of whether `step` is inflationary; for a **monotone** `step` on a lattice
/// satisfying the ascending-chain condition this converges to the least
/// fixpoint. The caller must ensure monotonicity and termination (finite-height
/// lattice, or a contracting metric like non-negative path lengths).
pub fn lfp<L: JoinSemilattice>(step: impl Fn(&L) -> L) -> L {
    let mut cur = L::bottom();
    loop {
        let next = cur.clone().join(step(&cur));
        if next == cur {
            return cur;
        }
        cur = next;
    }
}

impl JoinSemilattice for bool {
    fn bottom() -> Self {
        false
    }
    fn join(self, other: Self) -> Self {
        self || other
    }
}

impl<T: Ord + Clone> JoinSemilattice for BTreeSet<T> {
    fn bottom() -> Self {
        BTreeSet::new()
    }
    fn join(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<K: Ord + Clone, V: JoinSemilattice> JoinSemilattice for BTreeMap<K, V> {
    fn bottom() -> Self {
        BTreeMap::new()
    }
    fn join(mut self, other: Self) -> Self {
        for (k, v) in other {
            let merged = match self.remove(&k) {
                Some(existing) => existing.join(v),
                None => v,
            };
            self.insert(k, merged);
        }
        self
    }
}

/// A min-plus ("tropical") distance: `None` is `+∞` (the bottom), and `join` is
/// numeric **minimum** — so `lfp` over a map of these computes shortest paths.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct MinDist(pub Option<u64>);

impl MinDist {
    /// `+∞`.
    pub const INF: MinDist = MinDist(None);
    /// A finite distance.
    pub fn finite(d: u64) -> MinDist {
        MinDist(Some(d))
    }
    /// Add an edge weight (saturating; `+∞` stays `+∞`).
    pub fn add(self, w: u64) -> MinDist {
        MinDist(self.0.map(|d| d.saturating_add(w)))
    }
}

impl JoinSemilattice for MinDist {
    fn bottom() -> Self {
        MinDist::INF
    }
    fn join(self, other: Self) -> Self {
        MinDist(match (self.0, other.0) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.min(b)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bool_lfp() {
        // x = x ∨ true  ⇒  true
        assert!(lfp(|_: &bool| true));
        // x = x ∨ false ⇒  false (least fixpoint above ⊥)
        assert!(!lfp(|_: &bool| false));
    }

    #[test]
    fn set_transitive_closure() {
        // edges of the chain 0→1→2→3
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
        assert_eq!(reach.len(), 6); // all i<j in a 4-chain
        assert!(reach.contains(&(0, 3)));
        assert!(!reach.contains(&(3, 0)));
    }

    #[test]
    fn min_plus_shortest_paths() {
        // 0 ->1 (1), 1->2 (2), 0->2 (5): shortest 0→2 is 3, not the direct 5.
        let edges = [(0u32, 1u32, 1u64), (1, 2, 2), (0, 2, 5)];
        let nodes = [0u32, 1, 2];
        let dist = lfp(|d: &BTreeMap<(u32, u32), MinDist>| {
            let mut out = d.clone();
            // base: each edge relaxes its endpoints
            for &(u, v, w) in &edges {
                let e = MinDist::finite(w);
                let cur = out.get(&(u, v)).copied().unwrap_or(MinDist::INF);
                out.insert((u, v), cur.join(e));
            }
            // relax: dist(i,j) ⊔= dist(i,k) + edge(k,j)
            for &i in &nodes {
                for &(k, j, w) in &edges {
                    if let Some(&dik) = d.get(&(i, k)) {
                        let cand = dik.add(w);
                        let cur = out.get(&(i, j)).copied().unwrap_or(MinDist::INF);
                        out.insert((i, j), cur.join(cand));
                    }
                }
            }
            out
        });
        assert_eq!(dist.get(&(0, 2)), Some(&MinDist::finite(3)));
        assert_eq!(dist.get(&(0, 1)), Some(&MinDist::finite(1)));
    }
}
