//! **Kernel replay** — turning a checked Farkas certificate into a real
//! `⊢ ⊥`, generic over any [`Int`] backend.
//!
//! This is the counterpart to [`crate::farkas`]: that module decides whether a
//! certificate is arithmetically valid (pure data); this one re-derives the
//! refutation through the kernel. Because it is written against the `Int` trait,
//! the *same* replay drives native HOL, an alternative integer encoding, or a
//! future object-level `int` in internal PA / SOA.
//!
//! ## What is wired
//!
//! The **unit-coefficient cycle** case, now with `<`/`≤` **mixing**: a set of
//! asserted ordering literals `t₀ ⋈₀ t₁, t₁ ⋈₁ t₂, …, tₙ₋₁ ⋈ₙ₋₁ t₀`
//! (each `⋈ ∈ {<, ≤}`, at least one strict) that chain around a cycle. Folding
//! the mixed-transitivity lemmas (`lt_trans` / `lt_of_le_of_lt` /
//! `lt_of_lt_of_le` / `le_trans`) collapses the chain to `t₀ < t₀`, refuted by
//! `lt_irrefl`. This subsumes the strict-only transitivity cycle the
//! `covalence-alethe` bridge handles today and adds the non-strict/mixed case
//! (`la_generic` with `≤` literals) it reports `NotImplemented`.
//!
//! The general **scale-and-sum** Farkas refutation (non-unit rational
//! coefficients, non-cyclic combinations) additionally needs a linear ring
//! normaliser to prove the summed polynomial equals its constant — see
//! `SKELETONS.md`. The [`crate::farkas`] checker already validates those
//! certificates as data; only the kernel construction is staged.

use covalence_core::Result;
use covalence_hol_api::{Hol, Int};

/// Why a cycle refutation could not be built.
#[derive(Debug, thiserror::Error)]
pub enum ReplayError {
    /// The edges are not a closed chain, or none is strict.
    #[error("refute_cycle: {0}")]
    Cycle(String),
    /// A kernel inference rejected a step (a replay bug, not unsoundness).
    #[error(transparent)]
    Kernel(#[from] covalence_core::Error),
}

/// The strictness of an ordering edge.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Strict {
    /// `<`
    Lt,
    /// `≤`
    Le,
}

impl Strict {
    /// The strictness of a transitive composition: strict if either side is.
    fn join(self, other: Strict) -> Strict {
        if self == Strict::Lt || other == Strict::Lt {
            Strict::Lt
        } else {
            Strict::Le
        }
    }
}

/// One asserted ordering edge `lhs ⋈ rhs` with its proof `⊢ lhs ⋈ rhs`.
pub struct Edge<H: Hol> {
    pub lhs: H::Term,
    pub rhs: H::Term,
    pub thm: H::Thm,
    pub strict: Strict,
}

impl<H: Hol> Edge<H> {
    pub fn new(lhs: H::Term, rhs: H::Term, thm: H::Thm, strict: Strict) -> Self {
        Edge {
            lhs,
            rhs,
            thm,
            strict,
        }
    }
}

/// Compose two adjacent edges `a ⋈₁ b` and `b ⋈₂ c` into `a ⋈₃ c`, picking the
/// transitivity lemma by their strictness and instantiating it at `a, b, c`.
fn compose<H: Int>(
    h: &H,
    a: &H::Term,
    b: &H::Term,
    c: &H::Term,
    left: &H::Thm,
    ls: Strict,
    right: &H::Thm,
    rs: Strict,
) -> Result<(H::Thm, Strict)> {
    let lemma = match (ls, rs) {
        (Strict::Lt, Strict::Lt) => h.lt_trans()?,
        (Strict::Le, Strict::Lt) => h.lt_of_le_of_lt()?,
        (Strict::Lt, Strict::Le) => h.lt_of_lt_of_le()?,
        (Strict::Le, Strict::Le) => h.le_trans()?,
    };
    // lemma : ∀a b c. a ⋈₁ b ⟹ b ⋈₂ c ⟹ a ⋈₃ c
    let inst = h.all_elim(lemma, a.clone())?;
    let inst = h.all_elim(inst, b.clone())?;
    let inst = h.all_elim(inst, c.clone())?;
    let step = h.imp_elim(inst, left.clone())?;
    let step = h.imp_elim(step, right.clone())?;
    Ok((step, ls.join(rs)))
}

/// Refute a cycle of `<`/`≤` edges: from `t₀ ⋈₀ t₁, …, tₙ₋₁ ⋈ₙ₋₁ t₀` (adjacent
/// edges sharing endpoints, closing the loop, at least one strict) derive
/// `⊢ ⊥`, with the edge literals as hypotheses.
///
/// Errors if the edges do not form a closed chain or none is strict (then the
/// cycle is consistent — `t₀ ≤ … ≤ t₀` proves nothing).
pub fn refute_cycle<H: Int>(h: &H, edges: &[Edge<H>]) -> std::result::Result<H::Thm, ReplayError>
where
    H::Term: PartialEq,
{
    let err = |m: &str| ReplayError::Cycle(m.to_string());
    let first = edges.first().ok_or_else(|| err("empty cycle"))?;

    // Fold the chain, accumulating `⊢ t₀ ⋈ tip`.
    let start = first.lhs.clone();
    let mut tip = first.rhs.clone();
    let mut acc = first.thm.clone();
    let mut acc_strict = first.strict;

    for edge in &edges[1..] {
        if edge.lhs != tip {
            return Err(err("edges are not a connected chain"));
        }
        let (next, strict) = compose(
            h,
            &start,
            &tip,
            &edge.rhs,
            &acc,
            acc_strict,
            &edge.thm,
            edge.strict,
        )?;
        acc = next;
        acc_strict = strict;
        tip = edge.rhs.clone();
    }

    if tip != start {
        return Err(err("chain does not close the cycle"));
    }
    if acc_strict != Strict::Lt {
        return Err(err(
            "cycle has no strict edge (consistent, not a refutation)",
        ));
    }
    // acc : ⊢ t₀ < t₀
    Ok(h.absurd_lt(start, acc)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_api::NativeHol;

    /// Build the asserted-literal `Edge` `a ⋈ b` over `NativeHol`.
    fn edge(
        h: &NativeHol,
        a: &<NativeHol as Hol>::Term,
        b: &<NativeHol as Hol>::Term,
        s: Strict,
    ) -> Edge<NativeHol> {
        let atom = match s {
            Strict::Lt => h.lt(a.clone(), b.clone()),
            Strict::Le => h.le(a.clone(), b.clone()),
        }
        .expect("build ordering atom");
        Edge::new(a.clone(), b.clone(), h.assume(atom).expect("assume"), s)
    }

    /// A refutation `bot : ⊢ ⊥` genuinely proves falsity: `false_elim` closes an
    /// arbitrary goal from it.
    fn assert_is_falsity(h: &NativeHol, bot: <NativeHol as Hol>::Thm) {
        let q = h.var("q_goal", h.bool_ty());
        let anything = h.false_elim(bot, q.clone()).expect("⊥ proves anything");
        assert_eq!(h.concl(&anything), q, "the refutation is genuine falsity");
    }

    /// `x ≤ y ∧ y < z ∧ z ≤ x ⟹ ⊥` — a mixed `<`/`≤` cycle, the case the
    /// current strict-only bridge reports `NotImplemented`. End-to-end: build
    /// the literals, chain, and land a genuine kernel `⊢ ⊥`.
    #[test]
    fn mixed_le_lt_cycle() {
        let h = NativeHol;
        let ty = h.int_ty();
        let x = h.var("x", ty.clone());
        let y = h.var("y", ty.clone());
        let z = h.var("z", ty.clone());
        let edges = [
            edge(&h, &x, &y, Strict::Le),
            edge(&h, &y, &z, Strict::Lt),
            edge(&h, &z, &x, Strict::Le),
        ];
        let bot = refute_cycle(&h, &edges).expect("refutation");
        assert_eq!(
            h.hyps(&bot).len(),
            3,
            "hypotheses = the three asserted edges"
        );
        assert_is_falsity(&h, bot);
    }

    /// A strict-only cycle `a < b ∧ b < c ∧ c < a` still refutes (subsumes the
    /// old bridge behaviour).
    #[test]
    fn strict_cycle() {
        let h = NativeHol;
        let ty = h.int_ty();
        let a = h.var("a", ty.clone());
        let b = h.var("b", ty.clone());
        let c = h.var("c", ty.clone());
        let edges = [
            edge(&h, &a, &b, Strict::Lt),
            edge(&h, &b, &c, Strict::Lt),
            edge(&h, &c, &a, Strict::Lt),
        ];
        let bot = refute_cycle(&h, &edges).expect("refutation");
        assert_is_falsity(&h, bot);
    }

    /// An all-`≤` cycle is consistent — no strict edge, so no refutation.
    #[test]
    fn all_le_cycle_is_not_a_refutation() {
        let h = NativeHol;
        let ty = h.int_ty();
        let a = h.var("a", ty.clone());
        let b = h.var("b", ty.clone());
        let edges = [edge(&h, &a, &b, Strict::Le), edge(&h, &b, &a, Strict::Le)];
        assert!(refute_cycle(&h, &edges).is_err());
    }
}
