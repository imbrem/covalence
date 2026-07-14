//! **Kernel replay** — turning a checked arithmetic certificate into a real
//! `⊢ ⊥`, generic over the number representation *and* over how closed
//! comparisons are discharged.
//!
//! This is the counterpart to [`crate::farkas`]: that module decides whether a
//! certificate is arithmetically valid (pure data); this one re-derives the
//! refutation through the kernel. It is written against two
//! `covalence-hol-api` abstractions:
//!
//! - [`LinOrder`] — the ordered carrier (native eval `int`, a `succ`-tower
//!   `nat`, an object-level order in internal PA/SOA);
//! - [`Discharger`] — how a *closed* literal comparison (`5 ≤ 2`) is proved:
//!   by computation (eval TCB) or by pure induction (eval-TCB-free).
//!
//! So the same replay runs in the trusted eval kernel and in a from-scratch
//! `succ` representation with **no eval-TCB dependency** — you swap the
//! discharger.
//!
//! ## What is wired
//!
//! [`refute_chain`]: a chain of asserted ordering literals
//! `t₀ ⋈₀ t₁, …, tₙ₋₁ ⋈ₙ₋₁ tₙ` (each `⋈ ∈ {<, ≤}`) folded through the
//! mixed-transitivity lemmas into `⊢ t₀ ⋈ tₙ`, then **closed** two ways:
//!
//! - **cycle** (`tₙ = t₀`, at least one strict edge): `⊢ t₀ < t₀`, refuted by
//!   `lt_irrefl` — representation-independent, no discharger call.
//! - **literal bound** (`tₙ ≠ t₀`, both literals, relation false): e.g.
//!   `⊢ 5 ≤ 2`, refuted by the [`Discharger`] — this is where the eval-vs-`succ`
//!   choice bites.
//!
//! The general **scale-and-sum** Farkas refutation (non-unit coefficients) still
//! needs a linear ring normaliser — see `SKELETONS.md`. [`crate::farkas`]
//! already validates those certificates as data.

use covalence_hol_api::{Discharger, Hol, LinOrder, Strict};

/// Why a chain refutation could not be built.
#[derive(Debug, thiserror::Error)]
pub enum ReplayError {
    /// The edges are not a connected chain, or the closing is not a refutation.
    #[error("refute_chain: {0}")]
    Chain(String),
    /// A kernel inference rejected a step (a replay bug, not unsoundness).
    #[error(transparent)]
    Kernel(#[from] covalence_core::Error),
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
fn compose<L: LinOrder>(
    l: &L,
    a: &L::Term,
    b: &L::Term,
    c: &L::Term,
    left: &L::Thm,
    ls: Strict,
    right: &L::Thm,
    rs: Strict,
) -> Result<(L::Thm, Strict), ReplayError> {
    let lemma = match (ls, rs) {
        (Strict::Lt, Strict::Lt) => l.lt_trans()?,
        (Strict::Le, Strict::Lt) => l.lt_of_le_of_lt()?,
        (Strict::Lt, Strict::Le) => l.lt_of_lt_of_le()?,
        (Strict::Le, Strict::Le) => l.le_trans()?,
    };
    // lemma : ∀a b c. a ⋈₁ b ⟹ b ⋈₂ c ⟹ a ⋈₃ c
    let inst = l.all_elim(lemma, a.clone())?;
    let inst = l.all_elim(inst, b.clone())?;
    let inst = l.all_elim(inst, c.clone())?;
    let step = l.imp_elim(inst, left.clone())?;
    let step = l.imp_elim(step, right.clone())?;
    Ok((step, ls.join(rs)))
}

/// Replay an ordering chain into `⊢ ⊥`, generic over the carrier `L` and the
/// closed-comparison discharger `D`.
///
/// `edges` chain endpoint-to-endpoint (`edge[i].rhs == edge[i+1].lhs`). The fold
/// yields `⊢ t₀ ⋈ tₙ`; then either the cycle closes (`tₙ = t₀`, strict →
/// `absurd_lt`) or the terminal `t₀ ⋈ tₙ` is a false literal comparison closed
/// by `d`. Errors if the edges don't connect or the closing isn't a refutation.
pub fn refute_chain<L: LinOrder, D: Discharger<L>>(
    l: &L,
    d: &D,
    edges: &[Edge<L>],
) -> Result<L::Thm, ReplayError>
where
    L::Term: PartialEq,
{
    let err = |m: &str| ReplayError::Chain(m.to_string());
    let first = edges.first().ok_or_else(|| err("empty chain"))?;

    let start = first.lhs.clone();
    let mut tip = first.rhs.clone();
    let mut acc = first.thm.clone();
    let mut acc_strict = first.strict;

    for edge in &edges[1..] {
        if edge.lhs != tip {
            return Err(err("edges are not a connected chain"));
        }
        let (next, strict) = compose(
            l,
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

    if tip == start {
        // A cycle: t₀ ⋈ t₀. Needs a strict edge to refute via lt_irrefl.
        if acc_strict != Strict::Lt {
            return Err(err(
                "cycle has no strict edge (consistent, not a refutation)",
            ));
        }
        Ok(l.absurd_lt(start, acc)?)
    } else {
        // A bound: t₀ ⋈ tₙ over distinct terms — the discharger refutes it if it
        // is a false closed literal comparison (and fails otherwise).
        Ok(d.close(l, start, tip, acc_strict, acc)?)
    }
}

/// Refute a cycle with no closed-comparison step, over any [`LinOrder`] (no
/// discharger needed — a cycle closes on `lt_irrefl`). Convenience wrapper.
pub fn refute_cycle<L: LinOrder>(l: &L, edges: &[Edge<L>]) -> Result<L::Thm, ReplayError>
where
    L::Term: PartialEq,
{
    refute_chain(l, &NoDischarge, edges)
}

/// A discharger that refuses every closed comparison — for cycles that must
/// close purely on `lt_irrefl`.
struct NoDischarge;
impl<L: LinOrder> Discharger<L> for NoDischarge {
    fn lit(&self, _l: &L, _n: i128) -> L::Term {
        unreachable!("NoDischarge builds no literals")
    }
    fn close(
        &self,
        _l: &L,
        _a: L::Term,
        _b: L::Term,
        _s: Strict,
        _acc: L::Thm,
    ) -> covalence_core::Result<L::Thm> {
        Err(covalence_core::Error::NotAnEquation) // "no closed-literal discharge"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_api::{EvalDischarger, Int, NativeHol};

    fn edge(
        l: &NativeHol,
        a: &<NativeHol as Hol>::Term,
        b: &<NativeHol as Hol>::Term,
        s: Strict,
    ) -> Edge<NativeHol> {
        let atom = match s {
            Strict::Lt => LinOrder::lt(l, a.clone(), b.clone()),
            Strict::Le => LinOrder::le(l, a.clone(), b.clone()),
        }
        .expect("build ordering atom");
        Edge::new(a.clone(), b.clone(), l.assume(atom).expect("assume"), s)
    }

    fn assert_is_falsity(l: &NativeHol, bot: <NativeHol as Hol>::Thm) {
        let q = l.var("q_goal", l.bool_ty());
        let anything = l.false_elim(bot, q.clone()).expect("⊥ proves anything");
        assert_eq!(l.concl(&anything), q, "the refutation is genuine falsity");
    }

    /// `x ≤ y ∧ y < z ∧ z ≤ x ⟹ ⊥` — a mixed `<`/`≤` cycle (closes on
    /// `lt_irrefl`, no discharger).
    #[test]
    fn mixed_le_lt_cycle() {
        let l = NativeHol;
        let ty = l.int_ty();
        let x = l.var("x", ty.clone());
        let y = l.var("y", ty.clone());
        let z = l.var("z", ty.clone());
        let edges = [
            edge(&l, &x, &y, Strict::Le),
            edge(&l, &y, &z, Strict::Lt),
            edge(&l, &z, &x, Strict::Le),
        ];
        let bot = refute_cycle(&l, &edges).expect("refutation");
        assert_eq!(l.hyps(&bot).len(), 3);
        assert_is_falsity(&l, bot);
    }

    /// `5 ≤ x ∧ x ≤ y ∧ y ≤ 2 ⟹ ⊥` — a bound chain closing on the false literal
    /// comparison `5 ≤ 2`, discharged by the eval computation cert.
    #[test]
    fn bound_chain_closes_on_literal() {
        let l = NativeHol;
        let ty = l.int_ty();
        let x = l.var("x", ty.clone());
        let y = l.var("y", ty.clone());
        let five = l.int_lit(5);
        let two = l.int_lit(2);
        let edges = [
            edge(&l, &five, &x, Strict::Le),
            edge(&l, &x, &y, Strict::Le),
            edge(&l, &y, &two, Strict::Le),
        ];
        let bot = refute_chain(&l, &EvalDischarger, &edges).expect("refutation");
        assert_is_falsity(&l, bot);
    }

    /// A satisfiable bound chain `2 ≤ x ∧ x ≤ 5` must NOT refute — the discharger
    /// fails on the true comparison `2 ≤ 5`.
    #[test]
    fn satisfiable_chain_does_not_refute() {
        let l = NativeHol;
        let ty = l.int_ty();
        let x = l.var("x", ty.clone());
        let edges = [
            edge(&l, &l.int_lit(2), &x, Strict::Le),
            edge(&l, &x, &l.int_lit(5), Strict::Le),
        ];
        assert!(refute_chain(&l, &EvalDischarger, &edges).is_err());
    }
}
