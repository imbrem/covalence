//! Equality reasoning that the kernel rules don't already cover.
//!
//! The kernel's equality rules — [`Thm::refl`], [`Thm::sym`],
//! [`Thm::trans`], [`Thm::cong_app`], [`Thm::cong_abs`],
//! [`Thm::beta_conv`], [`Thm::eq_mp`] — **are the primitives**; call
//! them directly with `?`. The two congruence specialisations and the
//! whole-term rewriting conversion live as methods on
//! [`ThmExt`](crate::init::ext::ThmExt) /
//! [`TermExt`](crate::init::ext::TermExt)
//! ([`cong_fn`](crate::init::ext::ThmExt::cong_fn) /
//! [`cong_arg`](crate::init::ext::ThmExt::cong_arg) /
//! [`rw_all`](crate::init::ext::TermExt::rw_all) /
//! [`rewrite`](crate::init::ext::ThmExt::rewrite)). What remains here is
//! the multi-step [`trans_chain`] fold and the β-normaliser [`beta_nf`].
//!
//! HOL is folded into the kernel, so every equality is a single HOL
//! `=` ([`TermKind::Eq`](covalence_core::TermKind::Eq)) — there is no
//! `Trueprop` wrapper to unwrap.
//!
//! ## Reduction vocabulary — what reduces where
//!
//! The kernel has several *orthogonal* reduction relations. The
//! β-normaliser here does **β only**; nothing in this crate's
//! convenience layer unfolds definitions or computes on literals.
//! Reach for the right rule per kind:
//!
//! | Kind | What it rewrites | One step | Repeated (weak, no binders) |
//! |------|------------------|----------|------------------------------|
//! | **β** | `(λx. t) u → t[u/x]` | [`Thm::beta_conv`] | (via [`reduce`](crate::init::ext::TermExt::reduce)) |
//! | **δ** | defined constant → its body (`nat.add → λn m. …`) | [`Thm::unfold_term_spec`] / [`delta`](crate::init::ext::TermExt::delta) | [`delta_all`](crate::init::ext::TermExt::delta_all) (per symbol) |
//! | **prim / ι** | closed literal computation: `nat`/`int`/`bytes`/`bool` arithmetic, `succ`/`pred`, literal `=` | [`Thm::reduce_prim`] | [`reduce_consts`](crate::init::ext::TermExt::reduce_consts) |
//! | **βι** | β + ι together | — | [`reduce`](crate::init::ext::TermExt::reduce) |
//! | **η** | `(λx. f x) → f` | [`Thm::eta_conv`] | — |
//! | **spec coercion** | carrier ↔ wrapper for a derived type | [`Term::spec_abs`](covalence_core::Term::spec_abs) / [`spec_rep`](covalence_core::Term::spec_rep) | — |
//!
//! Two cross-cutting rules:
//!
//! - **The kinds are orthogonal.** β does no arithmetic
//!   (`(λx. x) (2 + 3)` β-reduces to `2 + 3`, not `5` — that is ι) and
//!   does not unfold `Spec` constants (that is δ). The combined
//!   [`reduce`](crate::init::ext::TermExt::reduce) does βι but still no
//!   δ; fold definitions in first with
//!   [`delta_all`](crate::init::ext::TermExt::delta_all).
//! - **Reduction is weak.** The repeated reducers stop at every `λ`;
//!   they never reduce under a binder. The lone exception is the strong
//!   normaliser [`beta_nf`] below, kept for the connective derivations.

use covalence_core::{Error, Result, Term, Thm};

use crate::init::ext::{TermExt, ThmExt};

/// Peel an application spine `f a₁ … aₙ` into `(f, [a₁, …, aₙ])`.
/// The head `f` is the left-most non-application; the args are in
/// left-to-right order.
pub fn spine(t: &Term) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut head = t;
    while let Some((f, a)) = head.as_app() {
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

/// `⊢ st = body a₁ … aₙ` — δ-unfold **only** the spine head of
/// `st = head a₁ … aₙ` (a defined-constant `Spec` leaf), leaving every
/// argument untouched. Unlike [`TermExt::delta_all`] — which unfolds
/// nested occurrences in the arguments too — this is the right tool when
/// the arguments must stay opaque (e.g. computing one membership /
/// element step over a *nested* expression). Errors if the head is not a
/// let-style unfoldable `Spec`.
pub fn delta_head(st: &Term) -> Result<Thm> {
    let (head, args) = spine(st);
    let mut acc = head.delta()?; // ⊢ head = body
    for arg in args {
        acc = acc.cong_fn(arg.clone())?; // append `arg` to both sides by congruence
    }
    Ok(acc)
}

/// Chain [`Thm::trans`] across a sequence of equational theorems:
/// `[A=B, B=C, C=D]` → `A=D`. Errors with [`Error::ConnectiveRule`] on
/// an empty sequence, and propagates any middle-term mismatch from
/// [`Thm::trans`].
pub fn trans_chain(steps: impl IntoIterator<Item = Thm>) -> Result<Thm> {
    let mut iter = steps.into_iter();
    let mut acc = iter
        .next()
        .ok_or_else(|| Error::ConnectiveRule("trans_chain: empty step sequence".into()))?;
    for next in iter {
        acc = acc.trans(next)?;
    }
    Ok(acc)
}

/// `⊢ t = nf`, where `nf` is the **β-normal form** of `t` — every
/// β-redex anywhere in `t` (in subterms and under binders) is fired,
/// repeatedly, until none remain. No hypotheses. Delegates to the
/// normalising conversion in [`crate::proofs::rewrite`].
///
/// Spec:
/// - Reduces **β and only β**. It fires a redex exactly when a subterm
///   has the syntactic shape `App(Abs(..), _)`. It never unfolds a
///   `Spec`/defined constant (δ), never runs [`Thm::reduce_prim`] (so
///   `nat`/`int`/`bytes`/`bool` arithmetic and literal `=` are **not**
///   evaluated), and never η-contracts. A `Spec` head applied to
///   arguments — e.g. `nat.add 1 1` — is therefore returned unchanged:
///   it is not a λ-redex.
/// - Result `nf` is the unique β-normal form (kernel terms are simply
///   typed, hence strongly normalising, so this always terminates).
/// - Works on open terms; free variables are inert leaves.
/// - The result equation carries an empty hypothesis set.
///
/// Unlike the rest of this module it currently **panics** on an
/// ill-typed `t` (the underlying conversion is infallible-or-bust);
/// that asymmetry will go away if the normaliser is rebuilt on the
/// `Result` rules.
pub fn beta_nf(t: Term) -> Thm {
    crate::proofs::rewrite::beta_nf(t)
}

// ============================================================================
// β-application plumbing — moving a fact between the *applied* form
// `pred arg` and its β-reduct `body`.
//
// `nat_induct`, `exists_intro` / `exists_elim`, and the recursor graph
// construction all phrase their inputs/outputs as a predicate *applied*
// to a point (`motive 0`, `pred witness`), while the surrounding proof
// works with the β-reduced body. These four helpers bridge the two
// directions, in both the **single-top-redex** flavour (`beta_conv`,
// when the head is a known λ) and the **strong-nf** flavour (`beta_nf`,
// for nested redexes — pure β, so literals / equations like `0 = 0` are
// *not* collapsed by ι).
// ============================================================================

/// `⊢ f arg` from `⊢ body`, where `body` is the single β-contraction of
/// the redex `f arg` (so `f` must be a λ). Re-wraps a fact about a
/// β-reduced body into the *applied* form `nat_induct` / `exists_*`
/// consume.
pub fn beta_expand(f: &Term, arg: Term, body: Thm) -> Result<Thm> {
    Thm::beta_conv(Term::app(f.clone(), arg))?
        .sym()?
        .eq_mp(body)
}

/// `⊢ body` from `⊢ f arg`, β-contracting the single top redex `f arg`
/// (the inverse of [`beta_expand`]).
pub fn beta_reduce(thm: Thm) -> Result<Thm> {
    Thm::beta_conv(thm.concl().clone())?.eq_mp(thm)
}

/// `⊢ t` from `⊢ nf`, where `nf` is the full **β-normal form** of `t` —
/// the strong-nf analogue of [`beta_expand`], for a redex `t` whose
/// contraction needs more than one step. Pure β (via [`beta_nf`]): any
/// literal equation in `t` is preserved, never ι-collapsed.
pub fn beta_nf_expand(t: Term, nf: Thm) -> Result<Thm> {
    beta_nf(t).sym()?.eq_mp(nf)
}

/// β-normalise a theorem's conclusion (pure β — see [`beta_nf_expand`]):
/// `Γ ⊢ φ` → `Γ ⊢ φ′` with `φ′` the β-normal form of `φ`. The strong-nf
/// analogue of [`beta_reduce`].
pub fn beta_nf_concl(thm: Thm) -> Result<Thm> {
    beta_nf(thm.concl().clone()).eq_mp(thm)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use covalence_core::Type;

    fn nat() -> Type {
        Type::nat()
    }

    fn nat_lit(n: u32) -> Term {
        Term::nat_lit(covalence_types::Nat::from_inner(n.into()))
    }

    #[test]
    fn beta_conv_fires_only_the_top_redex() {
        // (λx:nat. x) ((λy:nat. y) 7) --beta_conv--> (λy:nat. y) 7
        // i.e. one step, NOT recursing into the argument down to `7`.
        let id = Term::abs(nat(), Term::bound(0));
        let inner = id.clone().apply(nat_lit(7)).unwrap(); // (λy.y) 7
        let redex = id.apply(inner.clone()).unwrap();
        let (lhs, rhs) = Thm::beta_conv(redex.clone())
            .unwrap()
            .concl()
            .as_eq()
            .map(|(l, r)| (l.clone(), r.clone()))
            .unwrap();
        assert_eq!(lhs, redex);
        assert_eq!(rhs, inner, "beta_conv must leave the inner redex unfired");
    }

    #[test]
    fn beta_nf_does_not_unfold_specs_or_compute_literals() {
        // `nat.add 1 1` is a `Spec` head applied to literals — no
        // λ-redex anywhere — so β-normalisation returns it unchanged.
        // (NOT unfolded to its body, NOT evaluated to `2`.)
        let t = covalence_core::defs::nat_add()
            .apply(nat_lit(1))
            .unwrap()
            .apply(nat_lit(1))
            .unwrap();
        let (lhs, rhs) = beta_nf(t.clone()).concl().as_eq().unwrap().clone_pair();
        assert_eq!(lhs, t);
        assert_eq!(rhs, t, "beta_nf must not δ-unfold or compute literals");
    }

    #[test]
    fn beta_nf_reduces_a_real_redex_everywhere() {
        // (λx:nat. x) ((λx:nat. x) 5) --beta_nf--> 5, nested redex too.
        let id = Term::abs(nat(), Term::bound(0));
        let t = id.clone().apply(id.apply(nat_lit(5)).unwrap()).unwrap();
        let (_lhs, rhs) = beta_nf(t).concl().as_eq().unwrap().clone_pair();
        assert_eq!(rhs, nat_lit(5));
    }

    #[test]
    fn trans_chain_three_steps() {
        let a = Term::free("a", nat());
        let b = Term::free("b", nat());
        let c = Term::free("c", nat());
        let d = Term::free("d", nat());
        let ab = Thm::assume(a.clone().equals(b.clone()).unwrap()).unwrap();
        let bc = Thm::assume(b.equals(c.clone()).unwrap()).unwrap();
        let cd = Thm::assume(c.equals(d.clone()).unwrap()).unwrap();
        let ad = trans_chain([ab, bc, cd]).unwrap();
        let (lhs, rhs) = ad.concl().as_eq().unwrap();
        assert_eq!(lhs, &a);
        assert_eq!(rhs, &d);
    }

    #[test]
    fn trans_chain_rejects_empty() {
        assert!(trans_chain([]).is_err());
    }

    /// Tiny helper to own a borrowed `(&Term, &Term)` pair.
    trait ClonePair {
        fn clone_pair(self) -> (Term, Term);
    }
    impl ClonePair for (&Term, &Term) {
        fn clone_pair(self) -> (Term, Term) {
            (self.0.clone(), self.1.clone())
        }
    }
}
