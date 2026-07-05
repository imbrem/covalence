//! The **recursion theorem** for `nat`: `∃r. P_rec r` — a recursor
//! exists. Proving it discharges [`crate::init::nat::rec_holds`] (and
//! with it every `add`/`mul` fact, and the shallow Peano embedding).
//!
//! The construction is the standard graph route, at `α = nat`. It is now
//! **fully driven by the generic inductive engine**
//! ([`crate::init::inductive`]) at the `nat_sig` signature, with the
//! `NatTheory` adapter supplying induction + freeness. This module is
//! reduced to that adapter plus the assembly wiring — every proof step
//! below is `nat` *consuming* the engine, not a `nat`-specific derivation:
//!
//! 1. **Graph** — the term builders from [`crate::init::inductive::graph`].
//! 2. **Existence** `∀n. ∃a. Graph z f n a` —
//!    [`graph_total`](crate::init::inductive::existence::graph_total) over
//!    [`graph_intro`](crate::init::inductive::existence::graph_intro). ✓
//! 3. **Uniqueness** — per-constructor *inversion*
//!    [`graph_inv`](crate::init::inductive::uniqueness::graph_inv) (freeness
//!    `succ_inj` / `zero_ne_succ`) and *determinacy*
//!    [`graph_det`](crate::init::inductive::determinacy::graph_det). ✓
//! 4. **Assembly** — the recursor `λz f n. ε a. Graph z f n a`, its
//!    equations, and `∃r. P_rec r` from [`recursor::recursion_theorem`],
//!    given `natRec`'s `p_rec_pred`; `spec_ax` then transfers to `natRec`
//!    (`rec_holds_proof`). ✓
//!
//! What remains is one direction of *lifting*, not construction: deriving
//! a non-kernel `Inductive` impl (e.g. `nat`-from-`ind`, or `list`) to feed
//! the same engine. See `SKELETONS.md`.
//!
use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;

use crate::init::eq::beta_reduce;
use crate::init::ext::TermExt;
use crate::init::inductive::{Arg, Constructor, Inductive, InductiveSig, recursor};
use crate::init::logic::exists_elim;
use crate::init::nat::{nat_succ, succ, zero};

// Engine entry points used only by the `nat`-level validation tests below
// (production goes through `recursor::recursion_theorem`).
#[cfg(test)]
use crate::init::inductive::{determinacy, existence, graph as gb, uniqueness};

// ============================================================================
// Types / small builders
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

/// `nat → nat → nat` — the recursion step function `f`.
#[cfg(test)]
fn f_ty() -> Type {
    Type::fun(nat(), Type::fun(nat(), nat()))
}

#[cfg(test)]
fn var(name: &str) -> Term {
    Term::free(name, nat())
}

/// `h x y`.
#[cfg(test)]
fn app2(h: Term, x: Term, y: Term) -> Result<Term> {
    h.apply(x)?.apply(y)
}

// ============================================================================
// The graph predicate — built through the generic inductive engine
// ============================================================================

/// The `nat` signature: `zero` (nullary) and `succ` (one recursive
/// argument `m` with image `b`). This is what makes the engine's term
/// layer concrete; the proofs below specialise to it.
///
/// The generated closure and graph reproduce the hand-written
/// `G 0 z ∧ (∀m b. G m b ⟹ G (S m) (f m b))` / `∀G. closed ⟹ G n a`
/// exactly — the `nat` step terms are `[z, f]`, the recursor result type
/// is `nat`.
fn nat_sig() -> &'static InductiveSig {
    static SIG: std::sync::LazyLock<InductiveSig> = std::sync::LazyLock::new(|| InductiveSig {
        ty: Type::nat(),
        relation: "G",
        ctors: vec![
            Constructor::nullary(zero()),
            Constructor::new(
                nat_succ(),
                vec![Arg::Rec {
                    name: "m",
                    image: "b",
                }],
            ),
        ],
    });
    &SIG
}

/// `nat`'s [`Inductive`] adapter — the engine's view of `nat`, sourcing
/// **structural induction from the kernel primitive** [`Thm::nat_induct`].
///
/// This is the lifting seam in action: the recursion engine
/// ([`existence`], and later uniqueness / assembly) talks only to this
/// trait, so the day `nat` is rebuilt internally from `ind` (where
/// induction is a *derived* theorem), swapping this one impl re-targets the
/// whole engine — the proofs in [`existence`] are reused verbatim.
struct NatTheory;

impl Inductive for NatTheory {
    fn sig(&self) -> &InductiveSig {
        nat_sig()
    }

    fn induct(&self, _motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        // `cases = [⊢ motive 0, ⊢ motive m ⟹ motive (S m)]` (applied
        // form) — exactly `Thm::nat_induct`'s base / step.
        let [base, step]: [Thm; 2] = cases.try_into().map_err(|_| {
            covalence_core::Error::ConnectiveRule("nat induct: expected 2 cases".into())
        })?;
        Thm::nat_induct(base, step)
    }

    fn injective(&self, i: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        // Only `succ` (constructor 1) is injective-relevant; `succ_inj`
        // already has the shape `(S x = S y) ⟹ (x = y)`.
        match (i, xs, ys) {
            (1, [x], [y]) => Thm::succ_inj(x.clone(), y.clone()),
            _ => Err(covalence_core::Error::ConnectiveRule(format!(
                "nat injective: no injectivity for constructor {i}"
            ))),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        // `zero_ne_succ m : ⊢ ¬(0 = S m)`; bridge it to `(Cᵢ = Cⱼ) ⟹ F`
        // in whichever order is asked.
        match (i, j, xs, ys) {
            (0, 1, [], [m]) => {
                let eq = zero().equals(succ(m.clone()))?;
                Thm::zero_ne_succ(m.clone())?
                    .not_elim(Thm::assume(eq.clone())?)?
                    .imp_intro(&eq)
            }
            (1, 0, [m], []) => {
                let eq = succ(m.clone()).equals(zero())?;
                Thm::zero_ne_succ(m.clone())?
                    .not_elim(Thm::assume(eq.clone())?.sym()?)?
                    .imp_intro(&eq)
            }
            _ => Err(covalence_core::Error::ConnectiveRule(format!(
                "nat distinct: no rule for constructors {i}, {j}"
            ))),
        }
    }
}

/// `Graph z f n a ≜ ∀G. closed(z,f,G) ⟹ G n a`.
#[cfg(test)]
fn graph(z: &Term, f: &Term, n: Term, a: Term) -> Result<Term> {
    gb::graph(nat_sig(), &[z.clone(), f.clone()], &nat(), n, a)
}

/// The recursor step terms `[z, f]` for the `nat` signature.
#[cfg(test)]
fn steps(z: &Term, f: &Term) -> [Term; 2] {
    [z.clone(), f.clone()]
}

// ============================================================================
// Step of the existence induction — via the generic engine
// ============================================================================

/// `⊢ Graph z f n a ⟹ Graph z f (S n) (f n a)`, for free `n`, `a`.
/// Constructor-1 (`succ`) introduction from [`existence::graph_intro`],
/// with the canonical argument/image vars `m`/`b` instantiated to `n`/`a`.
#[cfg(test)]
fn graph_step(z: &Term, f: &Term, n: &Term, a: &Term) -> Result<Thm> {
    existence::graph_intro(nat_sig(), &steps(z, f), &nat(), 1)?
        .inst("m", n.clone())?
        .inst("b", a.clone())
}

// ============================================================================
// Existence: ∀n. ∃a. Graph z f n a, by induction
// ============================================================================

/// `⊢ ∀n. (λn. ∃a. Graph z f n a) n` — the graph is **total**: every `n`
/// is related to some `a`. The generic [`existence::graph_total`] at the
/// [`NatTheory`] adapter (its induction supplied by `Thm::nat_induct`).
/// (Conclusion is in `nat_induct`'s applied form; β-reduce the body to
/// read `∀n. ∃a. Graph z f n a`.)
#[cfg(test)]
pub(crate) fn graph_total(z: &Term, f: &Term) -> Result<Thm> {
    existence::graph_total(&NatTheory, &steps(z, f), &nat())
}

// ============================================================================
// Uniqueness, part 1: inversion — now the generic engine's `graph_inv`
// ============================================================================

/// `⊢ Graph z f 0 a ⟹ a = z`, for free `a` — the graph forces the value
/// at `0` to be `z`. Constructor-0 inversion from
/// [`uniqueness::graph_inv`].
#[cfg(test)]
pub(crate) fn graph_base_inv(z: &Term, f: &Term) -> Result<Thm> {
    uniqueness::graph_inv(&NatTheory, &steps(z, f), &nat(), 0)
}

// ============================================================================
// Uniqueness, part 2: determinacy — now the generic engine's `graph_det`
// ============================================================================

/// `⊢ ∀n. (λn. ∀a b. Graph z f n a ⟹ Graph z f n b ⟹ a = b) n` — the
/// graph is **functional**: it relates each `n` to at most one value.
/// The generic [`determinacy::graph_det`] at the [`NatTheory`] adapter.
/// (β-reduce the body to read `∀n a b. … ⟹ a = b`.)
#[cfg(test)]
pub(crate) fn graph_det(z: &Term, f: &Term) -> Result<Thm> {
    determinacy::graph_det(&NatTheory, &steps(z, f), &nat())
}

// ============================================================================
// Assembly: the recursion theorem — now the generic engine's `recursor`
// ============================================================================

/// `β → (nat → β → β) → nat → β` — the recursor's type at result type `β`.
fn rec_ty_at(beta: &Type) -> Type {
    let step = Type::fun(nat(), Type::fun(beta.clone(), beta.clone()));
    Type::fun(
        beta.clone(),
        Type::fun(step, Type::fun(nat(), beta.clone())),
    )
}

/// `natRec`'s recursion predicate `P_rec`, instantiated at result type
/// `β` — the exact predicate `spec_ax(natRec, ·)` works with, and the
/// predicate the engine's [`recursor::recursion_theorem`] ∃-introduces
/// over.
fn p_rec_pred_at(beta: &Type) -> Result<Term> {
    let poly = defs::nat_rec_spec()
        .tm()
        .expect("natRec carries a selector predicate")
        .clone();
    Ok(subst::subst_tfree_in_term(&poly, "a", beta))
}

/// `⊢ ∃r. P_rec r` — **the recursion theorem** for `nat` at result type
/// `β`. The generic [`recursor::recursion_theorem`] at [`NatTheory`], with
/// step variables `z : β`, `f : nat → β → β` and `natRec`'s
/// [`p_rec_pred_at`]. The `NatTheory` adapter's induction / freeness are
/// about the *domain* `nat`, independent of `β`, so the same engine runs
/// at every result type.
fn recursion_theorem_at(beta: &Type) -> Result<Thm> {
    // The engine run is `β`-independent (the `NatTheory` induction/freeness are
    // about the domain `nat`), so build it ONCE at a polymorphic result type and
    // instantiate — the same caching trick as list's `foldr_holds`. Avoids
    // re-running the engine for every `β` `natRec` is used at (each `list`
    // index/head/tail lemma uses a different one).
    static CACHE: std::sync::LazyLock<Thm> = std::sync::LazyLock::new(|| {
        recursion_theorem_build(&Type::tfree("__natrec_b")).expect("nat recursion theorem")
    });
    CACHE.clone().inst_tfree("__natrec_b", beta.clone())
}

fn recursion_theorem_build(beta: &Type) -> Result<Thm> {
    let z = Term::free("z", beta.clone());
    let f = Term::free("f", Type::fun(nat(), Type::fun(beta.clone(), beta.clone())));
    recursor::recursion_theorem(&NatTheory, &[z, f], beta, &p_rec_pred_at(beta)?)
}

/// `⊢ ∀z f. (natRec z f 0 = z) ∧ (∀n. natRec z f (S n) = f n (natRec z f n))`
/// at result type `β` — the recursion equations for `natRec` at any result
/// type, **fully proved** (no hypotheses). The polymorphic core behind
/// [`rec_holds_proof`].
pub(crate) fn rec_holds_proof_at(beta: &Type) -> Result<Thm> {
    let pred = p_rec_pred_at(beta)?;
    let natrec = defs::nat_rec(beta.clone());
    let rec_ty = rec_ty_at(beta);
    let step =
        Thm::spec_ax(natrec.clone(), Term::free("r", rec_ty.clone()))?.all_intro("r", rec_ty)?; // ⊢ ∀r. P_rec r ⟹ P_rec natRec
    let p_nr = exists_elim(recursion_theorem_at(beta)?, Term::app(pred, natrec), step)?;
    beta_reduce(p_nr)
}

/// `⊢ ∃r. P_rec r` — **the recursion theorem** for `nat` at `β := nat`.
#[cfg(test)]
fn recursion_theorem() -> Result<Thm> {
    recursion_theorem_at(&nat())
}

/// `⊢ ∀z f. (natRec z f 0 = z) ∧ (∀n. natRec z f (S n) = f n (natRec z f n))`
/// — the recursion equations for `natRec`, **fully proved** (no
/// hypotheses). Discharges [`crate::init::nat::rec_holds`]: the
/// recursion theorem gives a recursor, and `spec_ax(natRec, ·)`
/// transfers its equations to `natRec` itself.
pub(crate) fn rec_holds_proof() -> Result<Thm> {
    rec_holds_proof_at(&nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zf() -> (Term, Term) {
        (Term::free("z", nat()), Term::free("f", f_ty()))
    }

    #[test]
    fn graph_step_extends_by_one() {
        let (z, f) = zf();
        let n = var("n");
        let a = var("a");
        let thm = graph_step(&z, &f, &n, &a).unwrap();
        assert!(thm.hyps().is_empty());

        let lhs = graph(&z, &f, n.clone(), a.clone()).unwrap();
        let fna = app2(f.clone(), n.clone(), a.clone()).unwrap();
        let rhs = graph(&z, &f, succ(n), fna).unwrap();
        assert_eq!(thm.concl(), &lhs.imp(rhs).unwrap());
    }

    #[test]
    fn graph_total_is_provable_and_axiom_free() {
        let (z, f) = zf();
        let thm = graph_total(&z, &f).unwrap();
        assert!(thm.hyps().is_empty(), "graph_total must be axiom-free");

        // Specialise at a concrete `k` and β-reduce the motive body:
        // ⊢ ∃a. Graph z f k a.
        let k = var("k");
        let inst = thm.all_elim(k.clone()).unwrap();
        let reduced = beta_reduce(inst).unwrap();
        let expected = graph(&z, &f, k, var("a"))
            .unwrap()
            .exists("a", nat())
            .unwrap();
        assert_eq!(reduced.concl(), &expected);
    }

    #[test]
    fn graph_base_inv_pins_value_to_z() {
        let (z, f) = zf();
        let thm = graph_base_inv(&z, &f).unwrap();
        assert!(thm.hyps().is_empty(), "base inversion must be axiom-free");
        let a = var("a");
        let expected = graph(&z, &f, zero(), a.clone())
            .unwrap()
            .imp(a.equals(z.clone()).unwrap())
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn graph_step_inv_exposes_predecessor() {
        // The recursive-constructor inversion `graph_inv(.., 1)`, with the
        // canonical argument var `m` instantiated to `n`.
        let (z, f) = zf();
        let thm = uniqueness::graph_inv(&NatTheory, &steps(&z, &f), &nat(), 1)
            .unwrap()
            .inst("m", var("n"))
            .unwrap();
        assert!(thm.hyps().is_empty(), "step inversion must be axiom-free");

        let n = var("n");
        let a = var("a");
        let d = var("d");
        let inner = graph(&z, &f, n.clone(), d.clone())
            .unwrap()
            .and(
                a.clone()
                    .equals(app2(f.clone(), n.clone(), d).unwrap())
                    .unwrap(),
            )
            .unwrap();
        let exists_c = inner.exists("d", nat()).unwrap();
        let expected = graph(&z, &f, succ(n.clone()), a.clone())
            .unwrap()
            .imp(exists_c)
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn determinacy_is_provable_and_axiom_free() {
        let (z, f) = zf();
        let thm = graph_det(&z, &f).unwrap();
        assert!(thm.hyps().is_empty(), "determinacy must be axiom-free");
        // Specialise at k and β-reduce: ∀a b. Graph k a ⟹ Graph k b ⟹ a = b.
        let k = var("k");
        let reduced = beta_reduce(thm.all_elim(k.clone()).unwrap()).unwrap();
        let a = var("a");
        let b = var("b");
        let expected = graph(&z, &f, k.clone(), a.clone())
            .unwrap()
            .imp(
                graph(&z, &f, k, b.clone())
                    .unwrap()
                    .imp(a.equals(b).unwrap())
                    .unwrap(),
            )
            .unwrap()
            .forall("b", nat())
            .unwrap()
            .forall("a", nat())
            .unwrap();
        assert_eq!(reduced.concl(), &expected);
    }

    #[test]
    fn recursion_theorem_is_axiom_free() {
        let rt = recursion_theorem().unwrap();
        assert!(rt.hyps().is_empty(), "∃r. P_rec r must be axiom-free");
        assert!(rt.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn rec_holds_is_fully_proved() {
        let thm = rec_holds_proof().unwrap();
        assert!(thm.hyps().is_empty(), "rec_holds is now a genuine theorem");
        // It proves exactly the statement init::nat::rec_holds asserts.
        assert_eq!(thm.concl(), crate::init::nat::rec_holds().concl());
    }
}
