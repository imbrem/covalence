//! The **recursion theorem** for `nat`: `∃r. P_rec r` — a recursor
//! exists. Proving it discharges [`crate::init::nat::rec_holds`] (and
//! with it every `add`/`mul` fact, and the shallow Peano embedding).
//!
//! The construction is the standard graph route, at `α = nat` (which is
//! all `add`/`mul` need). Increasingly it is driven by the generic
//! inductive engine ([`crate::init::inductive`]) at the [`nat_sig`]
//! signature, with the [`NatTheory`] adapter supplying induction from
//! `Thm::nat_induct` — this module keeps only the `nat`-specific glue and
//! the not-yet-generalised steps.
//!
//! 1. **Graph** `Graph z f n a` — the least relation closed under the
//!    recursion rules, encoded impredicatively as
//!    `∀G. (G 0 z ∧ ∀m b. G m b ⟹ G (S m) (f m b)) ⟹ G n a`. The term
//!    builders come from the engine ([`crate::init::inductive::graph`]);
//!    "unfolding" the graph is just manipulating the `∀G …` structure.
//! 2. **Existence** `∀n. ∃a. Graph z f n a` — now the engine's generic
//!    [`existence::graph_total`] over [`existence::graph_intro`];
//!    [`graph_base`] / [`graph_step`] are thin `nat` views of it. ✓
//! 3. **Uniqueness** — both halves now the engine's generic proofs over
//!    [`NatTheory`] (freeness `succ_inj` / `zero_ne_succ`): per-constructor
//!    *inversion* ([`uniqueness::graph_inv`], `graph_base_inv` its `nat`
//!    view) and *determinacy* `∀n a b. Graph z f n a ∧ Graph z f n b ⟹
//!    a = b` ([`determinacy::graph_det`]). ✓
//! 4. **Assemble** `r z f n ≜ ε a. Graph z f n a`, prove `P_rec r`,
//!    `∃`-introduce. The **last** `nat`-specific piece — it couples to
//!    `natRec`'s `defs` selector predicate; generalising it is the
//!    remaining engine work (see `SKELETONS.md`).
//!
use covalence_core::{Result, Term, Thm, Type, defs, subst};

use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::inductive::{
    Arg, Constructor, Inductive, InductiveSig, determinacy, existence, graph as gb, uniqueness,
};
use crate::init::logic::{exists_elim, exists_intro};
use crate::init::nat::{nat_succ, succ, zero};

// ============================================================================
// Types / small builders
// ============================================================================

fn nat() -> Type {
    Type::nat()
}

/// `nat → nat → nat` — the recursion step function `f`.
fn f_ty() -> Type {
    Type::fun(nat(), Type::fun(nat(), nat()))
}

fn var(name: &str) -> Term {
    Term::free(name, nat())
}

/// `h x y`.
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
fn graph(z: &Term, f: &Term, n: Term, a: Term) -> Result<Term> {
    gb::graph(nat_sig(), &[z.clone(), f.clone()], &nat(), n, a)
}

/// The recursor step terms `[z, f]` for the `nat` signature.
fn steps(z: &Term, f: &Term) -> [Term; 2] {
    [z.clone(), f.clone()]
}

// ============================================================================
// Step of the existence induction — via the generic engine
// ============================================================================

/// `⊢ Graph z f n a ⟹ Graph z f (S n) (f n a)`, for free `n`, `a`.
/// Constructor-1 (`succ`) introduction from [`existence::graph_intro`],
/// with the canonical argument/image vars `m`/`b` instantiated to `n`/`a`.
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
pub(crate) fn graph_total(z: &Term, f: &Term) -> Result<Thm> {
    existence::graph_total(&NatTheory, &steps(z, f), &nat())
}

// ============================================================================
// Uniqueness, part 1: inversion — now the generic engine's `graph_inv`
// ============================================================================

/// `⊢ Graph z f 0 a ⟹ a = z`, for free `a` — the graph forces the value
/// at `0` to be `z`. Constructor-0 inversion from
/// [`uniqueness::graph_inv`].
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
pub(crate) fn graph_det(z: &Term, f: &Term) -> Result<Thm> {
    determinacy::graph_det(&NatTheory, &steps(z, f), &nat())
}

// ============================================================================
// Assembly: the recursor via ε, its equations, and the recursion theorem
// ============================================================================

/// `nat → (nat → nat → nat) → nat → nat` — the recursor's type at `nat`.
fn rec_ty() -> Type {
    Type::fun(nat(), Type::fun(f_ty(), Type::fun(nat(), nat())))
}

/// `λa. Graph z f n a` — the predicate the recursor chooses from.
fn graph_pred(z: &Term, f: &Term, n: &Term) -> Result<Term> {
    Ok(Term::abs(
        nat(),
        subst::close(&graph(z, f, n.clone(), var("a"))?, "a"),
    ))
}

/// `ε a. Graph z f n a` — the chosen value at `n`.
fn rec_at(z: &Term, f: &Term, n: &Term) -> Result<Term> {
    Ok(Term::app(Term::select_op(nat()), graph_pred(z, f, n)?))
}

/// `⊢ Graph z f n (ε a. Graph z f n a)`, for free `n` — the chosen
/// value really is in the graph. From totality + Hilbert choice.
fn graph_at_rec(z: &Term, f: &Term) -> Result<Thm> {
    let n = var("n");
    let pred = graph_pred(z, f, &n)?;
    let exists_n = beta_reduce(graph_total(z, f)?.all_elim(n.clone())?)?;
    let choose = Thm::select_ax(pred.clone(), var("a"))?.all_intro("a", nat())?;
    let eps = Term::app(Term::select_op(nat()), pred.clone());
    beta_reduce(exists_elim(exists_n, Term::app(pred, eps), choose)?)
}

/// The closed recursor `λz f n. ε a. Graph z f n a`.
fn recursor() -> Result<Term> {
    let z = Term::free("z", nat());
    let f = Term::free("f", f_ty());
    let body = rec_at(&z, &f, &var("n"))?;
    let lam_n = Term::abs(nat(), subst::close(&body, "n"));
    let lam_f = Term::abs(f_ty(), subst::close(&lam_n, "f"));
    Ok(Term::abs(nat(), subst::close(&lam_f, "z")))
}

/// `r z f k`.
fn rzfk(r: &Term, z: &Term, f: &Term, k: Term) -> Result<Term> {
    r.clone().apply(z.clone())?.apply(f.clone())?.apply(k)
}

/// `natRec`'s recursion predicate `P_rec`, instantiated at `α := nat` —
/// the exact predicate `spec_ax(natRec, ·)` works with.
fn p_rec_pred() -> Result<Term> {
    let poly = defs::nat_rec_spec()
        .tm()
        .expect("natRec carries a selector predicate")
        .clone();
    Ok(subst::subst_tfree_in_term(&poly, "a", &nat()))
}

/// `⊢ ∃r. P_rec r` — **the recursion theorem** for `nat`. A recursor
/// exists. Built by assembling the graph: `r ≜ λz f n. ε a. Graph z f n a`
/// satisfies the recursion equations (base inversion at `0`, step +
/// determinacy at `S n`), so it witnesses the existential.
fn recursion_theorem() -> Result<Thm> {
    let r = recursor()?;
    let z = Term::free("z", nat());
    let f = Term::free("f", f_ty());
    let n = var("n");

    // eq1: ⊢ r z f 0 = z
    let eq1 = crate::init::eq::beta_nf(rzfk(&r, &z, &f, zero())?).trans(
        graph_base_inv(&z, &f)?
            .inst("a", rec_at(&z, &f, &zero())?)?
            .imp_elim(graph_at_rec(&z, &f)?.inst("n", zero())?)?,
    )?;

    // eq2: ⊢ ∀n. r z f (S n) = f n (r z f n)
    let rec_n = rec_at(&z, &f, &n)?;
    let g_at_n = graph_at_rec(&z, &f)?; // ⊢ Graph z f n rec_n
    let g_step = graph_step(&z, &f, &n, &rec_n)?.imp_elim(g_at_n)?; // ⊢ Graph z f (S n) (f n rec_n)
    let g_at_sn = graph_at_rec(&z, &f)?.inst("n", succ(n.clone()))?; // ⊢ Graph z f (S n) rec_{Sn}
    let fnrecn = app2(f.clone(), n.clone(), rec_n.clone())?;
    let det_eq = beta_reduce(graph_det(&z, &f)?.all_elim(succ(n.clone()))?)?
        .all_elim(rec_at(&z, &f, &succ(n.clone()))?)?
        .all_elim(fnrecn)?
        .imp_elim(g_at_sn)?
        .imp_elim(g_step)?; // ⊢ rec_{Sn} = f n rec_n
    let f_cong = crate::init::eq::beta_nf(rzfk(&r, &z, &f, n.clone())?)
        .sym()?
        .cong_arg(Term::app(f.clone(), n.clone()))?; // ⊢ f n rec_n = f n (r z f n)
    let eq2 = crate::init::eq::beta_nf(rzfk(&r, &z, &f, succ(n.clone()))?)
        .trans(det_eq)?
        .trans(f_cong)?
        .all_intro("n", nat())?;

    // P_rec body, generalised over z, f.
    let prec_body = eq1
        .and_intro(eq2)?
        .all_intro("f", f_ty())?
        .all_intro("z", nat())?;

    let pred = p_rec_pred()?;
    exists_intro(pred.clone(), r.clone(), beta_expand(&pred, r, prec_body)?)
}

/// `⊢ ∀z f. (natRec z f 0 = z) ∧ (∀n. natRec z f (S n) = f n (natRec z f n))`
/// — the recursion equations for `natRec`, **fully proved** (no
/// hypotheses). Discharges [`crate::init::nat::rec_holds`]: the
/// recursion theorem gives a recursor, and `spec_ax(natRec, ·)`
/// transfers its equations to `natRec` itself.
pub(crate) fn rec_holds_proof() -> Result<Thm> {
    let pred = p_rec_pred()?;
    let natrec = defs::nat_rec(nat());
    let step = Thm::spec_ax(natrec.clone(), Term::free("r", rec_ty()))?.all_intro("r", rec_ty())?; // ⊢ ∀r. P_rec r ⟹ P_rec natRec
    let p_nr = exists_elim(recursion_theorem()?, Term::app(pred, natrec), step)?;
    beta_reduce(p_nr)
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
