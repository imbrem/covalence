//! The **recursion theorem** for `nat`: `∃r. P_rec r` — a recursor
//! exists. Proving it discharges [`crate::init::nat::rec_holds`] (and
//! with it every `add`/`mul` fact, and the shallow Peano embedding).
//!
//! The construction is the standard graph route, at `α = nat` (which is
//! all `add`/`mul` need):
//!
//! 1. **Graph** `Graph z f n a` — the least relation closed under the
//!    recursion rules, encoded impredicatively as
//!    `∀G. (G 0 z ∧ ∀m b. G m b ⟹ G (S m) (f m b)) ⟹ G n a`. A plain
//!    term builder ([`graph`]); "unfolding" it is just manipulating the
//!    `∀G …` structure, no defined constant.
//! 2. **Existence** `∀n. ∃a. Graph z f n a` by induction
//!    ([`graph_base`] / [`graph_step`] are the base/step facts). ← here
//! 3. **Uniqueness** `∀n a b. Graph z f n a ∧ Graph z f n b ⟹ a = b`
//!    by induction (uses `succ_inj` / `zero_ne_succ`). *(next)*
//! 4. **Assemble** `r z f n ≜ ε a. Graph z f n a`, prove `P_rec r`,
//!    `∃`-introduce. *(next)*
//!
//! Steps 3–4 are not wired yet, so [`graph_total`] is unreachable from
//! non-test code — hence the module-level `dead_code` allow. It comes
//! off once the theorem lands in `rec_holds` (tracked in `SKELETONS.md`).
#![allow(dead_code)]

use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::ext::TermExt;
use crate::init::logic::{exists_elim, exists_intro};
use crate::init::nat::{succ, zero};

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

/// `nat → nat → bool` — the relation variable `G`.
fn g_ty() -> Type {
    Type::fun(nat(), Type::fun(nat(), Type::bool()))
}

fn var(name: &str) -> Term {
    Term::free(name, nat())
}

/// `h x y`.
fn app2(h: Term, x: Term, y: Term) -> Result<Term> {
    h.apply(x)?.apply(y)
}

// ============================================================================
// The graph predicate
// ============================================================================

/// `G 0 z ∧ (∀m b. G m b ⟹ G (S m) (f m b))` — `G` is closed under the
/// recursion rules for `z`, `f`.
fn closed(z: &Term, f: &Term, g: &Term) -> Result<Term> {
    let g0z = app2(g.clone(), zero(), z.clone())?;
    let m = var("m");
    let b = var("b");
    let gmb = app2(g.clone(), m.clone(), b.clone())?;
    let fmb = app2(f.clone(), m.clone(), b.clone())?;
    let g_succ = app2(g.clone(), succ(m.clone()), fmb)?;
    let step = gmb
        .imp(g_succ)?
        .forall("b", nat())?
        .forall("m", nat())?;
    g0z.and(step)
}

/// `Graph z f n a ≜ ∀G. closed(z,f,G) ⟹ G n a`.
fn graph(z: &Term, f: &Term, n: Term, a: Term) -> Result<Term> {
    let g = Term::free("G", g_ty());
    let gna = app2(g.clone(), n, a)?;
    closed(z, f, &g)?.imp(gna)?.forall("G", g_ty())
}

// ============================================================================
// Base / step of the existence induction
// ============================================================================

/// `⊢ Graph z f 0 z` — the graph relates `0` to `z`.
///
/// Fix `G`, assume it is closed; the first conjunct *is* `G 0 z`.
fn graph_base(z: &Term, f: &Term) -> Result<Thm> {
    let g = Term::free("G", g_ty());
    let cl = closed(z, f, &g)?;
    Thm::assume(cl.clone())?
        .and_elim_l()? // {closed G} ⊢ G 0 z
        .imp_intro(&cl)? //          ⊢ closed G ⟹ G 0 z
        .all_intro("G", g_ty()) //   ⊢ ∀G. closed G ⟹ G 0 z
}

/// `⊢ Graph z f n a ⟹ Graph z f (S n) (f n a)`, for free `n`, `a`.
///
/// Fix `G` and assume it closed: from `Graph z f n a` get `G n a`, and
/// from closure's step clause (at `m,b := n,a`) get `G n a ⟹ G (S n) (f n a)`.
fn graph_step(z: &Term, f: &Term, n: &Term, a: &Term) -> Result<Thm> {
    let g = Term::free("G", g_ty());
    let cl = closed(z, f, &g)?;
    let gh_term = graph(z, f, n.clone(), a.clone())?; // Graph z f n a
    let gh = Thm::assume(gh_term.clone())?; // {GH} ⊢ Graph z f n a
    let cl_thm = Thm::assume(cl.clone())?; // {CL} ⊢ closed G

    // {GH, CL} ⊢ G n a
    let g_n_a = gh.all_elim(g.clone())?.imp_elim(cl_thm.clone())?;
    // {CL} ⊢ G n a ⟹ G (S n) (f n a)
    let g_step = cl_thm
        .and_elim_r()?
        .all_elim(n.clone())?
        .all_elim(a.clone())?;
    // {GH, CL} ⊢ G (S n) (f n a)
    let g_succ = g_step.imp_elim(g_n_a)?;

    g_succ
        .imp_intro(&cl)? // {GH} ⊢ closed G ⟹ G (S n) (f n a)
        .all_intro("G", g_ty())? // {GH} ⊢ Graph z f (S n) (f n a)
        .imp_intro(&gh_term) //     ⊢ Graph z f n a ⟹ Graph z f (S n) (f n a)
}

// ============================================================================
// Existence: ∀n. ∃a. Graph z f n a, by induction
// ============================================================================

/// `⊢ f arg` from `⊢ body`, where `body` is `f arg` β-reduced (used to
/// re-wrap a fact into the "applied" form `nat_induct` / `exists_*` want).
fn beta_expand(f: &Term, arg: Term, body_proof: Thm) -> Result<Thm> {
    Thm::beta_conv(Term::app(f.clone(), arg))?
        .sym()?
        .eq_mp(body_proof)
}

/// `⊢ body[arg]` from `⊢ f arg` (β-reduce a conclusion that is a redex).
fn beta_reduce_thm(thm: Thm) -> Result<Thm> {
    Thm::beta_conv(thm.concl().clone())?.eq_mp(thm)
}

/// `λa. Graph z f n a` — the existential predicate at a fixed `n`.
fn ex_pred(z: &Term, f: &Term, n: &Term) -> Result<Term> {
    let body = graph(z, f, n.clone(), var("a"))?;
    Ok(Term::abs(nat(), subst::close(&body, "a")))
}

/// `λn. ∃a. Graph z f n a` — the induction motive.
fn motive(z: &Term, f: &Term) -> Result<Term> {
    let body = graph(z, f, var("n"), var("a"))?.exists("a", nat())?;
    Ok(Term::abs(nat(), subst::close(&body, "n")))
}

/// `⊢ ∀n. (λn. ∃a. Graph z f n a) n` — the graph is **total**: every `n`
/// is related to some `a`. (Conclusion is in `nat_induct`'s applied
/// form; β-reduce the body to read `∀n. ∃a. Graph z f n a`.)
pub(crate) fn graph_total(z: &Term, f: &Term) -> Result<Thm> {
    let mot = motive(z, f)?;

    // base: ⊢ motive 0  — witness a := z, via graph_base.
    let pred0 = ex_pred(z, f, &zero())?;
    let at_z = beta_expand(&pred0, z.clone(), graph_base(z, f)?)?; // ⊢ pred0 z
    let ex0 = exists_intro(pred0, z.clone(), at_z)?; // ⊢ ∃a. Graph z f 0 a
    let base = beta_expand(&mot, zero(), ex0)?; // ⊢ motive 0

    // step: ⊢ motive n ⟹ motive (S n).
    let n = var("n");
    let mot_n = Term::app(mot.clone(), n.clone());
    let exn = beta_reduce_thm(Thm::assume(mot_n.clone())?)?; // {motive n} ⊢ ∃a. Graph z f n a

    // ∀a. (pred_n a) ⟹ motive (S n): from Graph z f n a, witness f n a
    // for the successor existential.
    let pred_n = ex_pred(z, f, &n)?;
    let a = var("a");
    let pred_n_a = Term::app(pred_n.clone(), a.clone());
    let gna = beta_reduce_thm(Thm::assume(pred_n_a.clone())?)?; // {pred_n a} ⊢ Graph z f n a
    let g_succ = graph_step(z, f, &n, &a)?.imp_elim(gna)?; // ⊢ Graph z f (S n) (f n a)
    let pred_sn = ex_pred(z, f, &succ(n.clone()))?;
    let fna = app2(f.clone(), n.clone(), a.clone())?;
    let at_fna = beta_expand(&pred_sn, fna.clone(), g_succ)?; // ⊢ pred_sn (f n a)
    let ex_sn = exists_intro(pred_sn, fna, at_fna)?; // ⊢ ∃a. Graph z f (S n) a
    let mot_sn = Term::app(mot.clone(), succ(n.clone()));
    let step_lemma = beta_expand(&mot, succ(n.clone()), ex_sn)? // ⊢ motive (S n)
        .imp_intro(&pred_n_a)?
        .all_intro("a", nat())?; // ⊢ ∀a. pred_n a ⟹ motive (S n)

    let step = exists_elim(exn, mot_sn, step_lemma)? // {motive n} ⊢ motive (S n)
        .imp_intro(&mot_n)?; //                          ⊢ motive n ⟹ motive (S n)

    Thm::nat_induct(base, step)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zf() -> (Term, Term) {
        (Term::free("z", nat()), Term::free("f", f_ty()))
    }

    #[test]
    fn graph_base_relates_zero_to_z() {
        let (z, f) = zf();
        let thm = graph_base(&z, &f).unwrap();
        assert!(thm.hyps().is_empty());
        assert_eq!(thm.concl(), &graph(&z, &f, zero(), z.clone()).unwrap());
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
        let reduced = beta_reduce_thm(inst).unwrap();
        let expected = graph(&z, &f, k, var("a")).unwrap().exists("a", nat()).unwrap();
        assert_eq!(reduced.concl(), &expected);
    }
}
