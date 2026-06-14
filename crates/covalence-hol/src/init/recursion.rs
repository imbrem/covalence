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

use crate::init::ext::{TermExt, ThmExt};
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

// ============================================================================
// Uniqueness, part 1: inversion lemmas via "determinizing" instances
// ============================================================================

/// `⊢ redex`, given `⊢ (redex β-reduced)`. Bridges a fact about a
/// β-normal body back to the un-reduced application the graph carries.
///
/// **β only** (`beta_nf`, not `reduce`): the instances apply relations
/// to literals like `0`, and we must *not* let ι collapse the resulting
/// `0 = 0` to `T` — the proofs are stated with the equation intact.
fn prove_redex(redex: Term, reduced_proof: Thm) -> Result<Thm> {
    crate::init::eq::beta_nf(redex).sym()?.eq_mp(reduced_proof)
}

/// β-normalise a theorem's conclusion (β only — see [`prove_redex`]).
fn reduce_concl(thm: Thm) -> Result<Thm> {
    crate::init::eq::beta_nf(thm.concl().clone()).eq_mp(thm)
}

/// The determinizing relation `λk c. (k = 0) ⟹ (c = z)` — closed under
/// the recursion rules, and pins the value at `0` to `z`.
fn det_zero(z: &Term) -> Result<Term> {
    let k = var("k");
    let c = var("c");
    let body = k.equals(zero())?.imp(c.equals(z.clone())?)?;
    let lam_c = Term::abs(nat(), subst::close(&body, "c"));
    Ok(Term::abs(nat(), subst::close(&lam_c, "k")))
}

/// `⊢ closed(z, f, det_zero z)`.
fn det_zero_closed(z: &Term, f: &Term) -> Result<Thm> {
    let g = det_zero(z)?;
    // conj1: ⊢ G 0 z  (G 0 z β-reduces to (0=0) ⟹ (z=z)).
    let eq00 = zero().equals(zero())?;
    let g0z_body = Thm::refl(z.clone())?.imp_intro(&eq00)?; // ⊢ (0=0) ⟹ (z=z)
    let conj1 = prove_redex(app2(g.clone(), zero(), z.clone())?, g0z_body)?;

    // conj2: ⊢ ∀m b. G m b ⟹ G (S m) (f m b)  — the consequent is
    // vacuously true (S m ≠ 0), so it holds regardless of the antecedent.
    let m = var("m");
    let b = var("b");
    let sm = succ(m.clone());
    let fmb = app2(f.clone(), m.clone(), b.clone())?;
    let sm_eq_0 = sm.clone().equals(zero())?;
    // {S m = 0} ⊢ f m b = z, by ex falso (S m = 0 contradicts 0 ≠ S m).
    let contra = Thm::zero_ne_succ(m.clone())?
        .not_elim(Thm::assume(sm_eq_0.clone())?.sym()?)? // ⊢ F
        .false_elim(fmb.clone().equals(z.clone())?)?; //     ⊢ f m b = z
    let g_succ_body = contra.imp_intro(&sm_eq_0)?; // ⊢ (S m = 0) ⟹ (f m b = z)
    let g_succ = prove_redex(app2(g.clone(), sm, fmb)?, g_succ_body)?;
    let conj2 = g_succ
        .imp_intro(&app2(g.clone(), m.clone(), b.clone())?)?
        .all_intro("b", nat())?
        .all_intro("m", nat())?;

    conj1.and_intro(conj2)
}

/// `⊢ Graph z f 0 a ⟹ a = z`, for free `a` — the graph forces the
/// value at `0` to be `z`. Instantiate the graph's `∀G` at
/// [`det_zero`], discharge closure, and read off `a = z`.
pub(crate) fn graph_base_inv(z: &Term, f: &Term) -> Result<Thm> {
    let a = var("a");
    let g = det_zero(z)?;
    let gh = graph(z, f, zero(), a.clone())?;
    // {GH} ⊢ G 0 a, then β-reduce to (0=0) ⟹ (a=z), then MP refl.
    let g0a = Thm::assume(gh.clone())?
        .all_elim(g)?
        .imp_elim(det_zero_closed(z, f)?)?;
    reduce_concl(g0a)? // {GH} ⊢ (0=0) ⟹ (a=z)
        .imp_elim(Thm::refl(zero())?)? // {GH} ⊢ a = z
        .imp_intro(&gh) //                  ⊢ Graph z f 0 a ⟹ a = z
}

// ============================================================================
// Uniqueness, part 2: step inversion via the "Good" instance
// ============================================================================

/// `λd. Graph z f j d ∧ c = f j d` — the predicate of the existential
/// inside `wit`.
fn wit_pred(z: &Term, f: &Term, j: &Term, c: &Term) -> Result<Term> {
    let d = var("d");
    let body =
        graph(z, f, j.clone(), d.clone())?.and(c.clone().equals(app2(f.clone(), j.clone(), d)?)?)?;
    Ok(Term::abs(nat(), subst::close(&body, "d")))
}

/// `wit z f k c ≜ ∀j. (k = S j) ⟹ (∃d. Graph z f j d ∧ c = f j d)` —
/// "if `k` is a successor `S j`, then `c` is `f j` of *some* value the
/// graph relates to `j`".
fn wit(z: &Term, f: &Term, k: &Term, c: &Term) -> Result<Term> {
    let j = var("j");
    let d = var("d");
    let exists_d = graph(z, f, j.clone(), d.clone())?
        .and(c.clone().equals(app2(f.clone(), j.clone(), d)?)?)?
        .exists("d", nat())?;
    k.clone()
        .equals(succ(j.clone()))?
        .imp(exists_d)?
        .forall("j", nat())
}

/// `Good ≜ λk c. Graph z f k c ∧ wit z f k c` — a *closed* relation that
/// additionally records the predecessor structure, so `Good (S n) a`
/// exposes `a = f n c` for a graph-related `c`.
fn good(z: &Term, f: &Term) -> Result<Term> {
    let k = var("k");
    let c = var("c");
    let body = graph(z, f, k.clone(), c.clone())?.and(wit(z, f, &k, &c)?)?;
    let lam_c = Term::abs(nat(), subst::close(&body, "c"));
    Ok(Term::abs(nat(), subst::close(&lam_c, "k")))
}

/// `⊢ wit z f 0 z` — vacuous, since `0` is never `S j`.
fn wit_zero(z: &Term, f: &Term) -> Result<Thm> {
    let j = var("j");
    let zero_eq_sj = zero().equals(succ(j.clone()))?;
    let exists_d = graph(z, f, j.clone(), var("d"))?
        .and(z.clone().equals(app2(f.clone(), j.clone(), var("d"))?)?)?
        .exists("d", nat())?;
    Thm::zero_ne_succ(j.clone())?
        .not_elim(Thm::assume(zero_eq_sj.clone())?)? // ⊢ F
        .false_elim(exists_d)? //                       ⊢ ∃d. …
        .imp_intro(&zero_eq_sj)? //                     ⊢ (0 = S j) ⟹ ∃d. …
        .all_intro("j", nat())
}

/// `⊢ closed(z, f, Good)`.
fn good_closed(z: &Term, f: &Term) -> Result<Thm> {
    let g = good(z, f)?;

    // conj1: ⊢ Good 0 z  (β-reduces to Graph 0 z ∧ wit 0 z).
    let conj1 = {
        let reduced = graph_base(z, f)?.and_intro(wit_zero(z, f)?)?;
        prove_redex(app2(g.clone(), zero(), z.clone())?, reduced)?
    };

    // conj2: ⊢ ∀m b. Good m b ⟹ Good (S m) (f m b).
    let m = var("m");
    let b = var("b");
    let good_mb = app2(g.clone(), m.clone(), b.clone())?;
    let gm = reduce_concl(Thm::assume(good_mb.clone())?)?.and_elim_l()?; // {GA} ⊢ Graph m b

    // Graph (S m) (f m b)
    let g_succ = graph_step(z, f, &m, &b)?.imp_elim(gm.clone())?; // {GA} ⊢ Graph (S m) (f m b)

    // wit (S m) (f m b): for free j, given S m = S j, succ_inj gives m = j,
    // so witness d := b — Graph j b (rewrite Graph m b) and f m b = f j b.
    let j = var("j");
    let fmb = app2(f.clone(), m.clone(), b.clone())?;
    let smsj = succ(m.clone()).equals(succ(j.clone()))?;
    let mj = Thm::succ_inj(m.clone(), j.clone())?.imp_elim(Thm::assume(smsj.clone())?)?; // {SMSJ} ⊢ m = j
    let graph_jb = gm.rewrite(&mj)?; // {GA, SMSJ} ⊢ Graph j b
    let fmb_eq_fjb = fmb.clone().rw_all(&mj)?; // {SMSJ} ⊢ f m b = f j b
    let conj = graph_jb.and_intro(fmb_eq_fjb)?; // {GA, SMSJ} ⊢ Graph j b ∧ f m b = f j b
    let pred_d = wit_pred(z, f, &j, &fmb)?;
    let ex_d = exists_intro(pred_d.clone(), b.clone(), beta_expand(&pred_d, b.clone(), conj)?)?;
    let wit_succ = ex_d.imp_intro(&smsj)?.all_intro("j", nat())?; // {GA} ⊢ wit (S m) (f m b)

    let conj2 = {
        let reduced = g_succ.and_intro(wit_succ)?;
        prove_redex(app2(g.clone(), succ(m.clone()), fmb)?, reduced)?
    }
    .imp_intro(&good_mb)?
    .all_intro("b", nat())?
    .all_intro("m", nat())?;

    conj1.and_intro(conj2)
}

/// `⊢ Graph z f (S n) a ⟹ (∃c. Graph z f n c ∧ a = f n c)`, for free
/// `n`, `a` — the step-inversion lemma.
pub(crate) fn graph_step_inv(z: &Term, f: &Term) -> Result<Thm> {
    let n = var("n");
    let a = var("a");
    let gh = graph(z, f, succ(n.clone()), a.clone())?; // Graph (S n) a
    // {GH} ⊢ Good (S n) a, β-reduce, take the wit conjunct, specialise at n.
    let good_sn_a = Thm::assume(gh.clone())?
        .all_elim(good(z, f)?)?
        .imp_elim(good_closed(z, f)?)?;
    let ex_c = reduce_concl(good_sn_a)? // {GH} ⊢ Graph (S n) a ∧ wit (S n) a
        .and_elim_r()? //                  {GH} ⊢ ∀j. (S n = S j) ⟹ ∃d. …
        .all_elim(n.clone())? //           {GH} ⊢ (S n = S n) ⟹ ∃d. Graph n d ∧ a = f n d
        .imp_elim(Thm::refl(succ(n.clone()))?)?; // {GH} ⊢ ∃d. Graph n d ∧ a = f n d
    ex_c.imp_intro(&gh)
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
    fn good_closed_is_axiom_free() {
        let (z, f) = zf();
        assert!(good_closed(&z, &f).unwrap().hyps().is_empty());
    }

    #[test]
    fn graph_step_inv_exposes_predecessor() {
        let (z, f) = zf();
        let thm = graph_step_inv(&z, &f).unwrap();
        assert!(thm.hyps().is_empty(), "step inversion must be axiom-free");

        let n = var("n");
        let a = var("a");
        let d = var("d");
        let inner = graph(&z, &f, n.clone(), d.clone())
            .unwrap()
            .and(a.clone().equals(app2(f.clone(), n.clone(), d).unwrap()).unwrap())
            .unwrap();
        let exists_c = inner.exists("d", nat()).unwrap();
        let expected = graph(&z, &f, succ(n.clone()), a.clone())
            .unwrap()
            .imp(exists_c)
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }
}
