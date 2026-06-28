//! # Projections `π₁`/`π₂` for the λ_iter Gödel pairing
//!
//! `code.pair a b = 2^a·(2b+1)`. The first projection `π₁` is the **2-adic
//! valuation** — defined by course-of-values recursion (`cv_exists`, choice-free,
//! per the CLAUDE.md proof convention), *not* an ε-selector:
//!
//! ```text
//!     π₁ n  =  if (n = 0) ∨ odd n  then 0  else S(π₁ (n/2))
//! ```
//!
//! (`odd n` tested as `n ≠ 2·(n/2)`). The recursion reads `π₁` only at `n/2 < n`
//! (`Hext`), so `cv_exists` hands back a fixpoint with this recurrence. The
//! second projection is the closed form `π₂ n = ((n / 2^(π₁ n)) − 1)/2`.
//!
//! Round-trip laws (the foundation-neutral export — see `init/SKELETONS.md`):
//! `π₁ (pair a b) = a`, `π₂ (pair a b) = b`, by induction on `a`.

use std::collections::BTreeMap;

use covalence_core::{Result, Term, Thm, Type, Var, defs, subst};
use smol_str::SmolStr;

use crate::init::code::{pair, pair_ne_zero, pair_succ_eq, pair_zero_eq, parity};
use crate::init::cond::{cond_false, cond_true};
use crate::init::cv_recursion::{cv_fixpoint, cv_witness};
use crate::init::eq::{beta_expand, beta_nf, beta_nf_concl, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::lambda_iter::{nat_lt_le_trans, nat_zero_or_succ};
use crate::init::logic::exists_elim;
use crate::init::nat;
use crate::init::nat_div::{
    bool_eqf, cond_cong_arm, div_mul_cancel, div_mul_le, nat_pos_of_ne_zero, or_false_l, or_true_r,
};
use crate::script::ConstDef;

// ============================================================================
// Term helpers
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}
/// `nat → nat` — the cv-recursion result type (`'a := nat`) and the history type.
fn nn() -> Type {
    Type::fun(nat_ty(), nat_ty())
}
fn lit(n: u64) -> Term {
    Term::nat_lit(n)
}
fn nvar(s: &str) -> Term {
    Term::free(s, nat_ty())
}
fn succ(n: Term) -> Term {
    Term::app(defs::nat_succ(), n)
}
fn mul(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_mul(), a), b)
}
fn add(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_add(), a), b)
}
fn div(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_div(), a), b)
}
fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_lt(), a), b)
}
/// `n / 2`.
fn half(n: &Term) -> Term {
    div(n.clone(), lit(2))
}

/// `cond` at result type `nat` (the kernel `bool.cond`, shared with `cond.cov`).
fn cond_op() -> Term {
    let cd = crate::init::cond::cov::env()
        .lookup_const("cond")
        .expect("cond.cov defines `cond`");
    let t = match cd {
        ConstDef::Poly(t) | ConstDef::Op(t) => t,
        ConstDef::Eq => panic!("`cond` is not Eq"),
    };
    subst::subst_tfrees_in_term(&t, &BTreeMap::from([(SmolStr::from("a"), nat_ty())]))
}
fn cond3(g: Term, t: Term, e: Term) -> Term {
    Term::app(Term::app(Term::app(cond_op(), g), t), e)
}

/// `(n = 0) ∨ ¬(n = 2·(n/2))` — the base-case guard (true at `0` and at odd `n`).
fn guard(n: &Term) -> Result<Term> {
    n.clone()
        .equals(lit(0))?
        .or(n.clone().equals(mul(lit(2), half(n)))?.not()?)
}

/// `F := λn g. cond (guard n) 0 (S (g (n/2)))` — the valuation step functional.
fn f_v2() -> Result<Term> {
    let (n, g) = (nvar("n"), Term::free("g", nn()));
    let rec = Term::app(g, half(&n)); // g (n/2)
    let body = cond3(guard(&n)?, lit(0), succ(rec));
    let lg = Term::abs(nn(), subst::close(&body, "g"));
    Ok(Term::abs(nat_ty(), subst::close(&lg, "n")))
}

// ============================================================================
// Decrease + Hext
// ============================================================================

/// `⊢ ∀n. (0 < n) ⟹ (n/2 < n)` — the recursion's decrease (`2 > 1`).
fn half_lt() -> Result<Thm> {
    let n = nvar("n");
    let q = half(&n);
    let goal = lt(q.clone(), n.clone());
    // (n/2)·2 ≤ n   (div.mul_le, no hypothesis)
    let mul_le = div_mul_le().all_elim(n.clone())?.all_elim(lit(2))?; // (n/2)·2 ≤ n
    let exq = nat_zero_or_succ().all_elim(q.clone())?; // q=0 ∨ ∃k. q=S k
    let exq_t = exq.concl().as_app().expect("∃").1.clone();
    // q = 0 : goal is `0 < n` (rewrite 0→q into the `0<n` hypothesis).
    let case_zero = {
        let hq = q.clone().equals(lit(0))?;
        Thm::assume(lt(lit(0), n.clone()))?
            .rewrite(&Thm::assume(hq.clone())?.sym()?)? // 0 → q : q < n
            .imp_intro(&hq)?
    };
    // q = S k : q < q·2 ≤ n.
    let case_succ = {
        let k = nvar("k");
        let pred = exq_t.as_app().expect("∃ pred").1.clone();
        let hk_redex = Term::app(pred, k.clone());
        let hk = beta_reduce(Thm::assume(hk_redex.clone())?)?; // q = S k
        let q_pos = nat::zero_lt_succ()
            .all_elim(k.clone())?
            .rewrite(&hk.clone().sym()?)?; // 0 < q
        let q2 = nat::mul_comm()
            .all_elim(q.clone())?
            .all_elim(lit(2))?
            .trans(two_double()?.all_elim(q.clone())?)?; // q·2 = 2·q = q + q
        let q_lt_q2 = nat::lt_add_pos()
            .all_elim(q.clone())?
            .all_elim(q.clone())?
            .imp_elim(q_pos)? // q < q + q
            .rewrite(&q2.clone().sym()?)?; // q < q·2
        nat_lt_le_trans()
            .all_elim(q.clone())?
            .all_elim(mul(q.clone(), lit(2)))?
            .all_elim(n.clone())?
            .imp_elim(q_lt_q2)?
            .imp_elim(mul_le.clone())? // q < n
            .imp_intro(&hk_redex)?
            .all_intro("k", nat_ty())?
    };
    let q_lt_n = exists_elim(Thm::assume(exq_t.clone())?, goal, case_succ)?.imp_intro(&exq_t)?;
    exq.or_elim(case_zero, q_lt_n)?
        .imp_intro(&lt(lit(0), n.clone()))?
        .all_intro("n", nat_ty())
}

/// `⊢ ∀x. 2·x = x + x` (re-derived locally; mirrors `code::two_double`).
fn two_double() -> Result<Thm> {
    let x = nvar("x");
    let two_s1 = succ(lit(1)).reduce()?.sym()?; // 2 = S 1
    let to_s1 = two_s1.cong_arg(defs::nat_mul())?.cong_fn(x.clone())?; // 2·x = (S 1)·x
    let ms = nat::mul_step().all_elim(lit(1))?.all_elim(x.clone())?; // (S 1)·x = x + 1·x
    let one_mul = nat::mul_comm()
        .all_elim(lit(1))?
        .all_elim(x.clone())?
        .trans(nat::mul_one().all_elim(x.clone())?)?; // 1·x = x
    to_s1.trans(ms)?.rewrite(&one_mul)?.all_intro("x", nat_ty())
}

/// `⊢ Hext F` — the below-`x` extensionality of the valuation step functional.
/// `F` reads its history only at `x/2 < x` (when the guard is false), so any two
/// histories agreeing below `x` give the same `F x`.
fn prove_hext_v2() -> Result<Thm> {
    let f = f_v2()?;
    let (x, p, q) = (nvar("x"), Term::free("p", nn()), Term::free("q", nn()));
    let agree_term = {
        let i = nvar("i");
        lt(i.clone(), x.clone())
            .imp(Term::app(p.clone(), i.clone()).equals(Term::app(q.clone(), i.clone()))?)?
            .forall("i", nat_ty())?
    };
    let h_agree = Thm::assume(agree_term.clone())?;
    // F x r β= cond (guard x) 0 (S (r (x/2))).
    let red = |r: &Term| -> Thm { beta_nf(Term::app(Term::app(f.clone(), x.clone()), r.clone())) };

    let g = guard(&x)?;
    let g_eq_f = g.clone().equals(Term::bool_lit(false))?;
    let h_g = Thm::assume(g_eq_f.clone())?; // guard = F
    // ¬(x = 0)  (else the left disjunct makes guard = T).
    let x_eq_0 = x.clone().equals(lit(0))?;
    let odd_t = x.clone().equals(mul(lit(2), half(&x)))?.not()?;
    let not_x0 = h_g
        .clone()
        .eq_mp(Thm::assume(x_eq_0.clone())?.or_intro_l(odd_t)?)? // {g=F, x=0} ⊢ F
        .imp_intro(&x_eq_0)?
        .not_intro()?; // {g=F} ⊢ ¬(x=0)
    let pos = nat_pos_of_ne_zero().all_elim(x.clone())?.imp_elim(not_x0)?; // 0 < x
    let sub_lt = half_lt()?.all_elim(x.clone())?.imp_elim(pos)?; // x/2 < x
    let arm_eq = h_agree
        .clone()
        .all_elim(half(&x))?
        .imp_elim(sub_lt)? // p(x/2) = q(x/2)
        .cong_arg(defs::nat_succ())? // S(p(x/2)) = S(q(x/2))
        .imp_intro(&g_eq_f)?; // {agree} ⊢ g=F ⟹ S..=S..
    let cong = cond_cong_arm()
        .inst_tfree("a", nat_ty())?
        .all_elim(g.clone())?
        .all_elim(lit(0))?
        .all_elim(succ(Term::app(p.clone(), half(&x))))?
        .all_elim(succ(Term::app(q.clone(), half(&x))))?
        .imp_elim(arm_eq)?; // cond g 0 (S(p(x/2))) = cond g 0 (S(q(x/2)))
    let feq = red(&p).trans(cong)?.trans(red(&q).sym()?)?; // F x p = F x q
    feq.imp_intro(&agree_term)?
        .all_intro("q", nn())?
        .all_intro("p", nn())?
        .all_intro("x", nat_ty())
}

/// The **explicit, choice-free** valuation function (`cv_witness` at the
/// valuation step functional — `natRec`/`cond`/`nat.div`/`succ`, no ε).
pub fn v2_explicit() -> Result<Term> {
    let w = subst::subst_tfrees_in_term(
        &cv_witness(),
        &BTreeMap::from([(SmolStr::from("a"), nat_ty())]),
    );
    let w = subst::subst_free(&w, &Var::new("F", f_v2()?.type_of()?), &f_v2()?);
    Ok(subst::subst_free(&w, &Var::new("d", nat_ty()), &lit(0)))
}

/// `⊢ ∀n. v2 n = cond ((n=0) ∨ ¬(n=2·(n/2))) 0 (S (v2 (n/2)))` — the valuation's
/// recurrence, read off [`cv_fixpoint`] (no ∃, no ε).
pub fn v2_recurrence() -> Result<Thm> {
    let n = nvar("n");
    let v2 = v2_explicit()?;
    let fixed = cv_fixpoint()?
        .inst_tfree("a", nat_ty())?
        .inst("F", f_v2()?)?
        .inst("d", lit(0))?
        .imp_elim(prove_hext_v2()?)?; // ∀n. v2 n = F n v2
    fixed
        .all_elim(n.clone())?
        .trans(beta_nf(Term::app(
            Term::app(f_v2()?, n.clone()),
            v2.clone(),
        )))? // v2 n = cond (guard n) 0 (S (v2 (n/2)))
        .all_intro("n", nat_ty())
}

// ============================================================================
// `π₁` round-trip:  `⊢ ∀a b. v2 (code.pair a b) = a`
// ============================================================================

/// Prove `⊢ ∀<ivar>. body` by `nat`-induction (local copy of `code::induct_on`,
/// which is private): `motive = λ<ivar>. body`, `base : ⊢ body[0]`,
/// `step : ⊢ body[n] ⟹ body[S n]` (`n` free).
fn induct_on(ivar: &str, motive: &Term, base: Thm, step: Thm) -> Result<Thm> {
    let n = nvar(ivar);
    let base = beta_expand(motive, lit(0), base)?; // ⊢ motive 0
    let pn = Term::app(motive.clone(), n.clone());
    let body_n = beta_reduce(Thm::assume(pn.clone())?)?; // {motive n} ⊢ body[n]
    let body_sn = step.imp_elim(body_n)?; //                 {motive n} ⊢ body[S n]
    let p_sn = beta_expand(motive, succ(n.clone()), body_sn)?; // {motive n} ⊢ motive (S n)
    let step = p_sn.imp_intro(&pn)?; //                        ⊢ motive n ⟹ motive (S n)
    beta_nf_concl(Thm::nat_induct(base, step)?)
}

/// The else-arm of a `Γ ⊢ lhs = cond g t e` conclusion (its RHS's last
/// argument), read off verbatim so [`cond_true`]/[`cond_false`] get a branch
/// term matching the recurrence's β-normal form exactly.
fn cond_else(thm: &Thm) -> Result<Term> {
    let rhs = thm
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?
        .1;
    Ok(rhs
        .as_app()
        .expect("cond g t e is an application")
        .1
        .clone())
}

/// `⊢ ¬(x = y)` for distinct literals `x ≠ y` — `reduce` folds `nat.eq` to `F`.
fn ne_lit(x: u64, y: u64) -> Result<Thm> {
    let eq_term = lit(x).equals(lit(y))?;
    eq_term
        .clone()
        .reduce()? // (x=y) = F
        .eq_mp(Thm::assume(eq_term.clone())?)? // {x=y} ⊢ F
        .imp_intro(&eq_term)? // (x=y) ⟹ F
        .not_intro() // ¬(x=y)
}

/// `⊢ ∀a b. v2 (code.pair a b) = a` — the first projection recovers the
/// exponent. By induction on `a` against the recurrence [`v2_recurrence`]:
///
/// * **base** `a = 0`: `pair 0 b = S(b+b)` is *odd*, so the guard's odd disjunct
///   (`parity`) fires → `cond T 0 _ = 0`.
/// * **step** `a = S a'`: `pair (S a) b = 2·(pair a b)` is *even and nonzero*, so
///   both guard disjuncts are `F` → `cond F 0 (S(v2 (·/2)))`; `(2X)/2 = X`
///   (`div.mul_cancel`) feeds the IH, giving `S a'`.
pub fn v2_pair() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let v2 = v2_explicit()?;
    let v2_at = |t: Term| Term::app(v2.clone(), t);

    // motive M(a) = (v2 (pair a b) = a), with `b` free.
    let body = v2_at(pair(a.clone(), b.clone())).equals(a.clone())?;
    let motive = Term::abs(nat_ty(), subst::close(&body, "a"));

    // ---- base: v2 (pair 0 b) = 0 ----
    let base = {
        let n0 = succ(add(b.clone(), b.clone())); // S(b+b) = pair 0 b
        let rec = v2_recurrence()?.all_elim(n0.clone())?; // v2 n0 = cond (guard n0) 0 (S(v2(n0/2)))
        // The guard's odd disjunct ¬(n0 = 2·(n0/2)) holds: n0 is odd (`parity`).
        let par = parity()?.all_elim(half(&n0))?.all_elim(b.clone())?; // ¬(n0 = (n0/2)+(n0/2))
        let td = two_double()?.all_elim(half(&n0))?; // 2·(n0/2) = (n0/2)+(n0/2)
        let r_thm = par.rewrite(&td.sym()?)?; // ¬(n0 = 2·(n0/2))
        let r_eq_t = r_thm.eqt_intro()?; // ¬(n0 = 2·(n0/2)) = T
        let red = rec
            .rewrite(&r_eq_t)? // cond ((n0=0) ∨ T) 0 (…)
            .rewrite(&or_true_r().all_elim(n0.clone().equals(lit(0))?)?)?; // cond T 0 (…)
        // The else-arm is read off `red`'s RHS (so it matches the recurrence's
        // β-normal form exactly), then discarded by `cond.true`.
        let else_arm = cond_else(&red)?;
        let cf = cond_true(&nat_ty(), &lit(0), &else_arm)?; // cond T 0 (…) = 0
        let v2n0 = red.trans(cf)?; // v2 n0 = 0
        let pzb = pair_zero_eq()?.all_elim(b.clone())?; // pair 0 b = S(b+b) = n0
        pzb.cong_arg(v2.clone())?.trans(v2n0)? // v2 (pair 0 b) = 0
    };

    // ---- step: (v2 (pair a b) = a) ⟹ (v2 (pair (S a) b) = S a) ----
    let step = {
        let a = nvar("a");
        let p = pair(a.clone(), b.clone()); // P = pair a b
        let body_a = v2_at(p.clone()).equals(a.clone())?; // v2 P = a   (the IH)
        let ih = Thm::assume(body_a.clone())?;
        let pse = pair_succ_eq()?.all_elim(a.clone())?.all_elim(b.clone())?; // pair (S a) b = 2·P
        let n1 = mul(lit(2), p.clone()); // 2·P
        let rec = v2_recurrence()?.all_elim(n1.clone())?; // v2 n1 = cond (guard n1) 0 (S(v2(n1/2)))

        // (2·P)/2 = P  via div.mul_cancel + mul_comm.
        let comm = nat::mul_comm().all_elim(lit(2))?.all_elim(p.clone())?; // 2·P = P·2
        let mc = div_mul_cancel()
            .all_elim(p.clone())?
            .all_elim(lit(2))?
            .imp_elim(ne_lit(2, 0)?)?; // (P·2)/2 = P
        let half_eq = comm
            .cong_arg(defs::nat_div())?
            .cong_fn(lit(2))? // (2·P)/2 = (P·2)/2
            .trans(mc)?; // (2·P)/2 = P

        // guard n1 = F:  left (n1 = 0) is F (`pair_ne_zero`), right is F (n1 is even).
        let ne0 = pair_ne_zero()?
            .all_elim(succ(a.clone()))?
            .all_elim(b.clone())?
            .rewrite(&pse)?; // ¬(n1 = 0)
        let l_eq_f = bool_eqf()
            .all_elim(n1.clone().equals(lit(0))?)?
            .imp_elim(ne0)?; // (n1 = 0) = F
        let even_eq = half_eq
            .clone()
            .cong_arg(Term::app(defs::nat_mul(), lit(2)))? // 2·(n1/2) = 2·P
            .sym()?; // n1 = 2·(n1/2)
        let r_term = n1.clone().equals(mul(lit(2), half(&n1)))?.not()?; // ¬(n1 = 2·(n1/2))
        let nn = Thm::assume(r_term.clone())?
            .not_elim(even_eq)? // {¬(n1=2·(n1/2))} ⊢ F
            .imp_intro(&r_term)?
            .not_intro()?; // ¬¬(n1 = 2·(n1/2))
        let r_eq_f = bool_eqf().all_elim(r_term.clone())?.imp_elim(nn)?; // ¬(n1 = 2·(n1/2)) = F

        let red = rec
            .rewrite(&l_eq_f)? // cond (F ∨ R) 0 (…)
            .rewrite(&r_eq_f)? // cond (F ∨ F) 0 (…)
            .rewrite(&or_false_l().all_elim(Term::bool_lit(false))?)?; // cond F 0 (…)
        let else_arm = cond_else(&red)?; // S(v2(n1/2)), β-normal
        let cf = cond_false(&nat_ty(), &lit(0), &else_arm)?; // cond F 0 (…) = S(v2(n1/2))
        // `half_eq` rewrites `n1/2 → P` inside the (β-reduced) `v2(n1/2)`; the IH
        // is stated on the *un-reduced* `v2 P`, so bridge through `beta_nf`.
        let bridge = beta_nf(v2_at(p.clone())).sym()?; // β-nf(v2 P) = v2 P
        let v2n1 = red
            .trans(cf)? // v2 n1 = S(v2(n1/2))
            .rewrite(&half_eq)? // v2 n1 = S(β-nf(v2 P))
            .rewrite(&bridge)? // v2 n1 = S(v2 P)
            .rewrite(&ih)?; // v2 n1 = S a
        pse.cong_arg(v2.clone())? // v2 (pair (S a) b) = v2 n1
            .trans(v2n1)? // v2 (pair (S a) b) = S a
            .imp_intro(&body_a)? // (v2 P = a) ⟹ (v2 (pair (S a) b) = S a)
    };

    induct_on("a", &motive, base, step)?
        .all_elim(a.clone())? // v2 (pair a b) = a  (a, b free)
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stage_a_builds() {
        for (name, thm) in [
            ("two_double", two_double()),
            ("half_lt", half_lt()),
            ("prove_hext_v2", prove_hext_v2()),
            ("v2_recurrence", v2_recurrence()),
            ("v2_pair", v2_pair()),
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }
}
