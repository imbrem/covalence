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

use crate::init::cv_recursion::{cv_fixpoint, cv_witness};
use crate::init::eq::{beta_nf, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::lambda_iter::{nat_lt_le_trans, nat_zero_or_succ};
use crate::init::logic::exists_elim;
use crate::init::nat;
use crate::init::nat_div::{cond_cong_arm, div_mul_le, nat_pos_of_ne_zero};
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
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }
}
