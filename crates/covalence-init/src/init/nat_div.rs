//! Euclidean division facts for `nat` — `div_mod` and `mod_lt`.
//!
//! `nat.div n m` is a Hilbert-ε selector (`defs/nat.rs`) pinned by the Euclidean
//! bounds `m ≠ 0 ⟹ (n/m)·m ≤ n < S(n/m)·m`, and `nat.mod n m := n - (n/m)·m`.
//! Those bounds become *provable* once we exhibit a function satisfying them.
//!
//! We build that function **constructively**, not by ε-skolemising a pointwise
//! existential — so the development transports across foundations (recursion is
//! foundation-neutral; choice is not; division needs no choice). [`cv_div_recurrence`]
//! instantiates the foundation-neutral course-of-values recursion theorem
//! [`cv_exists`](crate::init::cv_recursion::cv_exists) at the division step
//! functional `F n g := λm. cond (m=0 ∨ n<m) 0 (S (g (n−m) m))` (its recursive
//! read is at `n−m < n`, so `Hext F` holds), yielding `div` with the Euclidean
//! recurrence. The bounds then follow by [`strong_induct`](crate::init::lambda_iter::strong_induct)
//! through that recurrence; transferring them to the ε-selector `nat.div` via
//! `spec_ax` (a transitional seam — see the `nat.div` redefinition skeleton in
//! `covalence-core/SKELETONS.md`) gives `div_mod` / `mod_lt`.
//!
//! Arithmetic + `cond`/`bool` helper lemmas live in `nat_div.cov`; the
//! construction (step functional, `Hext`, recurrence) lives here.

use std::collections::BTreeMap;

use covalence_core::{Result, Term, Thm, Type, defs, subst};
use smol_str::SmolStr;

use crate::init::cv_recursion::cv_exists;
use crate::init::eq::beta_nf;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::{exists_elim, exists_intro};
use crate::script::ConstDef;

// ============================================================================
// The division step functional and its course-of-values fixpoint
// ============================================================================
//
// For division the recursion result type is `'a := nat → nat` (a "history" of
// quotients-of-`·`-by-each-`m`). The step functional
//   F n g := λm. cond (m=0 ∨ n<m) 0 (S (g (n−m) m))
// reads its history `g` only at `n−m < n` (when the guard is false), so it is
// below-`n` extensional (`Hext`), and `cv_exists` hands back a fixpoint `div`
// with the Euclidean recurrence `div n m = if m=0 ∨ n<m then 0 else S(div (n−m) m)`.

fn nat() -> Type {
    Type::nat()
}
/// `nat → nat` — the cv-recursion result type for division.
fn nn() -> Type {
    Type::fun(nat(), nat())
}
/// `nat → (nat → nat)` — a history.
fn g_ty() -> Type {
    Type::fun(nat(), nn())
}
fn nvar(s: &str) -> Term {
    Term::free(s, nat())
}
fn zero() -> Term {
    Term::nat_lit(0u64)
}
fn succ(n: Term) -> Term {
    Term::app(defs::nat_succ(), n)
}
fn lt(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_lt(), a), b)
}
fn sub(a: Term, b: Term) -> Term {
    Term::app(Term::app(defs::nat_sub(), a), b)
}
/// `cond` at result type `nat` — the SAME constant `cond.cov` defines (and that
/// `cond.true`/`cond.false`/`cond.cong_arm` are stated over), not the kernel
/// `defs::cond` (`bool.cond`); the two are definitionally equal but distinct
/// symbols, so everything must use one consistently.
fn cond_op() -> Term {
    let cd = crate::init::cond::cov::env()
        .lookup_const("cond")
        .expect("cond.cov defines `cond`");
    let t = match cd {
        ConstDef::Poly(t) | ConstDef::Op(t) => t,
        ConstDef::Eq => panic!("`cond` is not Eq"),
    };
    let sub = BTreeMap::from([(SmolStr::from("a"), nat())]);
    subst::subst_tfrees_in_term(&t, &sub)
}
fn cond3(g: Term, t: Term, e: Term) -> Term {
    Term::app(Term::app(Term::app(cond_op(), g), t), e)
}
/// `(m = 0) ∨ (n < m)` — the base-case guard.
fn guard(n: &Term, m: &Term) -> Result<Term> {
    m.clone().equals(zero())?.or(lt(n.clone(), m.clone()))
}
/// `F := λn g m. cond (m=0 ∨ n<m) 0 (S (g (n−m) m))` — a raw lambda (β trivial).
fn f_div() -> Result<Term> {
    let (n, g, m) = (nvar("n"), Term::free("g", g_ty()), nvar("m"));
    let rec = Term::app(Term::app(g, sub(n.clone(), m.clone())), m.clone()); // g (n−m) m
    let body = cond3(guard(&n, &m)?, zero(), succ(rec));
    let lm = Term::abs(nat(), subst::close(&body, "m"));
    let lg = Term::abs(g_ty(), subst::close(&lm, "g"));
    Ok(Term::abs(nat(), subst::close(&lg, "n")))
}

fn fun_ext() -> Thm {
    crate::init::cat::cov::env()
        .lemma_ready("fun.ext")
        .expect("cat.cov fun.ext")
}

/// `⊢ Hext F` — the below-`x` extensionality of the division step functional.
fn prove_hext_div() -> Result<Thm> {
    let f = f_div()?;
    let (x, p, q, m) = (
        nvar("x"),
        Term::free("p", g_ty()),
        Term::free("q", g_ty()),
        nvar("m"),
    );
    let agree_term = {
        let i = nvar("i");
        lt(i.clone(), x.clone())
            .imp(Term::app(p.clone(), i.clone()).equals(Term::app(q.clone(), i.clone()))?)?
            .forall("i", nat())?
    };
    let h_agree = Thm::assume(agree_term.clone())?;

    // The β-reduced division step at (x, ·, m): F x r m = cond (guard x m) 0 (S (r (x−m) m)).
    let red = |r: &Term| -> Thm {
        beta_nf(Term::app(
            Term::app(Term::app(f.clone(), x.clone()), r.clone()),
            m.clone(),
        ))
    };

    // false-arm obligation: guard = F ⟹ S(p(x−m)m) = S(q(x−m)m).
    let g = guard(&x, &m)?;
    let h_g = Thm::assume(g.clone().equals(Term::bool_lit(false))?)?;
    let m_eq_0 = m.clone().equals(zero())?;
    let x_lt_m = lt(x.clone(), m.clone());
    // ¬(m=0)
    let not_m0 = h_g
        .clone()
        .eq_mp(Thm::assume(m_eq_0.clone())?.or_intro_l(x_lt_m.clone())?)? // {g=F,m=0} ⊢ F
        .imp_intro(&m_eq_0)?
        .not_intro()?; // {g=F} ⊢ ¬(m=0)
    // ¬(x<m)
    let not_xm = h_g
        .clone()
        .eq_mp(Thm::assume(x_lt_m.clone())?.or_intro_r(m_eq_0.clone())?)?
        .imp_intro(&x_lt_m)?
        .not_intro()?; // {g=F} ⊢ ¬(x<m)
    // m ≤ x  (from ¬(x<m), via lt_or_ge)
    let m_le_x_term = Term::app(Term::app(defs::nat_le(), m.clone()), x.clone());
    let m_le_x = nat_lt_or_ge()
        .all_elim(x.clone())?
        .all_elim(m.clone())?
        .or_elim(
            not_xm
                .clone()
                .not_elim(Thm::assume(x_lt_m.clone())?)?
                .false_elim(m_le_x_term.clone())?
                .imp_intro(&x_lt_m)?,
            Thm::assume(m_le_x_term.clone())?.imp_intro(&m_le_x_term)?,
        )?; // {g=F} ⊢ m ≤ x
    // x − m < x
    let sub_lt = nat_sub_lt_self()
        .all_elim(x.clone())?
        .all_elim(m.clone())?
        .imp_elim(not_m0)?
        .imp_elim(m_le_x)?; // {g=F} ⊢ x−m < x
    // p(x−m) m = q(x−m) m, then S-cong
    let arm_eq = h_agree
        .clone()
        .all_elim(sub(x.clone(), m.clone()))?
        .imp_elim(sub_lt)? // {g=F, agree} ⊢ p(x−m) = q(x−m)
        .cong_fn(m.clone())? // p(x−m) m = q(x−m) m
        .cong_arg(defs::nat_succ())? // S(p(x−m)m) = S(q(x−m)m)
        .imp_intro(&g.clone().equals(Term::bool_lit(false))?)?; // {agree} ⊢ g=F ⟹ S..=S..

    // cond congruence over the false arm, instantiated.
    let cong = cond_cong_arm()
        .inst_tfree("a", nat())?
        .all_elim(g.clone())?
        .all_elim(zero())?
        .all_elim(succ(Term::app(
            Term::app(p.clone(), sub(x.clone(), m.clone())),
            m.clone(),
        )))?
        .all_elim(succ(Term::app(
            Term::app(q.clone(), sub(x.clone(), m.clone())),
            m.clone(),
        )))?
        .imp_elim(arm_eq)?; // {agree} ⊢ cond_form p = cond_form q

    // pointwise: F x p m = F x q m
    let pointwise = red(&p)
        .trans(cong)?
        .trans(red(&q).sym()?)?
        .all_intro("m", nat())?; // {agree} ⊢ ∀m. F x p m = F x q m

    // fun.ext: F x p = F x q
    let fxp = Term::app(Term::app(f.clone(), x.clone()), p.clone());
    let fxq = Term::app(Term::app(f.clone(), x.clone()), q.clone());
    let feq = fun_ext()
        .inst_tfree("a", nat())?
        .inst_tfree("b", nat())?
        .all_elim(fxp)?
        .all_elim(fxq)?
        .imp_elim(pointwise)?; // {agree} ⊢ F x p = F x q
    feq.imp_intro(&agree_term)?
        .all_intro("q", g_ty())?
        .all_intro("p", g_ty())?
        .all_intro("x", nat())
}

/// `⊢ ∃div. ∀n m. div n m = cond (m=0 ∨ n<m) 0 (S (div (n−m) m))` — the
/// constructive Euclidean division function exists, with its recurrence. Built
/// from [`cv_exists`] at the division step functional (no choice operator).
pub fn cv_div_recurrence() -> Result<Thm> {
    let f = f_div()?;
    // ∃fix. ∀n. fix n = F n fix
    let ex = cv_exists()?
        .inst_tfree("a", nn())?
        .inst("F", f.clone())?
        .imp_elim(prove_hext_div()?)?;

    // repackage to the per-(n,m) recurrence.
    let (n, m, fixv) = (nvar("n"), nvar("m"), Term::free("fix", g_ty()));
    let rec_body = |d: &Term| -> Result<Term> {
        Term::app(Term::app(d.clone(), n.clone()), m.clone()).equals(cond3(
            guard(&n, &m)?,
            zero(),
            succ(Term::app(
                Term::app(d.clone(), sub(n.clone(), m.clone())),
                m.clone(),
            )),
        ))
    };
    let pred_body = rec_body(&fixv)?.forall("m", nat())?.forall("n", nat())?;
    let pred = Term::abs(g_ty(), subst::close(&pred_body, "fix"));

    let step = {
        // exists_elim wants the step antecedent as `pred_ex fix` (a β-redex);
        // assume that, β-reduce to the usable `∀n. fix n = F n fix`.
        let pred_ex = ex.concl().as_app().expect("∃ is an application").1.clone();
        let hf_redex = Term::app(pred_ex, fixv.clone());
        let hf = crate::init::eq::beta_reduce(Thm::assume(hf_redex.clone())?)?;
        // fix n m = F n fix m = cond (guard n m) 0 (S (fix (n−m) m))
        let recur = hf
            .all_elim(n.clone())?
            .cong_fn(m.clone())? // fix n m = (F n fix) m
            .trans(beta_nf(Term::app(
                Term::app(Term::app(f.clone(), n.clone()), fixv.clone()),
                m.clone(),
            )))? // = cond ...
            .all_intro("m", nat())?
            .all_intro("n", nat())?; // ∀n m. fix n m = cond ...
        exists_intro(pred.clone(), fixv.clone(), beta_nf_to(&pred, &fixv, recur)?)?
            .imp_intro(&hf_redex)?
            .all_intro("fix", g_ty())?
    };
    exists_elim(ex, Term::app(defs::exists(g_ty()), pred), step)
}

/// `⊢ pred witness` (β-redex form) from `⊢ body`, the β-reduct.
fn beta_nf_to(pred: &Term, witness: &Term, body: Thm) -> Result<Thm> {
    crate::init::eq::beta_expand(pred, witness.clone(), body)
}

crate::cov_theory! {
    /// Arithmetic helper lemmas for the division development.
    pub mod cov from "nat_div.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "natrec" = crate::init::nat::natrec_env();
        import "nat" = crate::init::nat::cov::env();
        import "lambda_iter" = crate::init::lambda_iter::cov::env();
        import "cond" = crate::init::cond::cov::env();
        "nat.lt_or_ge"        => pub fn nat_lt_or_ge;
        "nat.pos_of_ne_zero"  => pub fn nat_pos_of_ne_zero;
        "nat.lt_add_pos"      => pub fn nat_lt_add_pos;
        "nat.sub_lt_self"     => pub fn nat_sub_lt_self;
        "bool.cases"          => pub fn bool_cases;
        "cond.cong_arm"       => pub fn cond_cong_arm;
        "bool.eqt"            => pub fn bool_eqt;
        "bool.eqf"            => pub fn bool_eqf;
        "or.true_r"           => pub fn or_true_r;
        "or.false_l"          => pub fn or_false_l;
    }
}

pub use cov::{
    bool_cases, bool_eqf, bool_eqt, cond_cong_arm, nat_lt_add_pos, nat_lt_or_ge,
    nat_pos_of_ne_zero, nat_sub_lt_self, or_false_l, or_true_r,
};

#[cfg(test)]
mod tests {
    #[test]
    fn helpers_prove() {
        assert!(super::nat_lt_or_ge().hyps().is_empty());
        assert!(super::nat_pos_of_ne_zero().hyps().is_empty());
        assert!(super::nat_lt_add_pos().hyps().is_empty());
        assert!(super::nat_sub_lt_self().hyps().is_empty());
        assert!(super::bool_cases().hyps().is_empty());
        assert!(super::cond_cong_arm().hyps().is_empty());
    }

    /// The constructive Euclidean division function + recurrence (via `cv_exists`).
    #[test]
    fn cv_div_recurrence_proves() {
        let thm = super::cv_div_recurrence().expect("cv_div_recurrence");
        assert!(thm.hyps().is_empty(), "cv_div_recurrence should be closed");
    }
}
