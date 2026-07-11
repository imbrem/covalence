//! Euclidean division facts for `nat`.
//!
//! `nat.div` is **defined by recursion** in the kernel (`defs/nat.rs`,
//! [`nat_div_body`](covalence_hol_eval::defs)) — the explicit course-of-values
//! fixpoint of the division step functional `F n g := λm. cond (m=0 ∨ n<m) 0
//! (S (g (n−m) m))` (`g` is read only at `n−m < n`, so `Hext F` holds). This
//! module proves the rest **about that constant, choice-free** — no Hilbert ε
//! beyond the shared `natRec`, no `spec_ax`:
//!
//! - [`div_explicit`] reconstructs the kernel's definitional body and
//!   [`div_explicit_recurrence`] reads its recurrence off [`cv_fixpoint`];
//!   [`nat_div_recurrence`] folds that onto `nat.div` via the definitional
//!   `delta`-unfold (`nat_div_def_matches_explicit` checks the body matches).
//! - [`nat_div_spec`] discharges the proved `div.zero`/`div.bounds` (about a
//!   *free* recurrence witness, in `nat_div.cov`) at `nat.div` to get its
//!   Euclidean bounds; the `div_mod`/`mod_lt`/recurrence/`shr` facts build on
//!   those in `nat_div_facts.cov`. `nat.mod n m := n − (n/m)·m`.
//!
//! Arithmetic + `cond`/`bool` helper lemmas live in `nat_div.cov`; the term
//! construction (step functional, `Hext`, recurrence) lives here.

use covalence_hol_eval::derived::DerivedRules;
use std::collections::BTreeMap;

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs;
use smol_str::SmolStr;

use crate::init::cv_recursion::{cv_exists, cv_fixpoint, cv_witness};
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
    covalence_hol_eval::mk_nat(0u64)
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
/// `cond` at result type `nat` — the kernel `defs::cond` (`bool.cond`), which
/// `cond.cov` registers under the name `cond` and states its clauses
/// (`cond.true`/`cond.false`/`cond.cong_arm`) about. (Equals `defs::cond(nat)`;
/// looked up through the env so the `.cov` lemmas and this term share it.)
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
    let h_g = Thm::assume(g.clone().equals(covalence_hol_eval::mk_bool(false))?)?;
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
        .imp_intro(&g.clone().equals(covalence_hol_eval::mk_bool(false))?)?; // {agree} ⊢ g=F ⟹ S..=S..

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

/// The seed `λm. 0 : nat → nat` — the (value-irrelevant) base history.
fn div_seed() -> Term {
    Term::abs(nat(), zero())
}

/// The **explicit, choice-free** course-of-values division function: the closed
/// term that `nat.div` is defined as (`cv_witness` at the division step
/// functional — only `natRec`/`cond`/`nat.sub`/`succ`, no ε beyond the shared
/// `natRec`). `nat.div n m = (div_explicit n) m`.
pub fn div_explicit() -> Result<Term> {
    use covalence_core::Var;
    let w =
        subst::subst_tfrees_in_term(&cv_witness(), &BTreeMap::from([(SmolStr::from("a"), nn())]));
    let w = subst::subst_free(&w, &Var::new("F", f_div()?.type_of()?), &f_div()?);
    Ok(subst::subst_free(&w, &Var::new("d", nn()), &div_seed()))
}

/// `⊢ ∀n m. div n m = cond (m=0 ∨ n<m) 0 (S (div (n−m) m))` for the **explicit**
/// `div := div_explicit()` — its recurrence, read off [`cv_fixpoint`] (no `∃`,
/// no ε-skolemisation). This is what lets `nat.div`'s recurrence be a plain
/// `delta`-unfold once `nat.div := div_explicit`, removing the `spec_ax` seam.
pub fn div_explicit_recurrence() -> Result<Thm> {
    let (n, m) = (nvar("n"), nvar("m"));
    let div = div_explicit()?;
    // ⊢ ∀n. div n = F n div  (F = f_div, div = the explicit witness).
    let fixed = cv_fixpoint()?
        .inst_tfree("a", nn())?
        .inst("F", f_div()?)?
        .inst("d", div_seed())?
        .imp_elim(prove_hext_div()?)?;
    fixed
        .all_elim(n.clone())? // div n = F n div
        .cong_fn(m.clone())? // div n m = (F n div) m
        .trans(beta_nf(Term::app(
            Term::app(Term::app(f_div()?, n.clone()), div.clone()),
            m.clone(),
        )))? // = cond (m=0 ∨ n<m) 0 (S (div (n−m) m))
        .all_intro("m", nat())?
        .all_intro("n", nat())
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

// ============================================================================
// `nat.div`'s recurrence and bounds — from the recursive definition (no ε)
// ============================================================================
//
// `nat.div` is *defined* as the explicit cv fixpoint (`defs::nat_div_body`),
// which equals `div_explicit()` (verified by `nat_div_def_matches_explicit`). So
// its recurrence is `div_explicit_recurrence` rewritten through the definitional
// unfold `⊢ nat.div = div_explicit` — no Hilbert ε, no `spec_ax`. The Euclidean
// bounds are then the proved `div.zero`/`div.bounds` (about a *free* recurrence
// witness) instantiated at `nat.div` and discharged with its recurrence.

/// `⊢ ∀n m. nat.div n m = cond (m=0 ∨ n<m) 0 (S (nat.div (n−m) m))` — the
/// Euclidean recurrence for the **kernel** `nat.div`, by `delta`-unfolding the
/// definition into [`div_explicit_recurrence`] and folding the recursive call
/// back to `nat.div`.
pub fn nat_div_recurrence() -> Result<Thm> {
    let (n, m) = (nvar("n"), nvar("m"));
    // ⊢ nat.div = div_explicit  (definitional; the body *is* `div_explicit`).
    let unfold = defs::nat_div().delta()?;
    // nat.div n m = div_explicit n m
    let lhs = unfold.clone().cong_fn(n.clone())?.cong_fn(m.clone())?;
    // div_explicit n m = cond(…) 0 (S R), where R is the β-normal `div_explicit (n−m) m`.
    let mid = div_explicit_recurrence()?
        .all_elim(n.clone())?
        .all_elim(m.clone())?;
    // Fold the recursive call back to `nat.div (n−m) m`. The recurrence's RHS has it
    // β-reduced (R), so connect `R = div_explicit (n−m) m = nat.div (n−m) m`.
    let de = div_explicit()?;
    let de_app = Term::app(Term::app(de, sub(n.clone(), m.clone())), m.clone());
    let nd_eq_de = unfold
        .cong_fn(sub(n.clone(), m.clone()))? // nat.div (n−m) = div_explicit (n−m)
        .cong_fn(m.clone())?; // nat.div (n−m) m = div_explicit (n−m) m
    let r_eq_nd = beta_nf(de_app).sym()?.trans(nd_eq_de.sym()?)?; // R = nat.div (n−m) m
    let rhs = r_eq_nd
        .cong_arg(defs::nat_succ())? // S R = S (nat.div (n−m) m)
        .cong_arg(Term::app(Term::app(cond_op(), guard(&n, &m)?), zero()))?; // cond g 0 (S R) = …
    lhs.trans(mid)?
        .trans(rhs)?
        .all_intro("m", nat())?
        .all_intro("n", nat())
}

/// `⊢ (m=0 ⟹ nat.div n m = 0) ∧ (¬(m=0) ⟹ nat.div n m·m ≤ n ∧ n < S(nat.div n m)·m)`
/// universally over `n, m` — `nat.div`'s defining clauses, **proved** from its
/// recursive definition: `nat_div_recurrence` discharges the proved
/// `div.zero`/`div.bounds` (stated about a free recurrence witness) at `nat.div`.
pub fn nat_div_spec() -> Result<Thm> {
    let (n, m) = (nvar("n"), nvar("m"));
    let rec = nat_div_recurrence()?;
    // `div.zero`/`div.bounds` : `REC(div) ⟹ …` (free `div`); instantiate at
    // `nat.div` and discharge with its recurrence.
    let zero = div_zero()
        .inst("div", defs::nat_div())?
        .imp_elim(rec.clone())?;
    let bounds = div_bounds().inst("div", defs::nat_div())?.imp_elim(rec)?;
    zero.all_elim(n.clone())?
        .all_elim(m.clone())?
        .and_intro(bounds.all_elim(n.clone())?.all_elim(m.clone())?)?
        .all_intro("m", nat())?
        .all_intro("n", nat())
}
/// `⊢ ∀n m. m=0 ⟹ nat.div n m = 0` — the `m = 0` clause projected out of
/// [`nat_div_spec`].
pub fn nat_div_zero() -> Result<Thm> {
    let (n, m) = (nvar("n"), nvar("m"));
    nat_div_spec()?
        .all_elim(n)?
        .all_elim(m)?
        .and_elim_l()?
        .all_intro("m", nat())?
        .all_intro("n", nat())
}

/// The `m ≠ 0` clause of [`nat_div_spec`], projecting the lower (`left`) or upper
/// bound of the conjunction.
fn nat_div_pos_part(left: bool) -> Result<Thm> {
    let (n, m) = (nvar("n"), nvar("m"));
    let case_pos = nat_div_spec()?.all_elim(n)?.all_elim(m)?.and_elim_r()?; // ¬(m=0) ⟹ (le ∧ lt)
    let not_m0 = case_pos
        .concl()
        .as_app()
        .and_then(|(f, _)| f.as_app())
        .map(|(_, a)| a.clone())
        .expect("case_pos is an implication");
    let conj = case_pos.imp_elim(Thm::assume(not_m0.clone())?)?; // {¬(m=0)} ⊢ le ∧ lt
    let part = if left {
        conj.and_elim_l()?
    } else {
        conj.and_elim_r()?
    };
    part.imp_intro(&not_m0)?
        .all_intro("m", nat())?
        .all_intro("n", nat())
}

/// `⊢ ∀n m. ¬(m=0) ⟹ nat.div n m · m ≤ n` — the Euclidean lower bound.
pub fn nat_div_le() -> Result<Thm> {
    nat_div_pos_part(true)
}

/// `⊢ ∀n m. ¬(m=0) ⟹ n < S(nat.div n m) · m` — the Euclidean upper bound.
pub fn nat_div_lt() -> Result<Thm> {
    nat_div_pos_part(false)
}

/// `⊢ ∀n m. nat.mod n m = nat.sub n (nat.mul (nat.div n m) m)` — the `nat.mod`
/// defining equation, surfaced as a lemma so `nat_div_facts.cov` can rewrite
/// `nat.mod` without re-deriving the δ-unfold.
pub fn nat_mod_def() -> Result<Thm> {
    let (n, m) = (nvar("n"), nvar("m"));
    let mod_nm = Term::app(Term::app(defs::nat_mod(), n), m);
    let eq = crate::init::eq::delta_head(&mod_nm)?; // nat.mod n m = (λn m. …) n m
    let rhs = eq.concl().as_app().expect("= is an application").1.clone();
    eq.trans(beta_nf(rhs))? // nat.mod n m = nat.sub n (nat.mul (nat.div n m) m)
        .all_intro("m", nat())?
        .all_intro("n", nat())
}

/// The transferred `nat.div` selector facts as a script env: `nat.div.zero`,
/// `nat.div.le`, `nat.div.lt` (over the *spec* `nat.div`, not a free `div`)
/// plus `nat.mod.def`, imported by `nat_div_facts.cov` to prove `div_mod` /
/// `mod_lt`.
pub fn nat_div_facts_env() -> crate::script::Env {
    let mut e = crate::script::Env::empty();
    e.define_lemma("nat.div.zero", nat_div_zero().expect("nat.div.zero"));
    e.define_lemma("nat.div.le", nat_div_le().expect("nat.div.le"));
    e.define_lemma("nat.div.lt", nat_div_lt().expect("nat.div.lt"));
    e.define_lemma("nat.mod.def", nat_mod_def().expect("nat.mod.def"));
    e.define_lemma("nat.pos_of_ne_zero", nat_pos_of_ne_zero());
    e
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
        // The recurrence-parameterised division facts (free `div`), discharged
        // at `nat.div` by `nat_div_spec` below.
        "div.zero"            => pub fn div_zero;
        "div.bounds"          => pub fn div_bounds;
    }
}

pub use cov::{
    bool_cases, bool_eqf, bool_eqt, cond_cong_arm, div_bounds, div_zero, nat_lt_add_pos,
    nat_lt_or_ge, nat_pos_of_ne_zero, nat_sub_lt_self, or_false_l, or_true_r,
};

crate::cov_theory! {
    /// The headline Euclidean facts over `nat.div` / `nat.mod` — the division
    /// identity (`div.mod`) and the remainder bound (`mod.lt`) — built on the
    /// `nat.div` selector facts ([`nat_div_facts_env`]).
    pub mod facts from "nat_div_facts.cov" {
        import "core" = crate::script::Env::core();
        import "logic" = crate::init::logic::cov::env();
        import "natrec" = crate::init::nat::natrec_env();
        import "nat" = crate::init::nat::cov::env();
        import "divfacts" = super::nat_div_facts_env();
        "div.mul_le" => pub fn div_mul_le;
        "div.mod" => pub fn div_mod;
        "mod.lt"  => pub fn mod_lt;
        "div.unique" => pub fn div_unique;
        "div.mul_cancel" => pub fn div_mul_cancel;
        "div.lt" => pub fn div_lt;
        "div.ge" => pub fn div_ge;
        "div.div" => pub fn div_div;
        "shr.eq_div_pow" => pub fn shr_eq_div_pow;
        "mod.lt_eq" => pub fn mod_lt_eq;
        "mod.ge" => pub fn mod_ge;
    }
}

pub use facts::{
    div_div, div_ge, div_lt, div_mod, div_mul_cancel, div_mul_le, div_unique, mod_ge, mod_lt,
    mod_lt_eq, shr_eq_div_pow,
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

    /// The recurrence about the *explicit* (choice-free) division term, and that
    /// the term uses core's `defs::cond` (so it is expressible in the kernel).
    #[test]
    fn div_explicit_recurrence_proves() {
        let thm = super::div_explicit_recurrence().expect("div_explicit_recurrence");
        assert!(
            thm.hyps().is_empty(),
            "div_explicit_recurrence should be closed"
        );
    }

    /// The kernel `nat.div` definition (core) unfolds to exactly `div_explicit`
    /// (init) — so the proven recurrence is about `nat.div` itself.
    #[test]
    fn nat_div_def_matches_explicit() {
        use crate::init::ext::TermExt;
        let unfold = covalence_hol_eval::defs::nat_div()
            .delta()
            .expect("delta nat.div");
        let body = unfold.concl().as_eq().expect("eq").1.clone();
        assert_eq!(body, super::div_explicit().expect("div_explicit"));
    }

    /// `nat.div`'s Euclidean clauses, derived from its recursive definition.
    #[test]
    fn nat_div_spec_proves() {
        let thm = super::nat_div_spec().expect("nat_div_spec");
        assert!(thm.hyps().is_empty(), "nat_div_spec should be closed");
    }

    /// The division identity `div.mod` and remainder bound `mod.lt`.
    #[test]
    fn div_mod_and_mod_lt_prove() {
        assert!(
            super::div_mod().hyps().is_empty(),
            "div.mod should be closed"
        );
        assert!(super::mod_lt().hyps().is_empty(), "mod.lt should be closed");
    }

    /// Quotient uniqueness and `(a·b)/b = a`.
    #[test]
    fn div_unique_and_mul_cancel_prove() {
        assert!(
            super::div_unique().hyps().is_empty(),
            "div.unique should be closed"
        );
        assert!(
            super::div_mul_cancel().hyps().is_empty(),
            "div.mul_cancel should be closed"
        );
    }

    /// The division recurrence as conditional equations.
    #[test]
    fn div_recurrence_equations_prove() {
        assert!(super::div_lt().hyps().is_empty(), "div.lt should be closed");
        assert!(super::div_ge().hyps().is_empty(), "div.ge should be closed");
    }

    /// The iterated-division law `(a/b)/c = a/(b·c)`.
    #[test]
    fn div_div_proves() {
        assert!(
            super::div_div().hyps().is_empty(),
            "div.div should be closed"
        );
    }

    /// The `shr` bridge `shr a m = a / 2^m`.
    #[test]
    fn shr_eq_div_pow_proves() {
        assert!(
            super::shr_eq_div_pow().hyps().is_empty(),
            "shr.eq_div_pow should be closed"
        );
    }

    /// The modulus recurrence (conditional equations).
    #[test]
    fn mod_recurrence_proves() {
        assert!(
            super::mod_lt_eq().hyps().is_empty(),
            "mod.lt_eq should be closed"
        );
        assert!(super::mod_ge().hyps().is_empty(), "mod.ge should be closed");
    }
}
