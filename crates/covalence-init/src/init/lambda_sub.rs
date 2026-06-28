//! # λ_iter subtyping on the type fragment — reflexivity + transitivity
//!
//! The first genuine **metatheorem** of the deep embedding. Subtyping on the
//! type fragment (`A ::= 0 | 1 | Xᵢ | A⊗B | A+B`, no binders) is the structural
//! **congruence** — covariant in `⊗`/`+`, reflexive at the leaves — reified as a
//! binary impredicative inductive relation over the [`lambda_ty`] codes:
//!
//! ```text
//!     Subtype a b  :=  ∀R:nat→nat→bool. ClosedSub R ⟹ R a b
//! ```
//!
//! where `ClosedSub R` conjoins the five congruence clauses. With the five
//! [intro rules](sub_tensor) and [rule induction](sub_induction), we prove:
//!
//! * [`sub_eq`]    `⊢ ∀a b. Subtype a b ⟹ a = b`  — for this binder/width-free
//!   fragment subtyping *is* structural equality; by rule induction on the
//!   subtyping derivation (each rule is equality-preserving). No `code.pair`
//!   injectivity needed.
//! * [`sub_refl`]  `⊢ ∀c. WfTyCode c ⟹ Subtype c c` — by [`wf_ty_induction`].
//! * [`sub_trans`] `⊢ ∀a b c. Subtype a b ⟹ Subtype b c ⟹ Subtype a c` — `a = b`
//!   from [`sub_eq`], then rewrite `Subtype b c`.
//!
//! Richer subtyping (initial `0 <: A` / terminal `A <: 1`, or the
//! expression-level relation) needs genuine inversion + `code.pair` injectivity
//! — see `init/SKELETONS.md`.

use covalence_core::{Result, Term, Thm, Type};

use crate::init::eq::{beta_expand, beta_nf_concl, beta_nf_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::lambda_ty::{ty_base, ty_empty, ty_sum, ty_tensor, ty_unit, wf_ty_induction};

// ============================================================================
// Term helpers
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}
fn bool_ty() -> Type {
    Type::bool()
}
fn lit(n: u64) -> Term {
    Term::nat_lit(n)
}
fn nvar(s: &str) -> Term {
    Term::free(s, nat_ty())
}

/// `R : nat → nat → bool` — the impredicative relation variable.
fn r_ty() -> Type {
    Type::fun(nat_ty(), Type::fun(nat_ty(), bool_ty()))
}
fn r_var() -> Term {
    Term::free("R", r_ty())
}
/// `r a b` — a relation `r` applied to two codes.
fn rapp(r: &Term, a: &Term, b: &Term) -> Term {
    Term::app(Term::app(r.clone(), a.clone()), b.clone())
}

// ============================================================================
// `ClosedSub R` and `Subtype`
// ============================================================================

/// Number of congruence clauses (one per type constructor).
const N_CLAUSES: usize = 5;

/// `ClosedSub R` — the right-nested conjunction of the five congruence clauses:
///
/// ```text
///   R ⌜0⌝ ⌜0⌝ ∧ R ⌜1⌝ ⌜1⌝ ∧ (∀i. R ⌜Xᵢ⌝ ⌜Xᵢ⌝)
///     ∧ (∀a a' b b'. R a a' ⟹ R b b' ⟹ R ⌜a⊗b⌝ ⌜a'⊗b'⌝)
///     ∧ (∀a a' b b'. R a a' ⟹ R b b' ⟹ R ⌜a+b⌝ ⌜a'+b'⌝)
/// ```
fn closed_sub(r: &Term) -> Result<Term> {
    let (i, a, ap, b, bp) = (nvar("i"), nvar("a"), nvar("a'"), nvar("b"), nvar("b'"));

    let c_empty = rapp(r, &ty_empty(), &ty_empty());
    let c_unit = rapp(r, &ty_unit(), &ty_unit());
    let c_base = rapp(r, &ty_base(i.clone()), &ty_base(i.clone())).forall("i", nat_ty())?;

    let congruence = |ctor: &dyn Fn(Term, Term) -> Term| -> Result<Term> {
        rapp(r, &a, &ap)
            .imp(rapp(r, &b, &bp).imp(rapp(
                r,
                &ctor(a.clone(), b.clone()),
                &ctor(ap.clone(), bp.clone()),
            ))?)?
            .forall("b'", nat_ty())?
            .forall("b", nat_ty())?
            .forall("a'", nat_ty())?
            .forall("a", nat_ty())
    };
    let c_tensor = congruence(&ty_tensor)?;
    let c_sum = congruence(&ty_sum)?;

    let clauses = [c_empty, c_unit, c_base, c_tensor, c_sum];
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter.next().expect("N_CLAUSES > 0");
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `Subtype a b := ∀R. ClosedSub R ⟹ R a b`.
pub fn subtype(a: &Term, b: &Term) -> Result<Term> {
    closed_sub(&r_var())?
        .imp(rapp(&r_var(), a, b))?
        .forall("R", r_ty())
}

/// From a right-nested conjunction of `n` clauses, extract conjunct `k`.
fn nth_conjunct(mut thm: Thm, k: usize, n: usize) -> Result<Thm> {
    for _ in 0..k {
        thm = thm.and_elim_r()?;
    }
    if k + 1 < n { thm.and_elim_l() } else { Ok(thm) }
}

// ============================================================================
// Intro rules
// ============================================================================

/// A nullary congruence: `⊢ Subtype ctor ctor` (`idx`-th clause is `R ctor ctor`).
fn sub_nullary(idx: usize) -> Result<Thm> {
    let closed_t = closed_sub(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?;
    nth_conjunct(assumed, idx, N_CLAUSES)?
        .imp_intro(&closed_t)?
        .all_intro("R", r_ty())
}

/// `⊢ Subtype ⌜0⌝ ⌜0⌝`.
pub fn sub_empty() -> Result<Thm> {
    sub_nullary(0)
}
/// `⊢ Subtype ⌜1⌝ ⌜1⌝`.
pub fn sub_unit() -> Result<Thm> {
    sub_nullary(1)
}
/// `⊢ Subtype ⌜Xᵢ⌝ ⌜Xᵢ⌝`.
pub fn sub_base(i: Term) -> Result<Thm> {
    let closed_t = closed_sub(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?;
    nth_conjunct(assumed, 2, N_CLAUSES)?
        .all_elim(i)?
        .imp_intro(&closed_t)?
        .all_intro("R", r_ty())
}

/// A binary congruence: `⊢ Subtype a a' ⟹ Subtype b b' ⟹ Subtype (ctor a b) (ctor a' b')`,
/// where the `idx`-th clause is `∀a a' b b'. R a a' ⟹ R b b' ⟹ R (ctor a b) (ctor a' b')`.
fn sub_binary(idx: usize, a: Term, ap: Term, b: Term, bp: Term) -> Result<Thm> {
    let closed_t = closed_sub(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?; // {ClosedSub R} ⊢ ClosedSub R
    // R a a', R b b' from the two subtyping hypotheses.
    let r_aa = Thm::assume(subtype(&a, &ap)?)?
        .all_elim(r_var())?
        .imp_elim(assumed.clone())?; // {Subtype a a', ClosedSub R} ⊢ R a a'
    let r_bb = Thm::assume(subtype(&b, &bp)?)?
        .all_elim(r_var())?
        .imp_elim(assumed.clone())?; // ⊢ R b b'
    let r_ctor = nth_conjunct(assumed, idx, N_CLAUSES)?
        .all_elim(a.clone())?
        .all_elim(ap.clone())?
        .all_elim(b.clone())?
        .all_elim(bp.clone())?
        .imp_elim(r_aa)?
        .imp_elim(r_bb)?; // ⊢ R (ctor a b) (ctor a' b')
    r_ctor
        .imp_intro(&closed_t)?
        .all_intro("R", r_ty())?
        .imp_intro(&subtype(&b, &bp)?)?
        .imp_intro(&subtype(&a, &ap)?)
}

/// `⊢ Subtype a a' ⟹ Subtype b b' ⟹ Subtype ⌜a⊗b⌝ ⌜a'⊗b'⌝`.
pub fn sub_tensor(a: Term, ap: Term, b: Term, bp: Term) -> Result<Thm> {
    sub_binary(3, a, ap, b, bp)
}
/// `⊢ Subtype a a' ⟹ Subtype b b' ⟹ Subtype ⌜a+b⌝ ⌜a'+b'⌝`.
pub fn sub_sum(a: Term, ap: Term, b: Term, bp: Term) -> Result<Thm> {
    sub_binary(4, a, ap, b, bp)
}

// ============================================================================
// Rule induction
// ============================================================================

/// `pred a b` as the raw double application (a β-redex when `pred` is a λ).
fn pred_app(pred: &Term, a: &Term, b: &Term) -> Term {
    Term::app(Term::app(pred.clone(), a.clone()), b.clone())
}

/// **Rule induction over `Subtype`.** Given `pred : nat → nat → bool` closed
/// under the five congruence rules, conclude `⊢ ∀a b. Subtype a b ⟹ pred a b`
/// (`pred a b` the raw double application). Case proofs are stated over fresh
/// free variables; `sub_induction` does the `∀`-generalisation.
pub fn sub_induction(
    pred: &Term,
    case_empty: impl FnOnce() -> Result<Thm>,
    case_unit: impl FnOnce() -> Result<Thm>,
    case_base: impl FnOnce(&Term) -> Result<Thm>,
    case_tensor: impl FnOnce(&Term, &Term, &Term, &Term) -> Result<Thm>,
    case_sum: impl FnOnce(&Term, &Term, &Term, &Term) -> Result<Thm>,
) -> Result<Thm> {
    let (i, a, ap, b, bp) = (nvar("i"), nvar("a"), nvar("a'"), nvar("b"), nvar("b'"));

    let close4 = |t: Thm| -> Result<Thm> {
        t.all_intro("b'", nat_ty())?
            .all_intro("b", nat_ty())?
            .all_intro("a'", nat_ty())?
            .all_intro("a", nat_ty())
    };
    let clause_thms = [
        case_empty()?,
        case_unit()?,
        case_base(&i)?.all_intro("i", nat_ty())?,
        close4(case_tensor(&a, &ap, &b, &bp)?)?,
        close4(case_sum(&a, &ap, &b, &bp)?)?,
    ];
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("N_CLAUSES > 0");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    let closed_pred = acc; // ⊢ ClosedSub pred

    let (x, y) = (nvar("x"), nvar("y"));
    let sub = subtype(&x, &y)?;
    let pred_xy = Thm::assume(sub.clone())?
        .all_elim(pred.clone())?
        .imp_elim(closed_pred)?; // {Subtype x y} ⊢ pred x y
    pred_xy
        .imp_intro(&sub)?
        .all_intro("y", nat_ty())?
        .all_intro("x", nat_ty())
}

// ============================================================================
// The metatheorems
// ============================================================================

/// `⊢ ∀a b. Subtype a b ⟹ a = b` — on this fragment, subtyping *is* structural
/// equality (each congruence rule preserves it). By rule induction.
pub fn sub_eq() -> Result<Thm> {
    // pred = λa b. a = b
    let (a, b) = (nvar("a"), nvar("b"));
    let body = a.clone().equals(b.clone())?;
    let inner = Term::abs(nat_ty(), covalence_core::subst::close(&body, "b"));
    let pred = Term::abs(nat_ty(), covalence_core::subst::close(&inner, "a"));

    // congruence `pair tag (pair x (pair y 0))` from `x = x'`, `y = y'`.
    let cong_pair = |ex: Thm, ey: Thm| -> Result<Thm> {
        Thm::refl(crate::init::code::pair_const())?
            .mk_comb(ex)?
            .mk_comb(ey)
    };
    let cong_ctor = move |tag: u64, ea: Thm, eb: Thm| -> Result<Thm> {
        let inner0 = cong_pair(eb, Thm::refl(lit(0))?)?; // pair y 0 = pair y' 0
        let inner = cong_pair(ea, inner0)?; // pair x (pair y 0) = …
        cong_pair(Thm::refl(lit(tag))?, inner) // pair tag … = pair tag …
    };

    let nullary = |ctor: Term| -> Result<Thm> {
        beta_nf_expand(pred_app(&pred, &ctor, &ctor), Thm::refl(ctor.clone())?)
    };
    let binary = |tag: u64,
                  ctor: &dyn Fn(Term, Term) -> Term,
                  a: &Term,
                  ap: &Term,
                  b: &Term,
                  bp: &Term|
     -> Result<Thm> {
        let pa = pred_app(&pred, a, ap);
        let pb = pred_app(&pred, b, bp);
        let eq_a = beta_nf_concl(Thm::assume(pa.clone())?)?; // a = a'
        let eq_b = beta_nf_concl(Thm::assume(pb.clone())?)?; // b = b'
        let eq_ctor = cong_ctor(tag, eq_a, eq_b)?; // ctor a b = ctor a' b'
        beta_nf_expand(
            pred_app(
                &pred,
                &ctor(a.clone(), b.clone()),
                &ctor(ap.clone(), bp.clone()),
            ),
            eq_ctor,
        )?
        .imp_intro(&pb)?
        .imp_intro(&pa)
    };

    let thm = sub_induction(
        &pred,
        || nullary(ty_empty()),
        || nullary(ty_unit()),
        |i| nullary(ty_base(i.clone())),
        |a, ap, b, bp| binary(3, &ty_tensor, a, ap, b, bp),
        |a, ap, b, bp| binary(4, &ty_sum, a, ap, b, bp),
    )?;
    beta_nf_concl(thm) // ∀a b. Subtype a b ⟹ a = b
}

/// `⊢ ∀c. WfTyCode c ⟹ Subtype c c` — subtyping reflexivity, by induction on
/// the well-formedness of `c`.
pub fn sub_refl() -> Result<Thm> {
    // pred = λc. Subtype c c
    let c = nvar("c");
    let body = subtype(&c, &c)?;
    let pred = Term::abs(nat_ty(), covalence_core::subst::close(&body, "c"));

    let nullary = |ctor: Term, sub: Thm| -> Result<Thm> {
        beta_expand(&pred, ctor, sub) // (λc.Subtype c c) ctor
    };
    let binary = |ctor: &dyn Fn(Term, Term) -> Term,
                  sub_ctor: &dyn Fn(Term, Term, Term, Term) -> Result<Thm>,
                  l: &Term,
                  r: &Term|
     -> Result<Thm> {
        let prl = Term::app(pred.clone(), l.clone());
        let prr = Term::app(pred.clone(), r.clone());
        let s_ll = beta_reduce(Thm::assume(prl.clone())?)?; // Subtype l l
        let s_rr = beta_reduce(Thm::assume(prr.clone())?)?; // Subtype r r
        let s = sub_ctor(l.clone(), l.clone(), r.clone(), r.clone())?
            .imp_elim(s_ll)?
            .imp_elim(s_rr)?; // Subtype (ctor l r) (ctor l r)
        beta_expand(&pred, ctor(l.clone(), r.clone()), s)?
            .imp_intro(&prr)?
            .imp_intro(&prl)
    };

    let thm = wf_ty_induction(
        &pred,
        || nullary(ty_empty(), sub_empty()?),
        || nullary(ty_unit(), sub_unit()?),
        |i| nullary(ty_base(i.clone()), sub_base(i.clone())?),
        |l, r| binary(&ty_tensor, &sub_tensor, l, r),
        |l, r| binary(&ty_sum, &sub_sum, l, r),
    )?;
    beta_nf_concl(thm) // ∀c. WfTyCode c ⟹ Subtype c c
}

/// `⊢ ∀a b c. Subtype a b ⟹ Subtype b c ⟹ Subtype a c` — transitivity. From
/// [`sub_eq`], `a = b`; rewrite it into `Subtype b c`.
pub fn sub_trans() -> Result<Thm> {
    let (a, b, c) = (nvar("a"), nvar("b"), nvar("c"));
    let hab = Thm::assume(subtype(&a, &b)?)?; // Subtype a b
    let hbc = Thm::assume(subtype(&b, &c)?)?; // Subtype b c
    let a_eq_b = sub_eq()?
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .imp_elim(hab)?; // {Subtype a b} ⊢ a = b
    let sub_ac = hbc.rewrite(&a_eq_b.sym()?)?; // {Subtype a b, Subtype b c} ⊢ Subtype a c
    sub_ac
        .imp_intro(&subtype(&b, &c)?)?
        .imp_intro(&subtype(&a, &b)?)?
        .all_intro("c", nat_ty())?
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::lambda_ty::{wf_base, wf_empty, wf_tensor};

    /// Intro rules + the three metatheorems all replay to closed theorems.
    #[test]
    fn subtyping_theorems_are_closed() {
        let (l, r, i) = (nvar("l"), nvar("r"), nvar("i"));
        let thms: [(&str, Result<Thm>); 8] = [
            ("sub_empty", sub_empty()),
            ("sub_unit", sub_unit()),
            ("sub_base", sub_base(i)),
            (
                "sub_tensor",
                sub_tensor(l.clone(), l.clone(), r.clone(), r.clone()),
            ),
            (
                "sub_sum",
                sub_sum(l.clone(), l.clone(), r.clone(), r.clone()),
            ),
            ("sub_eq", sub_eq()),
            ("sub_refl", sub_refl()),
            ("sub_trans", sub_trans()),
        ];
        for (name, thm) in thms {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }

    /// Reflexivity applied: `WfTyCode ⌜X₀⊗1⌝ ⊢ Subtype ⌜X₀⊗1⌝ ⌜X₀⊗1⌝`, then
    /// transitivity composes it with itself.
    #[test]
    fn refl_and_trans_compose() {
        let t = ty_tensor(ty_base(lit(0)), ty_unit());
        // WfTyCode (X0 ⊗ 1)
        let wf_t = wf_tensor(ty_base(lit(0)), ty_unit())
            .and_then(|x| x.imp_elim(wf_base(lit(0))?))
            .and_then(|x| x.imp_elim(crate::init::lambda_ty::wf_unit()?))
            .expect("wf");
        let _ = wf_empty; // (kept available for richer compositions)
        let sub_tt = sub_refl()
            .and_then(|r| r.all_elim(t.clone()))
            .and_then(|r| r.imp_elim(wf_t))
            .expect("Subtype t t");
        assert!(sub_tt.hyps().is_empty());
        // trans: Subtype t t ⟹ Subtype t t ⟹ Subtype t t
        let composed = sub_trans()
            .and_then(|r| r.all_elim(t.clone()))
            .and_then(|r| r.all_elim(t.clone()))
            .and_then(|r| r.all_elim(t.clone()))
            .and_then(|r| r.imp_elim(sub_tt.clone()))
            .and_then(|r| r.imp_elim(sub_tt))
            .expect("trans compose");
        assert!(composed.hyps().is_empty());
    }
}
