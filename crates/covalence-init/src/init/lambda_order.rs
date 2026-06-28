//! # λ_iter richer subtyping — the order with bottom `0` and top `1`
//!
//! The structural *congruence* of [`lambda_sub`](crate::init::lambda_sub) is, on
//! this binder-free fragment, just equality (`sub_eq`). The genuine **subtyping
//! order** `<:` adds the two non-trivial cells of the bicartesian structure: `0`
//! is **initial** (empty is below everything) and `1` is **terminal** (everything
//! is below unit). It is a *new* impredicative relation (you cannot bolt rules
//! onto the fixed least-relation `Subtype`):
//!
//! ```text
//!     Order a b  :=  ∀R:nat→nat→bool. ClosedOrder R ⟹ R a b
//! ```
//!
//! where `ClosedOrder R` conjoins the five closure clauses
//!
//! ```text
//!   (∀a. WfTyCode a ⟹ R ⌜0⌝ a)            -- initial: 0 <: a
//!   (∀a. WfTyCode a ⟹ R a ⌜1⌝)            -- terminal: a <: 1
//!   (∀i. R ⌜Xᵢ⌝ ⌜Xᵢ⌝)                     -- reflexivity at base types
//!   (∀a a' b b'. R a a' ⟹ R b b' ⟹ R ⌜a⊗b⌝ ⌜a'⊗b'⌝)   -- covariant ⊗
//!   (∀a a' b b'. R a a' ⟹ R b b' ⟹ R ⌜a+b⌝ ⌜a'+b'⌝)   -- covariant +
//! ```
//!
//! Provided: the five [intro rules](ord_tensor), [rule induction](ord_induction),
//! and the metatheorems
//!
//! * [`subtype_to_order`] `⊢ ∀a b. Subtype a b ⟹ Order a b` — the congruence
//!   embeds into the order (so `Order` is reflexive on well-formed codes, etc.);
//! * [`ord_refl`] `⊢ ∀c. WfTyCode c ⟹ Order c c` — reflexivity, a corollary of
//!   the embedding and [`sub_refl`](crate::init::lambda_sub::sub_refl);
//! * [`ord_wf`] `⊢ ∀a b. Order a b ⟹ WfTyCode a ∧ WfTyCode b` — well-formedness
//!   preservation, by [rule induction](ord_induction).
//!
//! **Transitivity** `Order a b ⟹ Order b c ⟹ Order a c` needs genuine inversion
//! (generation) lemmas on `Order` — deferred, see `init/SKELETONS.md`.

use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::eq::{beta_nf_concl, beta_nf_expand};
use crate::init::ext::TermExt;
use crate::init::lambda_sub::{sub_induction, sub_refl};
use crate::init::lambda_ty::{
    ty_base, ty_empty, ty_sum, ty_tensor, ty_unit, wf_base, wf_empty, wf_sum, wf_tensor,
    wf_ty_code, wf_unit,
};

// ============================================================================
// Term helpers
// ============================================================================

fn nat_ty() -> Type {
    Type::nat()
}
fn bool_ty() -> Type {
    Type::bool()
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
/// `pred a b` as the raw double application (a β-redex when `pred` is a λ).
fn pred_app(pred: &Term, a: &Term, b: &Term) -> Term {
    Term::app(Term::app(pred.clone(), a.clone()), b.clone())
}

// ============================================================================
// `ClosedOrder R` and `Order`
// ============================================================================

/// Number of closure clauses.
const N_CLAUSES: usize = 5;

/// `ClosedOrder R` — the right-nested conjunction of the five closure clauses
/// (see the module docs).
fn closed_order(r: &Term) -> Result<Term> {
    let (i, a, ap, b, bp) = (nvar("i"), nvar("a"), nvar("a'"), nvar("b"), nvar("b'"));

    // initial: ∀a. WfTyCode a ⟹ R ⌜0⌝ a
    let c_init = wf_ty_code(&a)?
        .imp(rapp(r, &ty_empty(), &a))?
        .forall("a", nat_ty())?;
    // terminal: ∀a. WfTyCode a ⟹ R a ⌜1⌝
    let c_term = wf_ty_code(&a)?
        .imp(rapp(r, &a, &ty_unit()))?
        .forall("a", nat_ty())?;
    // reflexivity at base: ∀i. R ⌜Xᵢ⌝ ⌜Xᵢ⌝
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

    let clauses = [c_init, c_term, c_base, c_tensor, c_sum];
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter.next().expect("N_CLAUSES > 0");
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `Order a b := ∀R. ClosedOrder R ⟹ R a b`.
pub fn order(a: &Term, b: &Term) -> Result<Term> {
    closed_order(&r_var())?
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

/// `⊢ WfTyCode a ⟹ Order ⌜0⌝ a` — **initial**: `0` is below every well-formed
/// type (clause 0 is `∀a. WfTyCode a ⟹ R ⌜0⌝ a`).
pub fn ord_init(a: Term) -> Result<Thm> {
    let closed_t = closed_order(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?;
    let r_0a = nth_conjunct(assumed, 0, N_CLAUSES)?
        .all_elim(a.clone())?
        .imp_elim(Thm::assume(wf_ty_code(&a)?)?)?; // {ClosedOrder R, WfTyCode a} ⊢ R ⌜0⌝ a
    r_0a.imp_intro(&closed_t)?
        .all_intro("R", r_ty())?
        .imp_intro(&wf_ty_code(&a)?)
}

/// `⊢ WfTyCode a ⟹ Order a ⌜1⌝` — **terminal**: every well-formed type is below
/// `1` (clause 1 is `∀a. WfTyCode a ⟹ R a ⌜1⌝`).
pub fn ord_term(a: Term) -> Result<Thm> {
    let closed_t = closed_order(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?;
    let r_a1 = nth_conjunct(assumed, 1, N_CLAUSES)?
        .all_elim(a.clone())?
        .imp_elim(Thm::assume(wf_ty_code(&a)?)?)?; // {ClosedOrder R, WfTyCode a} ⊢ R a ⌜1⌝
    r_a1.imp_intro(&closed_t)?
        .all_intro("R", r_ty())?
        .imp_intro(&wf_ty_code(&a)?)
}

/// `⊢ Order ⌜Xᵢ⌝ ⌜Xᵢ⌝` — reflexivity at base types (clause 2).
pub fn ord_base(i: Term) -> Result<Thm> {
    let closed_t = closed_order(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?;
    nth_conjunct(assumed, 2, N_CLAUSES)?
        .all_elim(i)?
        .imp_intro(&closed_t)?
        .all_intro("R", r_ty())
}

/// A binary congruence (`idx`-th clause is `∀a a' b b'. R a a' ⟹ R b b' ⟹
/// R (ctor a b) (ctor a' b')`).
fn ord_binary(idx: usize, a: Term, ap: Term, b: Term, bp: Term) -> Result<Thm> {
    let closed_t = closed_order(&r_var())?;
    let assumed = Thm::assume(closed_t.clone())?; // {ClosedOrder R} ⊢ ClosedOrder R
    let r_aa = Thm::assume(order(&a, &ap)?)?
        .all_elim(r_var())?
        .imp_elim(assumed.clone())?; // {Order a a', ClosedOrder R} ⊢ R a a'
    let r_bb = Thm::assume(order(&b, &bp)?)?
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
        .imp_intro(&order(&b, &bp)?)?
        .imp_intro(&order(&a, &ap)?)
}

/// `⊢ Order a a' ⟹ Order b b' ⟹ Order ⌜a⊗b⌝ ⌜a'⊗b'⌝` — covariant product.
pub fn ord_tensor(a: Term, ap: Term, b: Term, bp: Term) -> Result<Thm> {
    ord_binary(3, a, ap, b, bp)
}
/// `⊢ Order a a' ⟹ Order b b' ⟹ Order ⌜a+b⌝ ⌜a'+b'⌝` — covariant sum.
pub fn ord_sum(a: Term, ap: Term, b: Term, bp: Term) -> Result<Thm> {
    ord_binary(4, a, ap, b, bp)
}

// ============================================================================
// Rule induction
// ============================================================================

/// **Rule induction over `Order`.** Given `pred : nat → nat → bool` closed under
/// the five rules, conclude `⊢ ∀a b. Order a b ⟹ pred a b` (`pred a b` the raw
/// double application). The `init`/`term` case proofs take the free index `a`
/// and must conclude `⊢ WfTyCode a ⟹ pred …` (matching their closure clauses);
/// the others mirror [`sub_induction`](crate::init::lambda_sub::sub_induction).
pub fn ord_induction(
    pred: &Term,
    case_init: impl FnOnce(&Term) -> Result<Thm>,
    case_term: impl FnOnce(&Term) -> Result<Thm>,
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
        case_init(&a)?.all_intro("a", nat_ty())?,
        case_term(&a)?.all_intro("a", nat_ty())?,
        case_base(&i)?.all_intro("i", nat_ty())?,
        close4(case_tensor(&a, &ap, &b, &bp)?)?,
        close4(case_sum(&a, &ap, &b, &bp)?)?,
    ];
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("N_CLAUSES > 0");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    let closed_pred = acc; // ⊢ ClosedOrder pred

    let (x, y) = (nvar("x"), nvar("y"));
    let ord = order(&x, &y)?;
    let pred_xy = Thm::assume(ord.clone())?
        .all_elim(pred.clone())?
        .imp_elim(closed_pred)?; // {Order x y} ⊢ pred x y
    pred_xy
        .imp_intro(&ord)?
        .all_intro("y", nat_ty())?
        .all_intro("x", nat_ty())
}

// ============================================================================
// The metatheorems
// ============================================================================

/// `⊢ ∀a b. Subtype a b ⟹ Order a b` — the structural congruence embeds into the
/// richer order. By rule induction over the `Subtype` derivation, mapping each
/// congruence rule to the corresponding `Order` rule.
pub fn subtype_to_order() -> Result<Thm> {
    // pred = λa b. Order a b
    let (a, b) = (nvar("a"), nvar("b"));
    let body = order(&a, &b)?;
    let inner = Term::abs(nat_ty(), subst::close(&body, "b"));
    let pred = Term::abs(nat_ty(), subst::close(&inner, "a"));

    let nullary = |ctor: Term, ord_cc: Thm| -> Result<Thm> {
        beta_nf_expand(pred_app(&pred, &ctor, &ctor), ord_cc)
    };
    let binary = |rule: Thm,
                  ctor: &dyn Fn(Term, Term) -> Term,
                  a: &Term,
                  ap: &Term,
                  b: &Term,
                  bp: &Term|
     -> Result<Thm> {
        let pa = pred_app(&pred, a, ap);
        let pb = pred_app(&pred, b, bp);
        let ord_a = beta_nf_concl(Thm::assume(pa.clone())?)?; // Order a a'
        let ord_b = beta_nf_concl(Thm::assume(pb.clone())?)?; // Order b b'
        let ord_ctor = rule.imp_elim(ord_a)?.imp_elim(ord_b)?; // Order (ctor a b) (ctor a' b')
        beta_nf_expand(
            pred_app(
                &pred,
                &ctor(a.clone(), b.clone()),
                &ctor(ap.clone(), bp.clone()),
            ),
            ord_ctor,
        )?
        .imp_intro(&pb)?
        .imp_intro(&pa)
    };

    let thm = sub_induction(
        &pred,
        || nullary(ty_empty(), ord_init(ty_empty())?.imp_elim(wf_empty()?)?),
        || nullary(ty_unit(), ord_term(ty_unit())?.imp_elim(wf_unit()?)?),
        |i| nullary(ty_base(i.clone()), ord_base(i.clone())?),
        |a, ap, b, bp| {
            binary(
                ord_tensor(a.clone(), ap.clone(), b.clone(), bp.clone())?,
                &ty_tensor,
                a,
                ap,
                b,
                bp,
            )
        },
        |a, ap, b, bp| {
            binary(
                ord_sum(a.clone(), ap.clone(), b.clone(), bp.clone())?,
                &ty_sum,
                a,
                ap,
                b,
                bp,
            )
        },
    )?;
    beta_nf_concl(thm) // ∀a b. Subtype a b ⟹ Order a b
}

/// `⊢ ∀c. WfTyCode c ⟹ Order c c` — reflexivity, a corollary of
/// [`subtype_to_order`] and [`sub_refl`](crate::init::lambda_sub::sub_refl).
pub fn ord_refl() -> Result<Thm> {
    let c = nvar("c");
    let wf = Thm::assume(wf_ty_code(&c)?)?;
    let sub_cc = sub_refl()?.all_elim(c.clone())?.imp_elim(wf)?; // {WfTyCode c} ⊢ Subtype c c
    subtype_to_order()?
        .all_elim(c.clone())?
        .all_elim(c.clone())?
        .imp_elim(sub_cc)? // {WfTyCode c} ⊢ Order c c
        .imp_intro(&wf_ty_code(&c)?)?
        .all_intro("c", nat_ty())
}

/// `⊢ ∀a b. Order a b ⟹ WfTyCode a ∧ WfTyCode b` — every order-related pair is
/// well-formed. By rule induction over the `Order` derivation.
pub fn ord_wf() -> Result<Thm> {
    // pred = λa b. WfTyCode a ∧ WfTyCode b
    let (a, b) = (nvar("a"), nvar("b"));
    let body = wf_ty_code(&a)?.and(wf_ty_code(&b)?)?;
    let inner = Term::abs(nat_ty(), subst::close(&body, "b"));
    let pred = Term::abs(nat_ty(), subst::close(&inner, "a"));

    // init: WfTyCode a ⟹ pred ⌜0⌝ a   (⌜0⌝ well-formed by `wf_empty`).
    let case_init = |a: &Term| -> Result<Thm> {
        let wf_a = Thm::assume(wf_ty_code(a)?)?;
        beta_nf_expand(
            pred_app(&pred, &ty_empty(), a),
            wf_empty()?.and_intro(wf_a)?,
        )?
        .imp_intro(&wf_ty_code(a)?)
    };
    // term: WfTyCode a ⟹ pred a ⌜1⌝.
    let case_term = |a: &Term| -> Result<Thm> {
        let wf_a = Thm::assume(wf_ty_code(a)?)?;
        beta_nf_expand(pred_app(&pred, a, &ty_unit()), wf_a.and_intro(wf_unit()?)?)?
            .imp_intro(&wf_ty_code(a)?)
    };
    let case_base = |i: &Term| -> Result<Thm> {
        let pair = wf_base(i.clone())?.and_intro(wf_base(i.clone())?)?;
        beta_nf_expand(
            pred_app(&pred, &ty_base(i.clone()), &ty_base(i.clone())),
            pair,
        )
    };
    let case_binary = |wf_ctor: fn(Term, Term) -> Result<Thm>,
                       ctor: &dyn Fn(Term, Term) -> Term,
                       a: &Term,
                       ap: &Term,
                       b: &Term,
                       bp: &Term|
     -> Result<Thm> {
        let pa = pred_app(&pred, a, ap);
        let pb = pred_app(&pred, b, bp);
        let ha = beta_nf_concl(Thm::assume(pa.clone())?)?; // WfTyCode a ∧ WfTyCode a'
        let hb = beta_nf_concl(Thm::assume(pb.clone())?)?; // WfTyCode b ∧ WfTyCode b'
        let wf_l = wf_ctor(a.clone(), b.clone())?
            .imp_elim(ha.clone().and_elim_l()?)?
            .imp_elim(hb.clone().and_elim_l()?)?; // WfTyCode (ctor a b)
        let wf_r = wf_ctor(ap.clone(), bp.clone())?
            .imp_elim(ha.and_elim_r()?)?
            .imp_elim(hb.and_elim_r()?)?; // WfTyCode (ctor a' b')
        beta_nf_expand(
            pred_app(
                &pred,
                &ctor(a.clone(), b.clone()),
                &ctor(ap.clone(), bp.clone()),
            ),
            wf_l.and_intro(wf_r)?,
        )?
        .imp_intro(&pb)?
        .imp_intro(&pa)
    };

    let thm = ord_induction(
        &pred,
        case_init,
        case_term,
        case_base,
        |a, ap, b, bp| case_binary(wf_tensor, &ty_tensor, a, ap, b, bp),
        |a, ap, b, bp| case_binary(wf_sum, &ty_sum, a, ap, b, bp),
    )?;
    beta_nf_concl(thm) // ∀a b. Order a b ⟹ WfTyCode a ∧ WfTyCode b
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(n: u64) -> Term {
        Term::nat_lit(n)
    }

    /// Intro rules + the three metatheorems all replay to closed theorems.
    #[test]
    fn order_theorems_are_closed() {
        let (l, r, i) = (nvar("l"), nvar("r"), nvar("i"));
        let thms: [(&str, Result<Thm>); 8] = [
            ("ord_init", ord_init(l.clone())),
            ("ord_term", ord_term(l.clone())),
            ("ord_base", ord_base(i)),
            (
                "ord_tensor",
                ord_tensor(l.clone(), l.clone(), r.clone(), r.clone()),
            ),
            (
                "ord_sum",
                ord_sum(l.clone(), l.clone(), r.clone(), r.clone()),
            ),
            ("subtype_to_order", subtype_to_order()),
            ("ord_refl", ord_refl()),
            ("ord_wf", ord_wf()),
        ];
        for (name, thm) in thms {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }

    /// The genuinely-richer cells: bottom below a compound, compound below top.
    /// `t = X₀ ⊗ 1`; derive `Order ⌜0⌝ t` and `Order t ⌜1⌝`.
    #[test]
    fn bottom_and_top() {
        let t = ty_tensor(ty_base(lit(0)), ty_unit());
        let wf_t = wf_tensor(ty_base(lit(0)), ty_unit())
            .and_then(|x| x.imp_elim(wf_base(lit(0))?))
            .and_then(|x| x.imp_elim(wf_unit()?))
            .expect("WfTyCode (X0 ⊗ 1)");

        // 0 <: t   (initial)
        let bot = ord_init(t.clone())
            .and_then(|x| x.imp_elim(wf_t.clone()))
            .expect("Order 0 t");
        assert!(bot.hyps().is_empty(), "Order 0 t should be closed");

        // t <: 1   (terminal)
        let top = ord_term(t.clone())
            .and_then(|x| x.imp_elim(wf_t.clone()))
            .expect("Order t 1");
        assert!(top.hyps().is_empty(), "Order t 1 should be closed");

        // well-formedness preservation recovers both ends of `0 <: t`.
        let parts = ord_wf()
            .and_then(|x| x.all_elim(ty_empty()))
            .and_then(|x| x.all_elim(t.clone()))
            .and_then(|x| x.imp_elim(bot))
            .expect("WfTyCode 0 ∧ WfTyCode t");
        assert!(parts.hyps().is_empty());
        parts.and_elim_r().expect("WfTyCode t");
    }
}
