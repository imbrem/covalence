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
//!   preservation, by [rule induction](ord_induction);
//! * [`ord_trans`] `⊢ ∀a b c. Order a b ⟹ Order b c ⟹ Order a c` —
//!   **transitivity**; and
//! * [`ord_antisym`] `⊢ ∀a b. Order a b ⟹ Order b a ⟹ a = b` —
//!   **antisymmetry**. With [`ord_refl`], `Order` is a genuine **partial order**.
//!
//! These rest on the **generation/inversion lemmas** [`inv_unit`]
//! (`Order ⌜1⌝ c ⟹ c = ⌜1⌝`, `1` maximal), [`inv_empty`] (`Order c ⌜0⌝ ⟹
//! c = ⌜0⌝`, `0` minimal), [`inv_tensor`], and [`inv_sum`] (a binary code is
//! below `c` only when `c = ⌜1⌝` or `c` is the matching binary with covariantly
//! related components). The binary inversions are stated with the **component
//! extractors** `ty_arg1`/`ty_arg2` (built on the `code_proj` projections)
//! instead of existentials, so the use-sites are plain rewrites.

use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::code::{pair, pair_const};
use crate::init::code_proj::{pi2_explicit, pi2_pair, v2_explicit, v2_pair_applied};
use crate::init::eq::{beta_nf_concl, beta_nf_expand};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::lambda_sub::{sub_induction, sub_refl};
use crate::init::lambda_ty::{
    ty_base, ty_code_distinct, ty_empty, ty_sum, ty_tensor, ty_unit, wf_base, wf_empty, wf_sum,
    wf_tensor, wf_ty_code, wf_unit,
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

// ============================================================================
// Component extractors — `Order` inversion without existentials
//
// A binary code is `pair tag (pair l (pair r 0))`, so its two arguments are
// recovered by the *projections* of `code_proj`:  `ty_arg1 c = π₁(π₂ c)` and
// `ty_arg2 c = π₁(π₂(π₂ c))`.  Stating the inversion lemmas with these explicit
// extractors (rather than `∃`) makes the transitivity use-site a plain rewrite.
// This is the first genuine *use* of the projection round-trips.
// ============================================================================

/// `π₂ t` — the second pairing projection, applied.
fn pi2_app(t: Term) -> Result<Term> {
    Ok(Term::app(pi2_explicit()?, t))
}
/// `π₁ t` (the 2-adic valuation), applied.
fn v2_app(t: Term) -> Result<Term> {
    Ok(Term::app(v2_explicit()?, t))
}
/// `ty_arg1 c = π₁(π₂ c)` — the first argument of a binary type code.
fn ty_arg1(c: &Term) -> Result<Term> {
    v2_app(pi2_app(c.clone())?)
}
/// `ty_arg2 c = π₁(π₂(π₂ c))` — the second argument of a binary type code.
fn ty_arg2(c: &Term) -> Result<Term> {
    v2_app(pi2_app(pi2_app(c.clone())?)?)
}

/// `⊢ ty_arg1 (pair t (pair p rest)) = p` — projects the first argument out of
/// any binary code (independent of the tag and the tail).
fn ty_arg1_eq(t: &Term, p: &Term, rest: &Term) -> Result<Thm> {
    let inner = pair(p.clone(), rest.clone()); // pair p rest
    let pi2c = pi2_pair()?.all_elim(t.clone())?.all_elim(inner.clone())?; // π₂(pair t inner) = inner
    let v2p = v2_pair_applied(p, rest)?; // app v2_explicit (pair p rest) = p
    pi2c.cong_arg(v2_explicit()?)?.trans(v2p) // π₁(π₂ c) = π₁ inner = p
}

/// `⊢ ty_arg2 (pair t (pair p (pair q rest))) = q`.
fn ty_arg2_eq(t: &Term, p: &Term, q: &Term, rest: &Term) -> Result<Thm> {
    let inner2 = pair(q.clone(), rest.clone()); // pair q rest
    let inner1 = pair(p.clone(), inner2.clone()); // pair p (pair q rest)
    let pi2c = pi2_pair()?.all_elim(t.clone())?.all_elim(inner1.clone())?; // π₂(pair t inner1) = inner1
    let pi2inner1 = pi2_pair()?.all_elim(p.clone())?.all_elim(inner2.clone())?; // π₂(pair p inner2) = inner2
    let v2q = v2_pair_applied(q, rest)?; // app v2_explicit (pair q rest) = q
    pi2c.cong_arg(pi2_explicit()?)? // π₂(π₂ c) = π₂ inner1
        .trans(pi2inner1)? // = inner2
        .cong_arg(v2_explicit()?)? // π₁(π₂(π₂ c)) = π₁ inner2
        .trans(v2q) // = q
}

/// `⊢ ty_arg1 (ty_tensor p q) = p` / `… (ty_sum p q) = p` (tag-agnostic).
fn ty_arg1_ctor(tag: u64, p: &Term, q: &Term) -> Result<Thm> {
    ty_arg1_eq(&lit(tag), p, &pair(q.clone(), lit(0)))
}
/// `⊢ ty_arg2 (ty_tensor p q) = q` / `… (ty_sum p q) = q`.
fn ty_arg2_ctor(tag: u64, p: &Term, q: &Term) -> Result<Thm> {
    ty_arg2_eq(&lit(tag), p, q, &lit(0))
}

// ============================================================================
// `Order` inversion (generation) lemmas
// ============================================================================

/// `⊢ ∀c. Order ⌜1⌝ c ⟹ c = ⌜1⌝` — `1` is **maximal**: nothing is strictly
/// above it, so `1 <: c` forces `c = 1`. By [rule induction](ord_induction) with
/// `pred a b := (a = ⌜1⌝) ⟹ (b = ⌜1⌝)`; the only non-vacuous case is `term`,
/// where the conclusion `1 = 1` is reflexivity.
pub fn inv_unit() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let body = a
        .clone()
        .equals(ty_unit())?
        .imp(b.clone().equals(ty_unit())?)?;
    let inner = Term::abs(nat_ty(), subst::close(&body, "b"));
    let pred = Term::abs(nat_ty(), subst::close(&inner, "a"));

    // `(x = 1) ⟹ (y = 1)` discharged ex falso when `x ≠ 1`.
    let vacuous = |x: &Term, y: &Term| -> Result<Thm> {
        let h = x.clone().equals(ty_unit())?;
        let imp = ty_code_distinct(x, &ty_unit())?
            .not_elim(Thm::assume(h.clone())?)? // {x=1} ⊢ F
            .false_elim(y.clone().equals(ty_unit())?)?
            .imp_intro(&h)?; // (x=1) ⟹ (y=1)
        beta_nf_expand(pred_app(&pred, x, y), imp)
    };

    let ind = ord_induction(
        &pred,
        |a| vacuous(&ty_empty(), a)?.imp_intro(&wf_ty_code(a)?),
        |a| {
            let imp = Thm::refl(ty_unit())?.imp_intro(&a.clone().equals(ty_unit())?)?; // (a=1)⟹(1=1)
            beta_nf_expand(pred_app(&pred, a, &ty_unit()), imp)?.imp_intro(&wf_ty_code(a)?)
        },
        |i| {
            let xi = ty_base(i.clone());
            let h = xi.clone().equals(ty_unit())?;
            beta_nf_expand(
                pred_app(&pred, &xi, &xi),
                Thm::assume(h.clone())?.imp_intro(&h)?, // (Xi=1)⟹(Xi=1)
            )
        },
        |a, ap, b, bp| {
            vacuous(
                &ty_tensor(a.clone(), b.clone()),
                &ty_tensor(ap.clone(), bp.clone()),
            )?
            .imp_intro(&pred_app(&pred, b, bp))?
            .imp_intro(&pred_app(&pred, a, ap))
        },
        |a, ap, b, bp| {
            vacuous(
                &ty_sum(a.clone(), b.clone()),
                &ty_sum(ap.clone(), bp.clone()),
            )?
            .imp_intro(&pred_app(&pred, b, bp))?
            .imp_intro(&pred_app(&pred, a, ap))
        },
    )?;

    // Specialise at `a := 1`, discharge `1 = 1`.
    let c = nvar("c");
    let ord1c = order(&ty_unit(), &c)?;
    let pred_1c = ind
        .all_elim(ty_unit())?
        .all_elim(c.clone())?
        .imp_elim(Thm::assume(ord1c.clone())?)?; // {Order 1 c} ⊢ pred 1 c
    beta_nf_concl(pred_1c)? // (1=1) ⟹ (c=1)
        .imp_elim(Thm::refl(ty_unit())?)? // {Order 1 c} ⊢ c = 1
        .imp_intro(&ord1c)?
        .all_intro("c", nat_ty())
}

// ----------------------------------------------------------------------------
// Binary inversion — shared engine for `inv_tensor` / `inv_sum`.
//
// The strengthened predicate carries projection redexes (`ty_arg1 a = π₁(π₂ a)`),
// so the `beta_nf` bridges would wrongly fire them. `apply2_*` reduce *only* the
// two predicate-application redexes, leaving the projections intact.
// ----------------------------------------------------------------------------

/// `⊢ pred x y = body[x,y]` reducing **only** the two spine redexes of the
/// double application `(λa b. body) x y` (not the projection redexes inside).
fn apply2_eq(pred: &Term, x: &Term, y: &Term) -> Result<Thm> {
    let s1 = Thm::beta_conv(Term::app(pred.clone(), x.clone()))? // (λa b.body) x = λb.body[x]
        .cong_fn(y.clone())?; // (λa b.body) x y = (λb.body[x]) y
    let mid = s1.concl().as_eq().expect("eq").1.clone();
    s1.trans(Thm::beta_conv(mid)?) // = body[x,y]
}
/// `⊢ pred x y` from `⊢ body[x,y]` (spine-only β-expansion).
fn apply2_intro(pred: &Term, x: &Term, y: &Term, body: Thm) -> Result<Thm> {
    apply2_eq(pred, x, y)?.sym()?.eq_mp(body)
}
/// `⊢ body[x,y]` from `⊢ pred x y` (spine-only β-reduction).
fn apply2_elim(pred: &Term, x: &Term, y: &Term, papp: Thm) -> Result<Thm> {
    apply2_eq(pred, x, y)?.eq_mp(papp)
}

/// `e1 : x = x'`, `e2 : y = y'`  ⟹  `⊢ ctor x y = ctor x' y'`, where
/// `ctor x y = pair tag (pair x (pair y 0))` (nested-pair congruence).
fn ctor_cong(tag: u64, e1: Thm, e2: Thm) -> Result<Thm> {
    let py = e2.cong_arg(pair_const())?.cong_fn(lit(0))?; // pair y 0 = pair y' 0
    let px = e1.cong_arg(pair_const())?.cong_app(py)?; // pair x (pair y 0) = pair x' (pair y' 0)
    px.cong_arg(Term::app(pair_const(), lit(tag))) // ctor x y = ctor x' y'
}

/// `⊢ ctor x y = ctor (ty_arg1 (ctor x y)) (ty_arg2 (ctor x y))` — a binary code
/// reconstructs from its own extracted components.
fn recon_eq(tag: u64, x: &Term, y: &Term) -> Result<Thm> {
    ctor_cong(
        tag,
        ty_arg1_ctor(tag, x, y)?.sym()?, // x = ty_arg1 (ctor x y)
        ty_arg2_ctor(tag, x, y)?.sym()?, // y = ty_arg2 (ctor x y)
    )
}

/// The non-`1` disjunct of the inversion: `b = ctor (ty_arg1 b) (ty_arg2 b) ∧
/// Order (ty_arg1 a) (ty_arg1 b) ∧ Order (ty_arg2 a) (ty_arg2 b)`.
fn disj_right(ctor: fn(Term, Term) -> Term, a: &Term, b: &Term) -> Result<Term> {
    let (a1, a2) = (ty_arg1(a)?, ty_arg2(a)?);
    let (b1, b2) = (ty_arg1(b)?, ty_arg2(b)?);
    let recon = b.clone().equals(ctor(b1.clone(), b2.clone()))?;
    let orders = order(&a1, &b1)?.and(order(&a2, &b2)?)?;
    recon.and(orders)
}
/// `b = ⌜1⌝ ∨ disj_right`.
fn disjunction(ctor: fn(Term, Term) -> Term, a: &Term, b: &Term) -> Result<Term> {
    b.clone().equals(ty_unit())?.or(disj_right(ctor, a, b)?)
}
/// `(a = ctor (ty_arg1 a) (ty_arg2 a)) ⟹ disjunction(a, b)` — the inversion
/// clause (the antecedent is the "`a` is a `ctor`" guard, false off-shape).
fn inv_clause(ctor: fn(Term, Term) -> Term, a: &Term, b: &Term) -> Result<Term> {
    let isbin = a.clone().equals(ctor(ty_arg1(a)?, ty_arg2(a)?))?;
    isbin.imp(disjunction(ctor, a, b)?)
}

/// Shared engine: `⊢ ∀a b c. Order (ctor a b) c ⟹ disjunction(ctor a b, c)`.
fn inv_binary(target_tag: u64, ctor: fn(Term, Term) -> Term) -> Result<Thm> {
    // pred a b := Order a b ∧ inv_clause(a, b)
    let (a, b) = (nvar("a"), nvar("b"));
    let body = order(&a, &b)?.and(inv_clause(ctor, &a, &b)?)?;
    let pred = Term::abs(
        nat_ty(),
        subst::close(&Term::abs(nat_ty(), subst::close(&body, "b")), "a"),
    );

    // The inversion clause, discharged vacuously when `a_code`'s tag ≠ target.
    let vacuous_clause = |a_code: &Term, b_code: &Term| -> Result<Thm> {
        let isbin = a_code
            .clone()
            .equals(ctor(ty_arg1(a_code)?, ty_arg2(a_code)?))?;
        ty_code_distinct(a_code, &ctor(ty_arg1(a_code)?, ty_arg2(a_code)?))?
            .not_elim(Thm::assume(isbin.clone())?)? // {isbin} ⊢ F
            .false_elim(disjunction(ctor, a_code, b_code)?)?
            .imp_intro(&isbin) // isbin ⟹ disjunction
    };

    // A binary case (`this_tag`/`this_ctor`/`this_rule`); matches the target iff
    // the tags agree.
    let binary_case = |this_tag: u64,
                       this_ctor: fn(Term, Term) -> Term,
                       this_rule: fn(Term, Term, Term, Term) -> Result<Thm>,
                       a: &Term,
                       ap: &Term,
                       b: &Term,
                       bp: &Term|
     -> Result<Thm> {
        let (pa, pb) = (pred_app(&pred, a, ap), pred_app(&pred, b, bp));
        let ord_a = apply2_elim(&pred, a, ap, Thm::assume(pa.clone())?)?.and_elim_l()?; // Order a ap
        let ord_b = apply2_elim(&pred, b, bp, Thm::assume(pb.clone())?)?.and_elim_l()?; // Order b bp
        let lhs = this_ctor(a.clone(), b.clone());
        let rhs = this_ctor(ap.clone(), bp.clone());
        let ord_lr = this_rule(a.clone(), ap.clone(), b.clone(), bp.clone())?
            .imp_elim(ord_a.clone())?
            .imp_elim(ord_b.clone())?; // Order (this_ctor a b) (this_ctor ap bp)
        let clause = if this_tag == target_tag {
            // matching: prove the right disjunct from the two sub-derivations.
            let isbin = lhs.clone().equals(ctor(ty_arg1(&lhs)?, ty_arg2(&lhs)?))?;
            let recon = recon_eq(this_tag, ap, bp)?; // rhs = ctor(ty_arg1 rhs)(ty_arg2 rhs)
            // Order (ty_arg1 lhs)(ty_arg1 rhs)  from  Order a ap.
            let o1 = ord_a
                .rewrite(&ty_arg1_ctor(this_tag, a, b)?.sym()?)? // a → ty_arg1 lhs
                .rewrite(&ty_arg1_ctor(this_tag, ap, bp)?.sym()?)?; // ap → ty_arg1 rhs
            let o2 = ord_b
                .rewrite(&ty_arg2_ctor(this_tag, a, b)?.sym()?)?
                .rewrite(&ty_arg2_ctor(this_tag, ap, bp)?.sym()?)?;
            let right = recon.and_intro(o1.and_intro(o2)?)?; // disj_right(lhs, rhs)
            right
                .or_intro_r(rhs.clone().equals(ty_unit())?)? // (rhs=1) ∨ disj_right
                .imp_intro(&isbin)
        } else {
            vacuous_clause(&lhs, &rhs)
        };
        apply2_intro(&pred, &lhs, &rhs, ord_lr.and_intro(clause?)?)?
            .imp_intro(&pb)?
            .imp_intro(&pa)
    };

    let ind = ord_induction(
        &pred,
        |a| {
            let wfa = wf_ty_code(a)?;
            let o = ord_init(a.clone())?.imp_elim(Thm::assume(wfa.clone())?)?;
            apply2_intro(
                &pred,
                &ty_empty(),
                a,
                o.and_intro(vacuous_clause(&ty_empty(), a)?)?,
            )?
            .imp_intro(&wfa)
        },
        |a| {
            let wfa = wf_ty_code(a)?;
            let o = ord_term(a.clone())?.imp_elim(Thm::assume(wfa.clone())?)?;
            // inv_clause(a, 1): the left (`1 = 1`) disjunct, regardless of `a`.
            let ante = a.clone().equals(ctor(ty_arg1(a)?, ty_arg2(a)?))?;
            let disj = Thm::refl(ty_unit())?.or_intro_l(disj_right(ctor, a, &ty_unit())?)?;
            let clause = disj.imp_intro(&ante)?;
            apply2_intro(&pred, a, &ty_unit(), o.and_intro(clause)?)?.imp_intro(&wfa)
        },
        |i| {
            let xi = ty_base(i.clone());
            let body = ord_base(i.clone())?.and_intro(vacuous_clause(&xi, &xi)?)?;
            apply2_intro(&pred, &xi, &xi, body)
        },
        |a, ap, b, bp| binary_case(3, ty_tensor, ord_tensor, a, ap, b, bp),
        |a, ap, b, bp| binary_case(4, ty_sum, ord_sum, a, ap, b, bp),
    )?;

    // Extract: instantiate `a := ctor x y`, discharge the (true) `isbin` guard.
    let (x, y, c) = (nvar("x"), nvar("y"), nvar("c"));
    let lhs = ctor(x.clone(), y.clone());
    let ord_lc = order(&lhs, &c)?;
    let pred_lc = ind
        .all_elim(lhs.clone())?
        .all_elim(c.clone())?
        .imp_elim(Thm::assume(ord_lc.clone())?)?; // {Order (ctor x y) c} ⊢ pred (ctor x y) c
    apply2_elim(&pred, &lhs, &c, pred_lc)?
        .and_elim_r()? // inv_clause(ctor x y, c)
        .imp_elim(recon_eq(target_tag, &x, &y)?)? // discharge isbin → disjunction
        .imp_intro(&ord_lc)?
        .all_intro("c", nat_ty())?
        .all_intro("y", nat_ty())?
        .all_intro("x", nat_ty())
}

/// `⊢ ∀a b c. Order ⌜a⊗b⌝ c ⟹ (c = ⌜1⌝ ∨ (c = ⌜(ty_arg1 c)⊗(ty_arg2 c)⌝ ∧
/// Order a (ty_arg1 c) ∧ Order b (ty_arg2 c)))` — tensor generation.
pub fn inv_tensor() -> Result<Thm> {
    inv_binary(3, ty_tensor)
}
/// Sum generation (analogue of [`inv_tensor`]).
pub fn inv_sum() -> Result<Thm> {
    inv_binary(4, ty_sum)
}

// ----------------------------------------------------------------------------
// Transitivity
// ----------------------------------------------------------------------------

/// `⊢ ∀a u v. (u = v) ⟹ Order a u ⟹ Order a v` — `Order` respects equality in
/// its right argument. Safe because `u` is a *free variable* (it occurs only in
/// the `R a u` slot, never inside `ClosedOrder`'s `ty_empty`/`ty_unit`).
fn order_resp_r() -> Result<Thm> {
    let (a, u, v) = (nvar("a"), nvar("u"), nvar("v"));
    let huv = u.clone().equals(v.clone())?;
    Thm::assume(order(&a, &u)?)?
        .rewrite(&Thm::assume(huv.clone())?)? // Order a u → Order a v
        .imp_intro(&order(&a, &u)?)?
        .imp_intro(&huv)?
        .all_intro("v", nat_ty())?
        .all_intro("u", nat_ty())?
        .all_intro("a", nat_ty())
}

/// `⊢ Order x v` from `eq : u = v` and `oxu : Order x u`.
fn transport_r(x: &Term, u: &Term, v: &Term, eq: Thm, oxu: Thm) -> Result<Thm> {
    order_resp_r()?
        .all_elim(x.clone())?
        .all_elim(u.clone())?
        .all_elim(v.clone())?
        .imp_elim(eq)?
        .imp_elim(oxu)
}

/// `⊢ WfTyCode x` from `⊢ Order x y` (left component, via [`ord_wf`]).
fn wf_left(x: &Term, y: &Term, oxy: Thm) -> Result<Thm> {
    ord_wf()?
        .all_elim(x.clone())?
        .all_elim(y.clone())?
        .imp_elim(oxy)?
        .and_elim_l()
}

/// `⊢ ∀a b c. Order a b ⟹ Order b c ⟹ Order a c` — **transitivity**, by rule
/// induction on the first derivation with the strengthened motive
/// `pred a b := Order a b ∧ (∀c. Order b c ⟹ Order a c)`. The covariant cases
/// invert the middle relation ([`inv_tensor`]/[`inv_sum`]); the `term` case uses
/// [`inv_unit`]; `init`/`base` are direct.
pub fn ord_trans() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let cc = nvar("c");
    let trans_part = order(&b, &cc)?
        .imp(order(&a, &cc)?)?
        .forall("c", nat_ty())?;
    let body = order(&a, &b)?.and(trans_part)?;
    let pred = Term::abs(
        nat_ty(),
        subst::close(&Term::abs(nat_ty(), subst::close(&body, "b")), "a"),
    );

    // The transitivity conjunct `∀c. Order <b> c ⟹ Order <a> c` of `pred <a> <b>`.
    let p_trans = |t: &Thm| -> Result<Thm> { beta_nf_concl(t.clone())?.and_elim_r() };
    let p_order = |t: &Thm| -> Result<Thm> { beta_nf_concl(t.clone())?.and_elim_l() };

    // Covariant case, shared by tensor/sum.
    let binary_case = |tag: u64,
                       ctor: fn(Term, Term) -> Term,
                       rule: fn(Term, Term, Term, Term) -> Result<Thm>,
                       inv: fn() -> Result<Thm>,
                       wf_rule: fn(Term, Term) -> Result<Thm>,
                       a: &Term,
                       ap: &Term,
                       b: &Term,
                       bp: &Term|
     -> Result<Thm> {
        let (pa, pb) = (pred_app(&pred, a, ap), pred_app(&pred, b, bp));
        let (ia, ib) = (Thm::assume(pa.clone())?, Thm::assume(pb.clone())?);
        let (oa, ob) = (p_order(&ia)?, p_order(&ib)?); // Order a ap, Order b bp
        let lhs = ctor(a.clone(), b.clone()); // a ⊗ b
        let rhs = ctor(ap.clone(), bp.clone()); // ap ⊗ bp
        // First conjunct: Order lhs rhs.
        let o_lr = rule(a.clone(), ap.clone(), b.clone(), bp.clone())?
            .imp_elim(oa.clone())?
            .imp_elim(ob.clone())?;
        // WfTyCode lhs (for the `c = 1` branch).
        let wf_lhs = wf_rule(a.clone(), b.clone())?
            .imp_elim(wf_left(a, ap, oa.clone())?)?
            .imp_elim(wf_left(b, bp, ob.clone())?)?;

        // Second conjunct: ∀c. Order rhs c ⟹ Order lhs c.
        let c = nvar("c");
        let o_rhs_c = order(&rhs, &c)?;
        let disj = inv()?
            .all_elim(ap.clone())?
            .all_elim(bp.clone())?
            .all_elim(c.clone())?
            .imp_elim(Thm::assume(o_rhs_c.clone())?)?; // c=1 ∨ disj_right(rhs, c)
        // c = 1 branch.
        let left = {
            let hc = c.clone().equals(ty_unit())?;
            let o_lhs_1 = ord_term(lhs.clone())?.imp_elim(wf_lhs.clone())?; // Order lhs 1
            transport_r(
                &lhs,
                &ty_unit(),
                &c,
                Thm::assume(hc.clone())?.sym()?,
                o_lhs_1,
            )?
            .imp_intro(&hc)?
        };
        // congruent branch.
        let right = {
            let dr = disj_right(ctor, &rhs, &c)?;
            let h = Thm::assume(dr.clone())?;
            let recon = h.clone().and_elim_l()?; // c = ctor (ty_arg1 c)(ty_arg2 c)
            let orders = h.and_elim_r()?;
            let o1 = orders
                .clone()
                .and_elim_l()? // Order (ty_arg1 rhs)(ty_arg1 c)
                .rewrite(&ty_arg1_ctor(tag, ap, bp)?)?; // Order ap (ty_arg1 c)
            let o2 = orders.and_elim_r()?.rewrite(&ty_arg2_ctor(tag, ap, bp)?)?; // Order bp (ty_arg2 c)
            let (a1c, a2c) = (ty_arg1(&c)?, ty_arg2(&c)?);
            let la = p_trans(&ia)?.all_elim(a1c.clone())?.imp_elim(o1)?; // Order a (ty_arg1 c)
            let lb = p_trans(&ib)?.all_elim(a2c.clone())?.imp_elim(o2)?; // Order b (ty_arg2 c)
            let o_lhs_args = rule(a.clone(), a1c.clone(), b.clone(), a2c.clone())?
                .imp_elim(la)?
                .imp_elim(lb)?; // Order lhs ((ty_arg1 c)⊗(ty_arg2 c))
            transport_r(&lhs, &ctor(a1c, a2c), &c, recon.sym()?, o_lhs_args)?.imp_intro(&dr)?
        };
        let o_lhs_c = disj
            .or_elim(left, right)?
            .imp_intro(&o_rhs_c)?
            .all_intro("c", nat_ty())?;
        beta_nf_expand(pred_app(&pred, &lhs, &rhs), o_lr.and_intro(o_lhs_c)?)?
            .imp_intro(&pb)?
            .imp_intro(&pa)
    };

    let ind = ord_induction(
        &pred,
        // init: 0 below everything ⇒ trans is immediate.
        |a| {
            let wfa = wf_ty_code(a)?;
            let o0a = ord_init(a.clone())?.imp_elim(Thm::assume(wfa.clone())?)?; // Order 0 a
            let c = nvar("c");
            let oac = Thm::assume(order(a, &c)?)?; // Order a c
            // ∀c. Order a c ⟹ Order 0 c   (0 is below the well-formed `c`).
            let wfc = ord_wf()?
                .all_elim(a.clone())?
                .all_elim(c.clone())?
                .imp_elim(oac)?
                .and_elim_r()?; // WfTyCode c
            let trans = ord_init(c.clone())?
                .imp_elim(wfc)? // Order 0 c
                .imp_intro(&order(a, &c)?)?
                .all_intro("c", nat_ty())?;
            beta_nf_expand(pred_app(&pred, &ty_empty(), a), o0a.and_intro(trans)?)?.imp_intro(&wfa)
        },
        // term: a below 1 ⇒ trans via inv_unit.
        |a| {
            let wfa = wf_ty_code(a)?;
            let oa1 = ord_term(a.clone())?.imp_elim(Thm::assume(wfa.clone())?)?;
            let c = nvar("c");
            let o1c = Thm::assume(order(&ty_unit(), &c)?)?;
            let hc = inv_unit()?.all_elim(c.clone())?.imp_elim(o1c.clone())?; // c = 1
            let oac = transport_r(a, &ty_unit(), &c, hc.sym()?, oa1.clone())?; // Order a c
            let trans = oac
                .imp_intro(&order(&ty_unit(), &c)?)?
                .all_intro("c", nat_ty())?;
            beta_nf_expand(pred_app(&pred, a, &ty_unit()), oa1.and_intro(trans)?)?.imp_intro(&wfa)
        },
        // base: trans is the identity.
        |i| {
            let xi = ty_base(i.clone());
            let o = ord_base(i.clone())?;
            let c = nvar("c");
            let trans = Thm::assume(order(&xi, &c)?)?
                .imp_intro(&order(&xi, &c)?)?
                .all_intro("c", nat_ty())?;
            beta_nf_expand(pred_app(&pred, &xi, &xi), o.and_intro(trans)?)
        },
        |a, ap, b, bp| {
            binary_case(
                3, ty_tensor, ord_tensor, inv_tensor, wf_tensor, a, ap, b, bp,
            )
        },
        |a, ap, b, bp| binary_case(4, ty_sum, ord_sum, inv_sum, wf_sum, a, ap, b, bp),
    )?;

    // ∀a b. Order a b ⟹ (Order a b ∧ ∀c. Order b c ⟹ Order a c) → reassemble.
    let (x, y, z) = (nvar("a"), nvar("b"), nvar("c"));
    let oab = Thm::assume(order(&x, &y)?)?;
    let trans = beta_nf_concl(
        ind.all_elim(x.clone())?
            .all_elim(y.clone())?
            .imp_elim(oab.clone())?,
    )?
    .and_elim_r()?; // {Order a b} ⊢ ∀c. Order b c ⟹ Order a c
    trans
        .all_elim(z.clone())?
        .imp_intro(&order(&x, &y)?)?
        .all_intro("c", nat_ty())?
        .all_intro("b", nat_ty())?
        .all_intro("a", nat_ty())
}

// ----------------------------------------------------------------------------
// Antisymmetry — `Order` is a partial order
// ----------------------------------------------------------------------------

/// `⊢ ∀c. Order c ⌜0⌝ ⟹ c = ⌜0⌝` — `0` is **minimal**: nothing is strictly below
/// it. The mirror of [`inv_unit`] (motive `pred a b := (b = ⌜0⌝) ⟹ (a = ⌜0⌝)`);
/// the only non-vacuous case is `init`, where the conclusion `0 = 0` is reflexivity.
pub fn inv_empty() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let body = b
        .clone()
        .equals(ty_empty())?
        .imp(a.clone().equals(ty_empty())?)?;
    let inner = Term::abs(nat_ty(), subst::close(&body, "b"));
    let pred = Term::abs(nat_ty(), subst::close(&inner, "a"));

    // `(y = 0) ⟹ (x = 0)` discharged ex falso when `y ≠ 0`.
    let vacuous = |x: &Term, y: &Term| -> Result<Thm> {
        let h = y.clone().equals(ty_empty())?;
        let imp = ty_code_distinct(y, &ty_empty())?
            .not_elim(Thm::assume(h.clone())?)? // {y=0} ⊢ F
            .false_elim(x.clone().equals(ty_empty())?)?
            .imp_intro(&h)?; // (y=0) ⟹ (x=0)
        beta_nf_expand(pred_app(&pred, x, y), imp)
    };

    let ind = ord_induction(
        &pred,
        |a| {
            // pred 0 a : (a=0) ⟹ (0=0); the consequent is reflexivity.
            let imp = Thm::refl(ty_empty())?.imp_intro(&a.clone().equals(ty_empty())?)?;
            beta_nf_expand(pred_app(&pred, &ty_empty(), a), imp)?.imp_intro(&wf_ty_code(a)?)
        },
        |a| vacuous(a, &ty_unit())?.imp_intro(&wf_ty_code(a)?), // b = 1 ≠ 0
        |i| {
            let xi = ty_base(i.clone());
            let h = xi.clone().equals(ty_empty())?;
            beta_nf_expand(
                pred_app(&pred, &xi, &xi),
                Thm::assume(h.clone())?.imp_intro(&h)?,
            )
        },
        |a, ap, b, bp| {
            vacuous(
                &ty_tensor(a.clone(), b.clone()),
                &ty_tensor(ap.clone(), bp.clone()),
            )?
            .imp_intro(&pred_app(&pred, b, bp))?
            .imp_intro(&pred_app(&pred, a, ap))
        },
        |a, ap, b, bp| {
            vacuous(
                &ty_sum(a.clone(), b.clone()),
                &ty_sum(ap.clone(), bp.clone()),
            )?
            .imp_intro(&pred_app(&pred, b, bp))?
            .imp_intro(&pred_app(&pred, a, ap))
        },
    )?;

    let c = nvar("c");
    let ord_c0 = order(&c, &ty_empty())?;
    let pred_c0 = ind
        .all_elim(c.clone())?
        .all_elim(ty_empty())?
        .imp_elim(Thm::assume(ord_c0.clone())?)?; // {Order c 0} ⊢ (0=0) ⟹ (c=0)
    beta_nf_concl(pred_c0)?
        .imp_elim(Thm::refl(ty_empty())?)? // {Order c 0} ⊢ c = 0
        .imp_intro(&ord_c0)?
        .all_intro("c", nat_ty())
}

/// `⊢ ∀a b. Order a b ⟹ Order b a ⟹ a = b` — **antisymmetry**, so `Order` is a
/// partial order. By rule induction on `Order a b` (motive `pred a b :=
/// Order b a ⟹ a = b`): `init`/`term` use [`inv_empty`]/[`inv_unit`], the
/// covariant cases invert the reverse relation and recurse.
pub fn ord_antisym() -> Result<Thm> {
    let (a, b) = (nvar("a"), nvar("b"));
    let body = order(&b, &a)?.imp(a.clone().equals(b.clone())?)?; // Order b a ⟹ a = b
    let inner = Term::abs(nat_ty(), subst::close(&body, "b"));
    let pred = Term::abs(nat_ty(), subst::close(&inner, "a"));

    let binary_case = |tag: u64,
                       ctor: fn(Term, Term) -> Term,
                       inv: fn() -> Result<Thm>,
                       a: &Term,
                       ap: &Term,
                       b: &Term,
                       bp: &Term|
     -> Result<Thm> {
        let (pa, pb) = (pred_app(&pred, a, ap), pred_app(&pred, b, bp));
        let ih_a = beta_nf_concl(Thm::assume(pa.clone())?)?; // Order ap a ⟹ a = ap
        let ih_b = beta_nf_concl(Thm::assume(pb.clone())?)?; // Order bp b ⟹ b = bp
        let lhs = ctor(a.clone(), b.clone());
        let rhs = ctor(ap.clone(), bp.clone());
        let o_rl = order(&rhs, &lhs)?;
        let disj = inv()?
            .all_elim(ap.clone())?
            .all_elim(bp.clone())?
            .all_elim(lhs.clone())?
            .imp_elim(Thm::assume(o_rl.clone())?)?; // lhs=1 ∨ disj_right(rhs, lhs)
        let left = {
            let h = lhs.clone().equals(ty_unit())?;
            ty_code_distinct(&lhs, &ty_unit())?
                .not_elim(Thm::assume(h.clone())?)?
                .false_elim(lhs.clone().equals(rhs.clone())?)?
                .imp_intro(&h)?
        };
        let right = {
            let dr = disj_right(ctor, &rhs, &lhs)?;
            let orders = Thm::assume(dr.clone())?.and_elim_r()?;
            let o1 = orders
                .clone()
                .and_elim_l()? // Order (ty_arg1 rhs)(ty_arg1 lhs)
                .rewrite(&ty_arg1_ctor(tag, ap, bp)?)?
                .rewrite(&ty_arg1_ctor(tag, a, b)?)?; // Order ap a
            let o2 = orders
                .and_elim_r()?
                .rewrite(&ty_arg2_ctor(tag, ap, bp)?)?
                .rewrite(&ty_arg2_ctor(tag, a, b)?)?; // Order bp b
            let ea = ih_a.clone().imp_elim(o1)?; // a = ap
            let eb = ih_b.clone().imp_elim(o2)?; // b = bp
            ctor_cong(tag, ea, eb)?.imp_intro(&dr)? // lhs = rhs
        };
        let eq = disj.or_elim(left, right)?.imp_intro(&o_rl)?; // Order rhs lhs ⟹ lhs = rhs
        beta_nf_expand(pred_app(&pred, &lhs, &rhs), eq)?
            .imp_intro(&pb)?
            .imp_intro(&pa)
    };

    let ind = ord_induction(
        &pred,
        |a| {
            let wfa = wf_ty_code(a)?;
            let oa0 = order(a, &ty_empty())?;
            let eq = inv_empty()?
                .all_elim(a.clone())?
                .imp_elim(Thm::assume(oa0.clone())?)? // a = 0
                .sym()? // 0 = a
                .imp_intro(&oa0)?; // Order a 0 ⟹ 0 = a
            beta_nf_expand(pred_app(&pred, &ty_empty(), a), eq)?.imp_intro(&wfa)
        },
        |a| {
            let wfa = wf_ty_code(a)?;
            let o1a = order(&ty_unit(), a)?;
            let eq = inv_unit()?
                .all_elim(a.clone())?
                .imp_elim(Thm::assume(o1a.clone())?)? // a = 1
                .imp_intro(&o1a)?; // Order 1 a ⟹ a = 1
            beta_nf_expand(pred_app(&pred, a, &ty_unit()), eq)?.imp_intro(&wfa)
        },
        |i| {
            let xi = ty_base(i.clone());
            let o = order(&xi, &xi)?;
            let eq = Thm::refl(xi.clone())?.imp_intro(&o)?; // Order Xi Xi ⟹ Xi = Xi
            beta_nf_expand(pred_app(&pred, &xi, &xi), eq)
        },
        |a, ap, b, bp| binary_case(3, ty_tensor, inv_tensor, a, ap, b, bp),
        |a, ap, b, bp| binary_case(4, ty_sum, inv_sum, a, ap, b, bp),
    )?;

    let (x, y) = (nvar("a"), nvar("b"));
    let oab = Thm::assume(order(&x, &y)?)?;
    beta_nf_concl(
        ind.all_elim(x.clone())?
            .all_elim(y.clone())?
            .imp_elim(oab)?,
    )? // Order b a ⟹ a = b
    .imp_intro(&order(&x, &y)?)?
    .all_intro("b", nat_ty())?
    .all_intro("a", nat_ty())
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// `inv_unit` is closed and inverts a concrete `Order ⌜1⌝ ⌜1⌝`.
    #[test]
    fn inversion_unit() {
        let thm = inv_unit().expect("inv_unit");
        assert!(thm.hyps().is_empty(), "inv_unit should be closed");
        // Order 1 1 ⟹ 1 = 1 (from terminal at a=1).
        let o11 = ord_term(ty_unit())
            .and_then(|x| x.imp_elim(wf_unit()?))
            .expect("Order 1 1");
        let eq = thm
            .all_elim(ty_unit())
            .and_then(|x| x.imp_elim(o11))
            .expect("1 = 1");
        assert!(eq.hyps().is_empty());
    }

    /// The binary inversions, both `1`/`0` inversions, transitivity, and
    /// antisymmetry replay closed.
    #[test]
    fn inversion_binary_closed() {
        for (name, thm) in [
            ("inv_tensor", inv_tensor()),
            ("inv_sum", inv_sum()),
            ("inv_empty", inv_empty()),
            ("ord_trans", ord_trans()),
            ("ord_antisym", ord_antisym()),
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }

    /// Antisymmetry applied: two `Order` derivations the same way collapse to an
    /// equality (`Order ⌜0⌝ ⌜0⌝` both ways gives `0 = 0` — a sanity instance).
    #[test]
    fn antisymmetry_instance() {
        let z = ty_empty();
        let o00 = ord_init(z.clone())
            .and_then(|x| x.imp_elim(wf_empty()?))
            .expect("Order 0 0");
        let eq = ord_antisym()
            .and_then(|x| x.all_elim(z.clone()))
            .and_then(|x| x.all_elim(z.clone()))
            .and_then(|x| x.imp_elim(o00.clone()))
            .and_then(|x| x.imp_elim(o00))
            .expect("0 = 0");
        assert!(eq.hyps().is_empty());
    }

    /// Transitivity composes the genuinely-richer cells: from `0 <: X₀⊗1` and
    /// `X₀⊗1 <: 1`, derive `0 <: 1`.
    #[test]
    fn transitivity_composes_bottom_top() {
        let t = ty_tensor(ty_base(lit(0)), ty_unit());
        let wf_t = wf_tensor(ty_base(lit(0)), ty_unit())
            .and_then(|x| x.imp_elim(wf_base(lit(0))?))
            .and_then(|x| x.imp_elim(wf_unit()?))
            .expect("WfTyCode (X0 ⊗ 1)");
        let bot = ord_init(t.clone())
            .and_then(|x| x.imp_elim(wf_t.clone()))
            .expect("Order 0 t");
        let top = ord_term(t.clone())
            .and_then(|x| x.imp_elim(wf_t))
            .expect("Order t 1");
        let bot_top = ord_trans()
            .and_then(|x| x.all_elim(ty_empty()))
            .and_then(|x| x.all_elim(t.clone()))
            .and_then(|x| x.all_elim(ty_unit()))
            .and_then(|x| x.imp_elim(bot))
            .and_then(|x| x.imp_elim(top))
            .expect("Order 0 1");
        assert!(bot_top.hyps().is_empty(), "Order 0 1 should be closed");
    }

    /// The component extractors round-trip on binary codes:
    /// `ty_arg1 ⌜p⊗q⌝ = p`, `ty_arg2 ⌜p⊗q⌝ = q` (and likewise for `+`).
    #[test]
    fn extractors_round_trip() {
        let (p, q) = (nvar("p"), nvar("q"));
        for (tag, name) in [(3u64, "⊗"), (4, "+")] {
            let a1 = ty_arg1_ctor(tag, &p, &q).unwrap_or_else(|e| panic!("arg1 {name}: {e}"));
            let a2 = ty_arg2_ctor(tag, &p, &q).unwrap_or_else(|e| panic!("arg2 {name}: {e}"));
            assert!(a1.hyps().is_empty() && a2.hyps().is_empty());
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
