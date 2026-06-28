//! # λ_iter type codes + `WfTyCode` — the first reified judgement
//!
//! The deep embedding's **type fragment** (Fig 1: `A ::= 0 | 1 | Xᵢ | A⊗B | A+B`).
//! Each type is Gödel-coded as a `nat` using the [`code::pair`](crate::init::code)
//! pairing and a small constructor **tag**:
//!
//! ```text
//!     ⌜0⌝      = pair 0 0
//!     ⌜1⌝      = pair 1 0
//!     ⌜Xᵢ⌝     = pair 2 (pair i 0)
//!     ⌜A ⊗ B⌝  = pair 3 (pair ⌜A⌝ (pair ⌜B⌝ 0))
//!     ⌜A + B⌝  = pair 4 (pair ⌜A⌝ (pair ⌜B⌝ 0))
//! ```
//!
//! `WfTyCode : nat → bool` carves out the *well-formed* codes (the image of the
//! grammar). It is the **least predicate closed under the constructors**,
//! written impredicatively in the style of `init/prop.rs`'s `Derivable_Prop`:
//!
//! ```text
//!     WfTyCode c  :=  ∀S:nat→bool. Closed S ⟹ S c
//! ```
//!
//! where `Closed S` conjoins the five closure clauses (one per constructor).
//! This needs *no* recursion machinery: the impredicative `∀S` encodes the
//! least fixpoint directly. Provided:
//!
//! * the five **intro rules** ([`wf_empty`]/[`wf_unit`]/[`wf_base`]/
//!   [`wf_tensor`]/[`wf_sum`]) — the only way to obtain `⊢ WfTyCode ⌜A⌝`, so
//!   establishing well-formedness *is* exhibiting the grammar derivation; and
//! * **rule induction** [`wf_ty_induction`] — `inst S := pred` discharged
//!   against `Closed pred`; the engine behind the type-fragment metatheorems
//!   (subtyping reflexivity/transitivity — see `init/SKELETONS.md`).
//!
//! The `code.pair` strict-decrease laws (`pair_left_lt`/`pair_right_lt`) are not
//! needed *here* (the impredicative encoding handles recursion); they re-enter
//! for the value-extracting `El` decoders and `Typed`.

use covalence_core::{Result, Term, Thm, Type};

use crate::init::code::pair;
use crate::init::ext::TermExt;

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

/// `S : nat → bool` — the impredicative predicate variable bound in `WfTyCode`.
fn s_ty() -> Type {
    Type::fun(nat_ty(), bool_ty())
}
fn s_var() -> Term {
    Term::free("S", s_ty())
}
fn s_at(c: &Term) -> Result<Term> {
    s_var().apply(c.clone())
}

// ============================================================================
// Type constructor codes  (tags 0..=4)
// ============================================================================

/// `⌜0⌝ = pair 0 0`.
pub fn ty_empty() -> Term {
    pair(lit(0), lit(0))
}
/// `⌜1⌝ = pair 1 0`.
pub fn ty_unit() -> Term {
    pair(lit(1), lit(0))
}
/// `⌜Xᵢ⌝ = pair 2 (pair i 0)`.
pub fn ty_base(i: Term) -> Term {
    pair(lit(2), pair(i, lit(0)))
}
/// `⌜A ⊗ B⌝ = pair 3 (pair ⌜A⌝ (pair ⌜B⌝ 0))`.
pub fn ty_tensor(l: Term, r: Term) -> Term {
    pair(lit(3), pair(l, pair(r, lit(0))))
}
/// `⌜A + B⌝ = pair 4 (pair ⌜A⌝ (pair ⌜B⌝ 0))`.
pub fn ty_sum(l: Term, r: Term) -> Term {
    pair(lit(4), pair(l, pair(r, lit(0))))
}

// ============================================================================
// `Closed S` and `WfTyCode`
// ============================================================================

/// Number of closure clauses (one per type constructor).
const N_CLAUSES: usize = 5;

/// `Closed S` — the right-nested conjunction of the five closure clauses for a
/// predicate application `s_apply = λc. S c`:
///
/// ```text
///   S ⌜0⌝ ∧ S ⌜1⌝ ∧ (∀i. S ⌜Xᵢ⌝)
///         ∧ (∀l r. S l ⟹ S r ⟹ S ⌜l⊗r⌝)
///         ∧ (∀l r. S l ⟹ S r ⟹ S ⌜l+r⌝)
/// ```
fn closed(s_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    let (i, l, r) = (nvar("i"), nvar("l"), nvar("r"));

    let c_empty = s_apply(&ty_empty())?;
    let c_unit = s_apply(&ty_unit())?;
    let c_base = s_apply(&ty_base(i.clone()))?.forall("i", nat_ty())?;
    let c_tensor = s_apply(&l)?
        .imp(s_apply(&r)?.imp(s_apply(&ty_tensor(l.clone(), r.clone()))?)?)?
        .forall("r", nat_ty())?
        .forall("l", nat_ty())?;
    let c_sum = s_apply(&l)?
        .imp(s_apply(&r)?.imp(s_apply(&ty_sum(l.clone(), r.clone()))?)?)?
        .forall("r", nat_ty())?
        .forall("l", nat_ty())?;

    let clauses = [c_empty, c_unit, c_base, c_tensor, c_sum];
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter.next().expect("N_CLAUSES > 0");
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `WfTyCode c := ∀S. Closed S ⟹ S c`.
pub fn wf_ty_code(c: &Term) -> Result<Term> {
    closed(&|x| s_at(x))?.imp(s_at(c)?)?.forall("S", s_ty())
}

/// From a right-nested conjunction of `n` clauses, extract conjunct `k`
/// (`0`-based): peel `k` right-projections, then a left-projection (unless `k`
/// is the last clause, which has no trailing `∧`).
fn nth_conjunct(mut thm: Thm, k: usize, n: usize) -> Result<Thm> {
    for _ in 0..k {
        thm = thm.and_elim_r()?;
    }
    if k + 1 < n { thm.and_elim_l() } else { Ok(thm) }
}

// ============================================================================
// Intro rules — the LCF-style well-formedness constructors
// ============================================================================

/// A nullary intro rule: `⊢ WfTyCode ctor`, where the `idx`-th closure clause
/// is directly `S ctor`.
fn wf_nullary(idx: usize) -> Result<Thm> {
    let closed_t = closed(&|x| s_at(x))?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed S} ⊢ Closed S
    let clause = nth_conjunct(assumed, idx, N_CLAUSES)?; // ⊢ S ctor
    clause.imp_intro(&closed_t)?.all_intro("S", s_ty())
}

/// `⊢ WfTyCode ⌜0⌝`.
pub fn wf_empty() -> Result<Thm> {
    wf_nullary(0)
}
/// `⊢ WfTyCode ⌜1⌝`.
pub fn wf_unit() -> Result<Thm> {
    wf_nullary(1)
}

/// `⊢ WfTyCode ⌜Xᵢ⌝` for a base-type index `i`.
pub fn wf_base(i: Term) -> Result<Thm> {
    let closed_t = closed(&|x| s_at(x))?;
    let assumed = Thm::assume(closed_t.clone())?;
    let clause = nth_conjunct(assumed, 2, N_CLAUSES)?; // ⊢ ∀i. S ⌜Xᵢ⌝
    clause
        .all_elim(i)?
        .imp_intro(&closed_t)?
        .all_intro("S", s_ty())
}

/// A binary intro rule: `⊢ WfTyCode l ⟹ WfTyCode r ⟹ WfTyCode (ctor l r)`,
/// where the `idx`-th closure clause is `∀l r. S l ⟹ S r ⟹ S(ctor l r)`.
fn wf_binary(idx: usize, l: Term, r: Term) -> Result<Thm> {
    let closed_t = closed(&|x| s_at(x))?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed S} ⊢ Closed S
    // S l, S r from the two well-formedness hypotheses.
    let s_l = Thm::assume(wf_ty_code(&l)?)?
        .all_elim(s_var())?
        .imp_elim(assumed.clone())?; // {WfTyCode l, Closed S} ⊢ S l
    let s_r = Thm::assume(wf_ty_code(&r)?)?
        .all_elim(s_var())?
        .imp_elim(assumed.clone())?; // {WfTyCode r, Closed S} ⊢ S r
    let s_ctor = nth_conjunct(assumed, idx, N_CLAUSES)?
        .all_elim(l.clone())?
        .all_elim(r.clone())?
        .imp_elim(s_l)?
        .imp_elim(s_r)?; // {…} ⊢ S (ctor l r)
    s_ctor
        .imp_intro(&closed_t)?
        .all_intro("S", s_ty())? // ⊢ WfTyCode (ctor l r)
        .imp_intro(&wf_ty_code(&r)?)?
        .imp_intro(&wf_ty_code(&l)?)
}

/// `⊢ WfTyCode l ⟹ WfTyCode r ⟹ WfTyCode ⌜l ⊗ r⌝`.
pub fn wf_tensor(l: Term, r: Term) -> Result<Thm> {
    wf_binary(3, l, r)
}
/// `⊢ WfTyCode l ⟹ WfTyCode r ⟹ WfTyCode ⌜l + r⌝`.
pub fn wf_sum(l: Term, r: Term) -> Result<Thm> {
    wf_binary(4, l, r)
}

// ============================================================================
// Rule induction
// ============================================================================

/// **Rule induction over `WfTyCode`.** Given `pred : nat → bool` and proofs
/// that it is closed under the five constructors, conclude
///
/// ```text
///   ⊢ ∀c. WfTyCode c ⟹ pred c
/// ```
///
/// The case proofs are stated over fresh free variables (`i`, `l`, `r`);
/// `wf_ty_induction` performs the `∀`-generalisation. `pred <code>` is the raw
/// application `Term::app(pred, code)` (a β-redex when `pred` is a λ) — the case
/// proofs must conclude with exactly that shape (β-expand if needed). This is
/// the impredicative `inst S := pred` discharged against `Closed pred`.
pub fn wf_ty_induction(
    pred: &Term,
    case_empty: impl FnOnce() -> Result<Thm>,
    case_unit: impl FnOnce() -> Result<Thm>,
    case_base: impl FnOnce(&Term) -> Result<Thm>,
    case_tensor: impl FnOnce(&Term, &Term) -> Result<Thm>,
    case_sum: impl FnOnce(&Term, &Term) -> Result<Thm>,
) -> Result<Thm> {
    let (i, l, r) = (nvar("i"), nvar("l"), nvar("r"));

    // Build `⊢ Closed pred`, clause by clause, in `closed`'s layout order.
    let clause_thms = [
        case_empty()?,
        case_unit()?,
        case_base(&i)?.all_intro("i", nat_ty())?,
        case_tensor(&l, &r)?
            .all_intro("r", nat_ty())?
            .all_intro("l", nat_ty())?,
        case_sum(&l, &r)?
            .all_intro("r", nat_ty())?
            .all_intro("l", nat_ty())?,
    ];
    let mut iter = clause_thms.into_iter().rev();
    let mut acc = iter.next().expect("N_CLAUSES > 0");
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    let closed_pred = acc; // ⊢ Closed pred

    // Discharge the impredicative definition for an arbitrary `c`.
    let c = nvar("c");
    let wf = wf_ty_code(&c)?;
    let pred_c = Thm::assume(wf.clone())?
        .all_elim(pred.clone())? // Closed pred ⟹ pred c
        .imp_elim(closed_pred)?; // {WfTyCode c} ⊢ pred c
    pred_c.imp_intro(&wf)?.all_intro("c", nat_ty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::code::pair_pos;
    use crate::init::eq::beta_expand;

    /// All five intro rules replay to closed (hypothesis-free) theorems.
    #[test]
    fn intro_rules_are_closed() {
        let (l, r, i) = (nvar("l"), nvar("r"), nvar("i"));
        for (name, thm) in [
            ("wf_empty", wf_empty()),
            ("wf_unit", wf_unit()),
            ("wf_base", wf_base(i)),
            ("wf_tensor", wf_tensor(l.clone(), r.clone())),
            ("wf_sum", wf_sum(l, r)),
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }
    }

    /// A concrete derivation: `WfTyCode ⌜(X₀ ⊗ 1) + 0⌝` — exercise the binary
    /// rules over the nullary ones.
    #[test]
    fn wf_of_a_concrete_type() {
        // l = X₀ ⊗ 1,  type = l + 0.
        let x0 = ty_base(lit(0));
        let l = ty_tensor(x0.clone(), ty_unit());
        let wf_l = wf_tensor(x0, ty_unit())
            .and_then(|t| t.imp_elim(wf_base(lit(0))?))
            .and_then(|t| t.imp_elim(wf_unit()?))
            .expect("WfTyCode (X0 ⊗ 1)");
        let wf_lr = wf_sum(l, ty_empty())
            .and_then(|t| t.imp_elim(wf_l))
            .and_then(|t| t.imp_elim(wf_empty()?))
            .expect("WfTyCode ((X0⊗1)+0)");
        assert!(
            wf_lr.hyps().is_empty(),
            "concrete WfTyCode should be closed"
        );
    }

    /// Rule induction: every well-formed type code is a positive `nat`
    /// (`pred := λc. 0 < c`; every constructor code is `pair _ _ > 0`).
    /// Demonstrates the induction principle end-to-end.
    #[test]
    fn wf_codes_are_positive() {
        let c = nvar("c");
        // pred = λc. 0 < c
        let zero_lt = Term::app(Term::app(covalence_core::defs::nat_lt(), lit(0)), c.clone());
        let pred = Term::abs(nat_ty(), covalence_core::subst::close(&zero_lt, "c"));

        // `pred ctor` = `(λc.0<c) ctor`, by β-expanding `0 < ctor` (`pair_pos`
        // at the constructor's pair arguments).
        fn pos_of(pred: &Term, ctor: Term) -> Result<Thm> {
            let (pa, b) = ctor.as_app().expect("ctor is pair a b");
            let (_p, a) = pa.as_app().expect("pair a");
            let zero_lt_ctor = pair_pos()?.all_elim(a.clone())?.all_elim(b.clone())?;
            beta_expand(pred, ctor, zero_lt_ctor)
        }
        // binary case: `pred l ⟹ pred r ⟹ pred ctor` (positivity is unconditional).
        fn binary(pred: &Term, ctor: Term, l: &Term, r: &Term) -> Result<Thm> {
            let prl = pred.clone().apply(l.clone())?;
            let prr = pred.clone().apply(r.clone())?;
            pos_of(pred, ctor)?.imp_intro(&prr)?.imp_intro(&prl)
        }

        let thm = wf_ty_induction(
            &pred,
            || pos_of(&pred, ty_empty()),
            || pos_of(&pred, ty_unit()),
            |i| pos_of(&pred, ty_base(i.clone())),
            |l, r| binary(&pred, ty_tensor(l.clone(), r.clone()), l, r),
            |l, r| binary(&pred, ty_sum(l.clone(), r.clone()), l, r),
        )
        .expect("wf induction: codes positive");
        assert!(thm.hyps().is_empty(), "induction result should be closed");
    }
}
