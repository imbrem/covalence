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

use covalence_core::{Result, Term, Thm, Type, subst};

use crate::init::code::{pair, pair_inj_l, pair_inj_r};
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};

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

// ============================================================================
// Constructor distinctness — different tags ⇒ different codes
//
// Every type code is `pair tag payload` with a distinct literal `tag` (0..4).
// So two codes built from different constructors differ already in the *first*
// pairing component: `pair_inj_l` forces the tags equal, which `reduce` refutes.
// ============================================================================

/// Decompose a constructor code `pair tag payload` into `(tag, payload)`.
fn unpair(c: &Term) -> (Term, Term) {
    let (head, payload) = c.as_app().expect("code is `pair tag payload`");
    let (_pair, tag) = head.as_app().expect("`pair tag` is an application");
    (tag.clone(), payload.clone())
}

/// `⊢ ¬(c₁ = c₂)` for two constructor codes whose top-level tags are distinct
/// literals (i.e. any two *different* constructors). `pair_inj_l` forces the
/// tags equal; `reduce` folds that literal equation to `F`.
pub fn ty_code_distinct(c1: &Term, c2: &Term) -> Result<Thm> {
    let (t1, p1) = unpair(c1);
    let (t2, p2) = unpair(c2);
    let heq = c1.clone().equals(c2.clone())?;
    let tags_eq = pair_inj_l()?
        .all_elim(t1.clone())?
        .all_elim(p1)?
        .all_elim(t2.clone())?
        .all_elim(p2)?
        .imp_elim(Thm::assume(heq.clone())?)?; // {c₁=c₂} ⊢ t₁ = t₂
    t1.equals(t2)?
        .reduce()? // (t₁=t₂) = F
        .eq_mp(tags_eq)? // {c₁=c₂} ⊢ F
        .imp_intro(&heq)?
        .not_intro() // ¬(c₁=c₂)
}

// ============================================================================
// Generation (inversion) lemmas for `WfTyCode`
//
//   WfTyCode ⌜l ⊗ r⌝ ⟹ WfTyCode l ∧ WfTyCode r        (and likewise for +)
//
// Proved by **rule induction** with the strengthened predicate
//
//   pred c := WfTyCode c ∧ (∀u v. c = ctor u v ⟹ WfTyCode u ∧ WfTyCode v)
//
// The `WfTyCode c` conjunct is what makes induction go through: in the matching
// constructor case the induction hypotheses hand back `WfTyCode` of the sub-codes
// (which the bare inversion clause could not), and `pair_inj` recovers `u`/`v`;
// every other constructor case is vacuous by `ty_code_distinct`.
// ============================================================================

/// `λc. WfTyCode c ∧ (∀u v. c = ctor u v ⟹ WfTyCode u ∧ WfTyCode v)`.
fn inv_pred(ctor: fn(Term, Term) -> Term) -> Result<Term> {
    let c = nvar("c");
    let (u, v) = (nvar("u"), nvar("v"));
    let inv = c
        .clone()
        .equals(ctor(u.clone(), v.clone()))?
        .imp(wf_ty_code(&u)?.and(wf_ty_code(&v)?)?)?
        .forall("v", nat_ty())?
        .forall("u", nat_ty())?;
    let body = wf_ty_code(&c)?.and(inv)?;
    Ok(Term::abs(nat_ty(), subst::close(&body, "c")))
}

/// From `⊢ pair tag (pair l (pair r 0)) = pair tag (pair u (pair v 0))` recover
/// `⊢ l = u` and `⊢ r = v` (the two `code.pair` injectivity peels).
fn binary_payload_inj(
    tag: u64,
    l: &Term,
    r: &Term,
    u: &Term,
    v: &Term,
    h: Thm,
) -> Result<(Thm, Thm)> {
    let pl = pair(l.clone(), pair(r.clone(), lit(0)));
    let pu = pair(u.clone(), pair(v.clone(), lit(0)));
    // Peel the tag: pair l (pair r 0) = pair u (pair v 0).
    let payloads = pair_inj_r()?
        .all_elim(lit(tag))?
        .all_elim(pl)?
        .all_elim(lit(tag))?
        .all_elim(pu)?
        .imp_elim(h)?;
    let r0 = pair(r.clone(), lit(0));
    let v0 = pair(v.clone(), lit(0));
    let l_eq = pair_inj_l()?
        .all_elim(l.clone())?
        .all_elim(r0.clone())?
        .all_elim(u.clone())?
        .all_elim(v0.clone())?
        .imp_elim(payloads.clone())?; // l = u
    let tails = pair_inj_r()?
        .all_elim(l.clone())?
        .all_elim(r0)?
        .all_elim(u.clone())?
        .all_elim(v0)?
        .imp_elim(payloads)?; // pair r 0 = pair v 0
    let r_eq = pair_inj_l()?
        .all_elim(r.clone())?
        .all_elim(lit(0))?
        .all_elim(v.clone())?
        .all_elim(lit(0))?
        .imp_elim(tails)?; // r = v
    Ok((l_eq, r_eq))
}

/// Shared engine for the binary generation lemmas: `⊢ WfTyCode (ctor L R) ⟹
/// WfTyCode L ∧ WfTyCode R`, where `ctor` is the tag-`target_tag` constructor.
fn binary_inv(
    target_tag: u64,
    ctor: fn(Term, Term) -> Term,
    big_l: Term,
    big_r: Term,
) -> Result<Thm> {
    let pred = inv_pred(ctor)?;

    // The inversion clause `∀u v. code = ctor u v ⟹ WfTyCode u ∧ WfTyCode v`,
    // built vacuously when `code`'s tag differs from the target.
    let vacuous_inv = |code: &Term| -> Result<Thm> {
        let (u, v) = (nvar("u"), nvar("v"));
        let eq = code.clone().equals(ctor(u.clone(), v.clone()))?;
        ty_code_distinct(code, &ctor(u.clone(), v.clone()))?
            .not_elim(Thm::assume(eq.clone())?)? // {code = ctor u v} ⊢ F
            .false_elim(wf_ty_code(&u)?.and(wf_ty_code(&v)?)?)?
            .imp_intro(&eq)?
            .all_intro("v", nat_ty())?
            .all_intro("u", nat_ty())
    };

    // A constructor case whose code is *not* the target: `⊢ pred code`, given
    // `⊢ WfTyCode code`. The inversion conjunct is vacuous.
    let nullary_case = |code: Term, wf_code: Thm| -> Result<Thm> {
        let body = wf_code.and_intro(vacuous_inv(&code)?)?;
        beta_expand(&pred, code, body)
    };

    // A binary constructor case (`this_tag`, `this_ctor`, `this_wf`):
    // `⊢ pred l ⟹ pred r ⟹ pred (this_ctor l r)`.
    let binary_case = |this_tag: u64,
                       this_ctor: fn(Term, Term) -> Term,
                       this_wf: fn(Term, Term) -> Result<Thm>,
                       l: &Term,
                       r: &Term|
     -> Result<Thm> {
        let pred_l = pred.clone().apply(l.clone())?; // (λc.…) l  — the IH, applied
        let pred_r = pred.clone().apply(r.clone())?;
        let wf_l = beta_reduce(Thm::assume(pred_l.clone())?)?.and_elim_l()?; // {pred l} ⊢ WfTyCode l
        let wf_r = beta_reduce(Thm::assume(pred_r.clone())?)?.and_elim_l()?; // {pred r} ⊢ WfTyCode r
        let code = this_ctor(l.clone(), r.clone());
        let wf_code = this_wf(l.clone(), r.clone())?
            .imp_elim(wf_l.clone())?
            .imp_elim(wf_r.clone())?; // WfTyCode (this_ctor l r)
        let inv = if this_tag == target_tag {
            let (u, v) = (nvar("u"), nvar("v"));
            let eq = code.clone().equals(ctor(u.clone(), v.clone()))?;
            let (l_eq, r_eq) =
                binary_payload_inj(this_tag, l, r, &u, &v, Thm::assume(eq.clone())?)?;
            wf_l.clone()
                .rewrite(&l_eq)? // WfTyCode u
                .and_intro(wf_r.clone().rewrite(&r_eq)?)? // ∧ WfTyCode v
                .imp_intro(&eq)?
                .all_intro("v", nat_ty())?
                .all_intro("u", nat_ty())?
        } else {
            vacuous_inv(&code)?
        };
        let body = wf_code.and_intro(inv)?;
        beta_expand(&pred, code, body)?
            .imp_intro(&pred_r)?
            .imp_intro(&pred_l)
    };

    let induction = wf_ty_induction(
        &pred,
        || nullary_case(ty_empty(), wf_empty()?),
        || nullary_case(ty_unit(), wf_unit()?),
        |i| nullary_case(ty_base(i.clone()), wf_base(i.clone())?),
        |l, r| binary_case(3, ty_tensor, wf_tensor, l, r),
        |l, r| binary_case(4, ty_sum, wf_sum, l, r),
    )?; // ⊢ ∀c. WfTyCode c ⟹ pred c

    // Instantiate at the target code, peel the inversion conjunct, discharge the
    // `code = code` antecedent by reflexivity.
    let code = ctor(big_l.clone(), big_r.clone());
    let wf_code = wf_ty_code(&code)?;
    let pred_code = induction
        .all_elim(code.clone())?
        .imp_elim(Thm::assume(wf_code.clone())?)?; // {WfTyCode code} ⊢ pred code
    beta_reduce(pred_code)?
        .and_elim_r()? // ∀u v. code = ctor u v ⟹ WfTyCode u ∧ WfTyCode v
        .all_elim(big_l.clone())?
        .all_elim(big_r.clone())?
        .imp_elim(Thm::refl(code)?)? // {WfTyCode code} ⊢ WfTyCode L ∧ WfTyCode R
        .imp_intro(&wf_code)
}

/// `⊢ WfTyCode ⌜l ⊗ r⌝ ⟹ WfTyCode l ∧ WfTyCode r` — tensor generation.
pub fn wf_tensor_inv(l: Term, r: Term) -> Result<Thm> {
    binary_inv(3, ty_tensor, l, r)
}
/// `⊢ WfTyCode ⌜l + r⌝ ⟹ WfTyCode l ∧ WfTyCode r` — sum generation.
pub fn wf_sum_inv(l: Term, r: Term) -> Result<Thm> {
    binary_inv(4, ty_sum, l, r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::code::pair_pos;

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

    /// Every pair of *distinct* constructors yields unequal codes, closed.
    #[test]
    fn distinct_constructors() {
        let (l, r, i) = (nvar("l"), nvar("r"), nvar("i"));
        let codes = [
            ("0", ty_empty()),
            ("1", ty_unit()),
            ("X", ty_base(i)),
            ("⊗", ty_tensor(l.clone(), r.clone())),
            ("+", ty_sum(l, r)),
        ];
        for (n1, c1) in &codes {
            for (n2, c2) in &codes {
                if n1 == n2 {
                    continue;
                }
                let thm = ty_code_distinct(c1, c2).unwrap_or_else(|e| panic!("{n1} ≠ {n2}: {e}"));
                assert!(thm.hyps().is_empty(), "{n1} ≠ {n2} should be closed");
            }
        }
    }

    /// The generation lemmas replay closed, and actually invert a concrete
    /// derivation: `WfTyCode ⌜X₀ ⊗ 1⌝ ⟹ WfTyCode ⌜X₀⌝ ∧ WfTyCode ⌜1⌝`.
    #[test]
    fn generation_lemmas() {
        let (l, r) = (nvar("l"), nvar("r"));
        for (name, thm) in [
            ("wf_tensor_inv", wf_tensor_inv(l.clone(), r.clone())),
            ("wf_sum_inv", wf_sum_inv(l, r)),
        ] {
            let thm = thm.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(thm.hyps().is_empty(), "{name} should be closed");
        }

        // Invert a concrete tensor: feed in `WfTyCode (X₀ ⊗ 1)`, get the parts.
        let x0 = ty_base(lit(0));
        let wf_pair = wf_tensor(x0.clone(), ty_unit())
            .and_then(|t| t.imp_elim(wf_base(lit(0))?))
            .and_then(|t| t.imp_elim(wf_unit()?))
            .expect("WfTyCode (X0 ⊗ 1)");
        let parts = wf_tensor_inv(x0, ty_unit())
            .and_then(|t| t.imp_elim(wf_pair))
            .expect("invert WfTyCode (X0 ⊗ 1)");
        assert!(parts.hyps().is_empty(), "inverted parts should be closed");
        // ⊢ WfTyCode ⌜X₀⌝ ∧ WfTyCode ⌜1⌝ — both halves recoverable.
        parts.clone().and_elim_l().expect("WfTyCode X0");
        parts.and_elim_r().expect("WfTyCode 1");
    }
}
