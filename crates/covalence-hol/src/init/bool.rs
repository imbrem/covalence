//! HOL boolean connective rules, as closed quantified theorems —
//! **all derived, zero postulates.**
//!
//! These are the `∀`-quantified theorem forms of the connective
//! intro/elim rules (`⊢ ∀p q. p ⟹ q ⟹ p ∧ q`, …). Each is built
//! from the kernel's connective methods ([`Thm::and_intro`],
//! [`Thm::or_elim`], [`Thm::false_elim`], …) plus `imp_intro` /
//! `all_intro`, so they carry no hypotheses. The connectives are
//! defined constants in `covalence_core::defs::logic`; nothing here is
//! assumed.
//!
//! ## Coverage
//!
//! - `axiom_conj_intro`: `⊢ ∀p q. p ⟹ q ⟹ p ∧ q`
//! - `axiom_conjunct1`: `⊢ ∀p q. p ∧ q ⟹ p`
//! - `axiom_conjunct2`: `⊢ ∀p q. p ∧ q ⟹ q`
//! - `axiom_disj1`: `⊢ ∀p q. p ⟹ p ∨ q`
//! - `axiom_disj2`: `⊢ ∀p q. q ⟹ p ∨ q`
//! - `axiom_disj_cases`:
//!     `⊢ ∀p q r. p ∨ q ⟹ (p ⟹ r) ⟹ (q ⟹ r) ⟹ r`
//! - `axiom_mp`: `⊢ ∀p q. (p ⟹ q) ⟹ p ⟹ q`
//! - `axiom_not_def`: `⊢ ∀p. ¬p ⟺ (p ⟹ F)`
//! - `axiom_true`: `⊢ T`
//! - `axiom_false_elim`: `⊢ ∀p. F ⟹ p` (ex falso), from the kernel's
//!   [`Thm::false_elim`] rule.
//!
//! ## Polymorphic theorems
//!
//! `∀`/`∃` facts are stored at the generic carrier `'a` and
//! `inst_tfree`-specialised on demand via the `…_at(α)` accessors.
//!
//! - `axiom_spec_at(α)`: `⊢ ∀(P:α→bool). ∀(y:α). (∀x. P x) ⟹ P y`
//! - `axiom_exists_intro_at(α)`: `⊢ ∀(P:α→bool). ∀(y:α). P y ⟹ ∃x. P x`

use std::sync::LazyLock;

use crate::HolLightCtx;
use crate::proofs::bool::truth;
use crate::proofs::rewrite::{beta_nf, eq_sides, unfold_at_1, unfold_at_2};
use covalence_core::{Term, Thm, Type, defs};

// ============================================================================
// Helpers
// ============================================================================

fn b() -> Type {
    Type::bool()
}

/// Convert `⊢ a = b` (raw `=` at `bool`) into `⊢ a ⟺ b` (the `iff`
/// connective). Folds `iff ≡ λp q. p = q` backwards.
fn to_iff(eq_thm: Thm) -> Thm {
    let (a, c) = eq_sides(eq_thm.concl()).expect("to_iff: not an equation");
    let iff_eq = unfold_at_2(defs::iff(), a, c); // ⊢ (a ⟺ c) = (a = c)
    iff_eq
        .sym()
        .expect("to_iff: sym")
        .eq_mp(eq_thm)
        .expect("to_iff: eq_mp")
}

// ============================================================================
// ∧ — conjunction rules
// ============================================================================

/// `⊢ ∀p q : bool. p ⟹ q ⟹ p ∧ q`.
pub fn axiom_conj_intro() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        Thm::assume(p.clone())
            .unwrap()
            .and_intro(Thm::assume(q.clone()).unwrap())
            .unwrap() // {p,q} ⊢ p ∧ q
            .imp_intro(&q)
            .unwrap()
            .imp_intro(&p)
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

/// `⊢ ∀p q : bool. p ∧ q ⟹ p`.
pub fn axiom_conjunct1() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        let conj = ctx.mk_and(p.clone(), q.clone());
        Thm::assume(conj.clone())
            .unwrap()
            .and_elim_l()
            .unwrap() // {p∧q} ⊢ p
            .imp_intro(&conj)
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

/// `⊢ ∀p q : bool. p ∧ q ⟹ q`.
pub fn axiom_conjunct2() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        let conj = ctx.mk_and(p.clone(), q.clone());
        Thm::assume(conj.clone())
            .unwrap()
            .and_elim_r()
            .unwrap()
            .imp_intro(&conj)
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

// ============================================================================
// ∨ — disjunction rules
// ============================================================================

/// `⊢ ∀p q : bool. p ⟹ p ∨ q`.
pub fn axiom_disj1() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        Thm::assume(p.clone())
            .unwrap()
            .or_intro_l(q.clone())
            .unwrap() // {p} ⊢ p ∨ q
            .imp_intro(&p)
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

/// `⊢ ∀p q : bool. q ⟹ p ∨ q`.
pub fn axiom_disj2() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        Thm::assume(q.clone())
            .unwrap()
            .or_intro_r(p.clone())
            .unwrap() // {q} ⊢ p ∨ q
            .imp_intro(&q)
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

/// `⊢ ∀p q r : bool. p ∨ q ⟹ (p ⟹ r) ⟹ (q ⟹ r) ⟹ r`.
pub fn axiom_disj_cases() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        let r = Term::free("r", b());
        let disj = ctx.mk_or(p.clone(), q.clone());
        let pr = ctx.mk_imp(p, r.clone());
        let qr = ctx.mk_imp(q, r);
        Thm::assume(disj.clone())
            .unwrap()
            .or_elim(
                Thm::assume(pr.clone()).unwrap(),
                Thm::assume(qr.clone()).unwrap(),
            )
            .unwrap() // {p∨q, p⟹r, q⟹r} ⊢ r
            .imp_intro(&qr)
            .unwrap()
            .imp_intro(&pr)
            .unwrap()
            .imp_intro(&disj)
            .unwrap()
            .all_intro("r", b())
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

// ============================================================================
// ⟹ — implication (modus ponens, as a theorem)
// ============================================================================

/// `⊢ ∀p q : bool. (p ⟹ q) ⟹ p ⟹ q`.
pub fn axiom_mp() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let p = Term::free("p", b());
        let q = Term::free("q", b());
        let pq = ctx.mk_imp(p.clone(), q.clone());
        Thm::assume(pq.clone())
            .unwrap()
            .imp_elim(Thm::assume(p.clone()).unwrap())
            .unwrap() // {p⟹q, p} ⊢ q
            .imp_intro(&p)
            .unwrap()
            .imp_intro(&pq)
            .unwrap()
            .all_intro("q", b())
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

// ============================================================================
// ¬ — negation defining equation
// ============================================================================

/// `⊢ ∀p : bool. ¬p ⟺ (p ⟹ F)` — HOL Light's defining equation of
/// negation, derived by unfolding `¬ ≡ λp. p ⟹ F`.
pub fn axiom_not_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let p = Term::free("p", b());
        let not_eq = unfold_at_1(defs::not(), p.clone()); // ⊢ ¬p = (p ⟹ F)
        to_iff(not_eq).all_intro("p", b()).unwrap()
    });
    AX.clone()
}

// ============================================================================
// T, F — truth values
// ============================================================================

/// `⊢ T` — truth. Re-export of the derived [`crate::proofs::bool::truth`].
pub fn axiom_true() -> Thm {
    truth()
}

/// `⊢ ∀p : bool. F ⟹ p` — ex falso quodlibet, derived from the
/// kernel's [`Thm::false_elim`] rule: assume `F`, eliminate to `p`,
/// discharge, generalise.
pub fn axiom_false_elim() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let f = Term::bool_lit(false);
        let p = Term::free("p", b());
        Thm::assume(f.clone())
            .unwrap()
            .false_elim(p)
            .unwrap() // {F} ⊢ p
            .imp_intro(&f)
            .unwrap()
            .all_intro("p", b())
            .unwrap()
    });
    AX.clone()
}

// ============================================================================
// ∀, ∃ — quantifier theorems (polymorphic, instantiated on demand)
// ============================================================================

/// `⊢ ∀(P : 'a → bool). ∀(y : 'a). (∀x. P x) ⟹ P y` — specialisation,
/// derived from the kernel's `all_elim` (SPEC).
fn axiom_spec_generic() -> &'static Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let alpha = Type::tfree("a");
        let pred_ty = Type::fun(alpha.clone(), b());
        let p = Term::free("P", pred_ty.clone());
        let y = Term::free("y", alpha.clone());

        let p_x = Term::app(p.clone(), Term::free("x", alpha.clone()));
        let all_p = ctx.mk_forall("x", alpha.clone(), p_x); // ∀x. P x

        Thm::assume(all_p.clone())
            .unwrap()
            .all_elim(y.clone())
            .unwrap() // {∀x.P x} ⊢ P y
            .imp_intro(&all_p)
            .unwrap()
            .all_intro("y", alpha)
            .unwrap()
            .all_intro("P", pred_ty)
            .unwrap()
    });
    &AX
}

/// `axiom_spec` instantiated at a specific carrier type.
pub fn axiom_spec_at(alpha: Type) -> Thm {
    axiom_spec_generic()
        .clone()
        .inst_tfree("a", alpha)
        .expect("axiom_spec_at: inst_tfree on the generic 'a")
}

/// `⊢ ∀(P : 'a → bool). ∀(y : 'a). P y ⟹ ∃x. P x` — existential
/// introduction, derived from `∃ ≜ λP. ∀q. (∀x. P x ⟹ q) ⟹ q`.
fn axiom_exists_intro_generic() -> &'static Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let alpha = Type::tfree("a");
        let pred_ty = Type::fun(alpha.clone(), b());
        let p = Term::free("P", pred_ty.clone());
        let y = Term::free("y", alpha.clone());

        // The predicate `λx. P x` that `∃` is applied to.
        let pred_lam = {
            let p_x = Term::app(p.clone(), Term::free("x", alpha.clone()));
            Term::abs("x", alpha.clone(), covalence_core::subst::close(&p_x, "x"))
        };
        // ⊢ (∃x. P x) = body, with the unfolded body β-normalised so
        // the `(λx. P x) x` redexes collapse to `P x`.
        let ex_def_raw = unfold_at_1(defs::exists(alpha.clone()), pred_lam);
        let (_, body_raw) = eq_sides(ex_def_raw.concl()).expect("exists: ex_def is an equation");
        let ex_def = ex_def_raw
            .trans(beta_nf(body_raw))
            .expect("exists: trans body");
        let (_, body) = eq_sides(ex_def.concl()).unwrap();

        // Build {P y} ⊢ body, i.e. ⊢ ∀q. (∀x. P x ⟹ q) ⟹ q.
        let q = Term::free("q", b());
        let p_x = Term::app(p.clone(), Term::free("x", alpha.clone()));
        let all_imp = ctx.mk_forall("x", alpha.clone(), ctx.mk_imp(p_x, q.clone())); // ∀x. P x ⟹ q
        let p_y = Term::app(p.clone(), y.clone());
        let body_thm = Thm::assume(all_imp.clone())
            .unwrap()
            .all_elim(y.clone())
            .unwrap() // {all_imp} ⊢ P y ⟹ q
            .imp_elim(Thm::assume(p_y.clone()).unwrap())
            .unwrap() // {all_imp, P y} ⊢ q
            .imp_intro(&all_imp)
            .unwrap() // {P y} ⊢ (∀x. P x ⟹ q) ⟹ q
            .all_intro("q", b())
            .unwrap(); // {P y} ⊢ ∀q. …

        debug_assert_eq!(body_thm.concl(), &body, "exists body shape mismatch");

        // Fold to ∃, discharge P y, generalise.
        ex_def
            .sym()
            .unwrap()
            .eq_mp(body_thm)
            .unwrap() // {P y} ⊢ ∃x. P x
            .imp_intro(&p_y)
            .unwrap()
            .all_intro("y", alpha)
            .unwrap()
            .all_intro("P", pred_ty)
            .unwrap()
    });
    &AX
}

/// `axiom_exists_intro` instantiated at a specific carrier type.
pub fn axiom_exists_intro_at(alpha: Type) -> Thm {
    axiom_exists_intro_generic()
        .clone()
        .inst_tfree("a", alpha)
        .expect("axiom_exists_intro_at: inst_tfree on the generic 'a")
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// A derived theorem: hypothesis-free, bool-typed conclusion.
    fn check_derived(th: Thm) {
        assert!(
            th.hyps().is_empty(),
            "derived theorem must be axiom-free, got hyps {:?}",
            th.hyps()
        );
        assert!(th.concl().type_of().unwrap().is_bool());
    }

    #[test]
    fn conj_rules_are_derived() {
        check_derived(axiom_conj_intro());
        check_derived(axiom_conjunct1());
        check_derived(axiom_conjunct2());
    }

    #[test]
    fn disj_rules_are_derived() {
        check_derived(axiom_disj1());
        check_derived(axiom_disj2());
        check_derived(axiom_disj_cases());
    }

    #[test]
    fn mp_and_not_def_are_derived() {
        check_derived(axiom_mp());
        check_derived(axiom_not_def());
    }

    #[test]
    fn true_is_derived() {
        check_derived(axiom_true());
    }

    #[test]
    fn false_elim_is_derived() {
        check_derived(axiom_false_elim());
    }

    #[test]
    fn spec_at_bool_is_derived() {
        check_derived(axiom_spec_at(Type::bool()));
    }

    #[test]
    fn exists_intro_at_bool_is_derived() {
        check_derived(axiom_exists_intro_at(Type::bool()));
    }
}
