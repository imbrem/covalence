//! HOL boolean connective rule axioms.
//!
//! Provides the standard HOL Light rule-axioms for `∧` / `∨` / `⟹`
//! / `¬` / `∀` / `∃` as `LazyLock<Thm>` constants. Each is a
//! `Thm::assume` over a Trueprop-wrapped HOL term — the standard
//! axiom-as-hypothesis pattern; downstream derivations that use a
//! rule carry the rule's concl in their hyps for audit, and
//! `PureHol::hyps()` filters such axiom hyps from the user-facing
//! report (see `pure_hol.rs`).
//!
//! The connectives themselves (`mk_and`, `mk_or`, `mk_imp`,
//! `mk_not`, `mk_forall`, `mk_exists`) live on
//! `crate::HolLightCtx`; the rules here pin down their
//! behaviour at the HOL bool level.
//!
//! ## Coverage
//!
//! Each connective gets its classical introduction / elimination
//! rule(s) in HOL form. These are equivalent to HOL Light's tactics
//! (`CONJ_TAC`, `DISJ1_TAC`, `MP`, etc.) lifted to theorem form.
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
//! - `axiom_false_elim`: `⊢ ∀p. F ⟹ p` (ex falso)
//!
//! ## Polymorphic axioms
//!
//! For `∀`/`∃` and other type-parametric facts we expose `… _at(α)`
//! variants returning the axiom instantiated at a specific
//! carrier type. The underlying `LazyLock<Thm>` stores the
//! generic-type version and `Thm::inst_tfree` produces specific
//! instances on demand (cheap via the new Pure `Def` design).
//!
//! - `axiom_spec_at(α)`: `⊢ ∀(P:α→bool). ∀(y:α). (∀x. P x) ⟹ P y`
//! - `axiom_exists_intro_at(α)`: `⊢ ∀(P:α→bool). ∀(y:α). P y ⟹ ∃x. P x`

use std::sync::LazyLock;

use crate::HolLightCtx;
use covalence_core::{Term, Thm, Type};

// ============================================================================
// Helpers
// ============================================================================

/// Wrap a HOL bool term `body` in `Trueprop` and assume it, giving
/// `{Trueprop body} ⊢ Trueprop body`. The single hypothesis is
/// the standard audit-trail; downstream `PureHol::hyps()` filters
/// it from the user-facing report.
fn assume_hol_axiom(body: Term) -> Thm {
    Thm::assume(body).expect("stdlib::bool: axiom body must be HOL bool-typed")
}

// ============================================================================
// ∧ — conjunction rules
// ============================================================================

/// `⊢ ∀p q : bool. p ⟹ q ⟹ p ∧ q`.
pub fn axiom_conj_intro() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let conj = ctx.mk_and(p.clone(), q.clone());
        let body = ctx.mk_imp(p.clone(), ctx.mk_imp(q.clone(), conj));
        let inner = ctx.mk_forall("q", bool_ty.clone(), body);
        let outer = ctx.mk_forall("p", bool_ty, inner);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

/// `⊢ ∀p q : bool. p ∧ q ⟹ p`.
pub fn axiom_conjunct1() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let conj = ctx.mk_and(p.clone(), q.clone());
        let body = ctx.mk_imp(conj, p);
        let inner = ctx.mk_forall("q", bool_ty.clone(), body);
        let outer = ctx.mk_forall("p", bool_ty, inner);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

/// `⊢ ∀p q : bool. p ∧ q ⟹ q`.
pub fn axiom_conjunct2() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let conj = ctx.mk_and(p.clone(), q.clone());
        let body = ctx.mk_imp(conj, q);
        let inner = ctx.mk_forall("q", bool_ty.clone(), body);
        let outer = ctx.mk_forall("p", bool_ty, inner);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

// ============================================================================
// ∨ — disjunction rules
// ============================================================================

/// `⊢ ∀p q : bool. p ⟹ p ∨ q`.
pub fn axiom_disj1() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let disj = ctx.mk_or(p.clone(), q.clone());
        let body = ctx.mk_imp(p, disj);
        let inner = ctx.mk_forall("q", bool_ty.clone(), body);
        let outer = ctx.mk_forall("p", bool_ty, inner);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

/// `⊢ ∀p q : bool. q ⟹ p ∨ q`.
pub fn axiom_disj2() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let disj = ctx.mk_or(p.clone(), q.clone());
        let body = ctx.mk_imp(q, disj);
        let inner = ctx.mk_forall("q", bool_ty.clone(), body);
        let outer = ctx.mk_forall("p", bool_ty, inner);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

/// `⊢ ∀p q r : bool. p ∨ q ⟹ (p ⟹ r) ⟹ (q ⟹ r) ⟹ r`.
pub fn axiom_disj_cases() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let r = Term::free("r", bool_ty.clone());
        let disj = ctx.mk_or(p.clone(), q.clone());
        let p_imp_r = ctx.mk_imp(p, r.clone());
        let q_imp_r = ctx.mk_imp(q, r.clone());
        let body = ctx.mk_imp(disj, ctx.mk_imp(p_imp_r, ctx.mk_imp(q_imp_r, r)));
        let inner1 = ctx.mk_forall("r", bool_ty.clone(), body);
        let inner2 = ctx.mk_forall("q", bool_ty.clone(), inner1);
        let outer = ctx.mk_forall("p", bool_ty, inner2);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

// ============================================================================
// ⟹ — implication rules
// ============================================================================

/// `⊢ ∀p q : bool. (p ⟹ q) ⟹ p ⟹ q` (HOL modus ponens).
pub fn axiom_mp() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let q = Term::free("q", bool_ty.clone());
        let p_imp_q = ctx.mk_imp(p.clone(), q.clone());
        let body = ctx.mk_imp(p_imp_q, ctx.mk_imp(p, q));
        let inner = ctx.mk_forall("q", bool_ty.clone(), body);
        let outer = ctx.mk_forall("p", bool_ty, inner);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

// ============================================================================
// ¬ — negation definition
// ============================================================================

/// `⊢ ∀p : bool. ¬p ⟺ (p ⟹ F)` — HOL Light's defining equation
/// of negation.
pub fn axiom_not_def() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let lhs = ctx.mk_not(p.clone());
        let rhs = ctx.mk_imp(p, ctx.f());
        let iff = ctx.mk_iff(lhs, rhs);
        let outer = ctx.mk_forall("p", bool_ty, iff);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

// ============================================================================
// T, F — truth values
// ============================================================================

/// `⊢ T` — truth.
pub fn axiom_true() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        assume_hol_axiom(ctx.t())
    });
    AX.clone()
}

/// `⊢ ∀p : bool. F ⟹ p` — ex falso quodlibet.
pub fn axiom_false_elim() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let bool_ty = ctx.bool_type();
        let p = Term::free("p", bool_ty.clone());
        let body = ctx.mk_imp(ctx.f(), p);
        let outer = ctx.mk_forall("p", bool_ty, body);
        assume_hol_axiom(outer)
    });
    AX.clone()
}

// ============================================================================
// ∀, ∃ — quantifier rules (polymorphic, instantiated on demand)
// ============================================================================

/// Universally-quantified specialisation axiom at the generic
/// carrier `'a`:
///
/// `⊢ ∀(P : 'a → bool). ∀(y : 'a). (∀x. P x) ⟹ P y`
fn axiom_spec_generic() -> &'static Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let alpha = Type::tfree("a");
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(alpha.clone(), bool_ty);

        let p = Term::free("P", pred_ty.clone());
        let y = Term::free("y", alpha.clone());

        // Inside (∀x. P x): x is the binder. mk_forall closes a
        // free named "x" of type 'a.
        let x = Term::free("x", alpha.clone());
        let p_x = Term::app(p.clone(), x);
        let all_p = ctx.mk_forall("x", alpha.clone(), p_x);

        let p_y = Term::app(p.clone(), y.clone());
        let body = ctx.mk_imp(all_p, p_y);

        let inner = ctx.mk_forall("y", alpha.clone(), body);
        let outer = ctx.mk_forall("P", pred_ty, inner);
        assume_hol_axiom(outer)
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

/// Existential introduction at the generic `'a`:
///
/// `⊢ ∀(P : 'a → bool). ∀(y : 'a). P y ⟹ ∃x. P x`
fn axiom_exists_intro_generic() -> &'static Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = HolLightCtx::new();
        let alpha = Type::tfree("a");
        let bool_ty = ctx.bool_type();
        let pred_ty = Type::fun(alpha.clone(), bool_ty);

        let p = Term::free("P", pred_ty.clone());
        let y = Term::free("y", alpha.clone());

        // ∃x. P x
        let x = Term::free("x", alpha.clone());
        let p_x = Term::app(p.clone(), x);
        let exists_p = ctx.mk_exists("x", alpha.clone(), p_x);

        let p_y = Term::app(p.clone(), y.clone());
        let body = ctx.mk_imp(p_y, exists_p);

        let inner = ctx.mk_forall("y", alpha.clone(), body);
        let outer = ctx.mk_forall("P", pred_ty, inner);
        assume_hol_axiom(outer)
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

    fn check_axiom(ax: Thm) {
        assert_eq!(ax.hyps().len(), 1, "axiom must have its own concl as hyp");
        assert_eq!(ax.hyps().iter().next().unwrap(), ax.concl());
        assert!(
            ax.concl().type_of().unwrap().is_formula(),
            "axiom concl must be prop-typed"
        );
    }

    #[test]
    fn conj_axioms_are_well_formed() {
        check_axiom(axiom_conj_intro());
        check_axiom(axiom_conjunct1());
        check_axiom(axiom_conjunct2());
    }

    #[test]
    fn disj_axioms_are_well_formed() {
        check_axiom(axiom_disj1());
        check_axiom(axiom_disj2());
        check_axiom(axiom_disj_cases());
    }

    #[test]
    fn imp_axiom_is_well_formed() {
        check_axiom(axiom_mp());
    }

    #[test]
    fn not_def_axiom_is_well_formed() {
        check_axiom(axiom_not_def());
    }

    #[test]
    fn true_and_false_elim_axioms_are_well_formed() {
        check_axiom(axiom_true());
        check_axiom(axiom_false_elim());
    }

    #[test]
    fn spec_at_bool_is_well_formed() {
        let ctx = HolLightCtx::new();
        let ax = axiom_spec_at(ctx.bool_type());
        assert!(ax.concl().type_of().unwrap().is_formula());
    }

    #[test]
    fn exists_intro_at_bool_is_well_formed() {
        let ctx = HolLightCtx::new();
        let ax = axiom_exists_intro_at(ctx.bool_type());
        assert!(ax.concl().type_of().unwrap().is_formula());
    }

    #[test]
    fn axioms_are_lazy_cached() {
        // Repeated calls return Thms with structurally equal
        // concl — the LazyLock identity guarantee carries through
        // to the user-facing API.
        let a1 = axiom_conj_intro();
        let a2 = axiom_conj_intro();
        assert_eq!(a1.concl(), a2.concl());
    }
}
