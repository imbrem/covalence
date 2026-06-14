//! Intro / elim rules for HOL's propositional connectives.
//!
//! In stock HOL Light the connectives `∧` / `∨` / `↔` / `∃` are
//! *definitions* over `=` (e.g. `p ∧ q ≡ (λf. f p q) = (λf. f T T)`),
//! and their intro / elim rules are *derived* theorems. In our kernel
//! each connective is a first-class `HolOp(_)` atom with no defining
//! equation — `reduce_prim` only evaluates it on `bool` *literals*
//! (`T ∧ F ≡ F`, …), which isn't enough to derive a rule about
//! arbitrary propositions `p`, `q`. So the standard rules live here
//! as `Thm::assume` postulates carrying a single self-hyp.
//!
//! **These postulates are temporary.** The connectives are meant to
//! be *built into the kernel* — the end-state is an axiom set that is
//! only about content-addressing / the observer system, with the
//! propositional rules either supplied directly by the kernel's
//! denotation of `HolOp(_)` or derived from it. When that lands, this
//! module collapses to thin tactic wrappers and the postulates go
//! away.
//!
//! Every helper in this file is one of:
//!
//! * a quantified-rule `LazyLock<Thm>` constant (the "axiom"), or
//! * a tactic that uses the axiom — invoking `all_elim` / `imp_elim`
//!   on it to produce the rule's conclusion at a specific witness.
//!
//! The tactics are pure combinators over kernel rules; they cannot
//! produce a false `Thm` independently. Soundness reduces to the
//! soundness of the postulated axioms, which are standard intro /
//! elim rules of higher-order logic.

use std::sync::LazyLock;

use covalence_core::{Term, Thm, Type};

use crate::HolLightCtx;

fn ctx() -> HolLightCtx {
    HolLightCtx::new()
}

fn bool_free(name: &str) -> Term {
    Term::free(name, Type::bool())
}

fn assume(body: Term) -> Thm {
    Thm::assume(body).expect("proofs::bool: closed bool body")
}

// ============================================================================
// Conjunction
// ============================================================================

/// `⊢ ∀p q:bool. p ⟹ q ⟹ p ∧ q` — and-introduction.
pub fn and_intro_ax() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let p = bool_free("p");
        let q = bool_free("q");
        let conj = ctx.mk_and(p.clone(), q.clone());
        let body = ctx.mk_imp(p.clone(), ctx.mk_imp(q.clone(), conj));
        let inner = ctx.mk_forall("q", Type::bool(), body);
        let outer = ctx.mk_forall("p", Type::bool(), inner);
        assume(outer)
    });
    AX.clone()
}

/// `⊢ ∀p q:bool. p ∧ q ⟹ p` — left and-elimination.
pub fn and_elim_l_ax() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let p = bool_free("p");
        let q = bool_free("q");
        let conj = ctx.mk_and(p.clone(), q.clone());
        let body = ctx.mk_imp(conj, p);
        let inner = ctx.mk_forall("q", Type::bool(), body);
        let outer = ctx.mk_forall("p", Type::bool(), inner);
        assume(outer)
    });
    AX.clone()
}

/// `⊢ ∀p q:bool. p ∧ q ⟹ q` — right and-elimination.
pub fn and_elim_r_ax() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let p = bool_free("p");
        let q = bool_free("q");
        let conj = ctx.mk_and(p.clone(), q.clone());
        let body = ctx.mk_imp(conj, q);
        let inner = ctx.mk_forall("q", Type::bool(), body);
        let outer = ctx.mk_forall("p", Type::bool(), inner);
        assume(outer)
    });
    AX.clone()
}

/// Build `Γ₁ ∪ Γ₂ ⊢ p ∧ q` from `Γ₁ ⊢ p` and `Γ₂ ⊢ q`.
pub fn and_intro(p_thm: Thm, q_thm: Thm) -> Thm {
    let p = p_thm.concl().clone();
    let q = q_thm.concl().clone();
    and_intro_ax()
        .all_elim(p)
        .expect("and_intro: all_elim p")
        .all_elim(q)
        .expect("and_intro: all_elim q")
        .imp_elim(p_thm)
        .expect("and_intro: imp_elim p")
        .imp_elim(q_thm)
        .expect("and_intro: imp_elim q")
}

/// Build `Γ ⊢ p` from `Γ ⊢ p ∧ q`. Requires the original conjunction
/// shape — errors out if the conclusion isn't a HOL `∧`.
pub fn and_elim_l(conj_thm: Thm) -> Thm {
    let (p, q) = parse_and(conj_thm.concl())
        .expect("and_elim_l: conclusion is not p ∧ q");
    and_elim_l_ax()
        .all_elim(p)
        .expect("and_elim_l: all_elim p")
        .all_elim(q)
        .expect("and_elim_l: all_elim q")
        .imp_elim(conj_thm)
        .expect("and_elim_l: imp_elim")
}

/// Build `Γ ⊢ q` from `Γ ⊢ p ∧ q`.
pub fn and_elim_r(conj_thm: Thm) -> Thm {
    let (p, q) = parse_and(conj_thm.concl())
        .expect("and_elim_r: conclusion is not p ∧ q");
    and_elim_r_ax()
        .all_elim(p)
        .expect("and_elim_r: all_elim p")
        .all_elim(q)
        .expect("and_elim_r: all_elim q")
        .imp_elim(conj_thm)
        .expect("and_elim_r: imp_elim")
}

/// Parse `App(App(/\, p), q)` → `(p, q)`. Returns `None` if the term
/// isn't a HOL conjunction (the `and` connective spec applied twice).
fn parse_and(t: &Term) -> Option<(Term, Term)> {
    let (op, p, q) = parse_binop(t)?;
    op.ptr_eq(&covalence_core::defs::and_spec()).then_some((p, q))
}

// ============================================================================
// Negation
// ============================================================================

/// `⊢ ∀p:bool. (p ⟹ F) ⟹ ¬p` — not-introduction.
pub fn not_intro_ax() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let p = bool_free("p");
        let imp_f = ctx.mk_imp(p.clone(), ctx.f());
        let body = ctx.mk_imp(imp_f, ctx.mk_not(p));
        let outer = ctx.mk_forall("p", Type::bool(), body);
        assume(outer)
    });
    AX.clone()
}

/// `⊢ ∀p:bool. ¬p ⟹ p ⟹ F` — not-elimination.
pub fn not_elim_ax() -> Thm {
    static AX: LazyLock<Thm> = LazyLock::new(|| {
        let ctx = ctx();
        let p = bool_free("p");
        let body = ctx.mk_imp(ctx.mk_not(p.clone()), ctx.mk_imp(p, ctx.f()));
        let outer = ctx.mk_forall("p", Type::bool(), body);
        assume(outer)
    });
    AX.clone()
}

/// Build `Γ ⊢ ¬p` from `Γ ⊢ p ⟹ F`. Requires the input's
/// conclusion to be `p ⟹ F`.
pub fn not_intro(p_imp_f_thm: Thm) -> Thm {
    let (p, _) = parse_imp(p_imp_f_thm.concl())
        .expect("not_intro: input is not `p ⟹ q`");
    not_intro_ax()
        .all_elim(p)
        .expect("not_intro: all_elim p")
        .imp_elim(p_imp_f_thm)
        .expect("not_intro: imp_elim")
}

/// Build `Γ₁ ∪ Γ₂ ⊢ F` from `Γ₁ ⊢ ¬p` and `Γ₂ ⊢ p`.
pub fn not_elim(not_p_thm: Thm, p_thm: Thm) -> Thm {
    let p = p_thm.concl().clone();
    not_elim_ax()
        .all_elim(p)
        .expect("not_elim: all_elim p")
        .imp_elim(not_p_thm)
        .expect("not_elim: imp_elim ¬p")
        .imp_elim(p_thm)
        .expect("not_elim: imp_elim p")
}

/// Parse `App(App(==>, p), q)` → `(p, q)`.
fn parse_imp(t: &Term) -> Option<(Term, Term)> {
    let (op, p, q) = parse_binop(t)?;
    op.ptr_eq(&covalence_core::defs::imp_spec()).then_some((p, q))
}

/// Parse a binary-connective application `App(App(op, p), q)` →
/// `(op_spec, p, q)` for *any* connective spec head. Callers filter on
/// the returned spec by `TermSpec::ptr_eq` (see [`parse_and`] /
/// [`parse_imp`]).
fn parse_binop(t: &Term) -> Option<(covalence_core::defs::TermSpec, Term, Term)> {
    use covalence_core::TermKind;
    let TermKind::App(f, q) = t.kind() else {
        return None;
    };
    let TermKind::App(head, p) = f.kind() else {
        return None;
    };
    let TermKind::Spec(h, _) = head.kind() else {
        return None;
    };
    Some((h.clone(), p.clone(), q.clone()))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn and_intro_yields_conjunction() {
        let ctx = ctx();
        let p_thm = Thm::assume(ctx.t()).expect("assume T");
        let q_thm = Thm::assume(ctx.t()).expect("assume T");
        let conj = and_intro(p_thm, q_thm);
        // Conclusion is `T ∧ T`.
        let (lhs, rhs) = parse_and(conj.concl()).expect("conj shape");
        assert_eq!(lhs, ctx.t());
        assert_eq!(rhs, ctx.t());
    }

    #[test]
    fn and_elim_l_round_trips() {
        let ctx = ctx();
        let p_thm = Thm::assume(ctx.t()).expect("assume T");
        let q_thm = Thm::assume(ctx.f()).expect("assume F");
        let conj = and_intro(p_thm.clone(), q_thm);
        let lhs = and_elim_l(conj);
        assert_eq!(lhs.concl(), p_thm.concl());
    }

    #[test]
    fn and_elim_r_round_trips() {
        let ctx = ctx();
        let p_thm = Thm::assume(ctx.t()).expect("assume T");
        let q_thm = Thm::assume(ctx.f()).expect("assume F");
        let conj = and_intro(p_thm, q_thm.clone());
        let rhs = and_elim_r(conj);
        assert_eq!(rhs.concl(), q_thm.concl());
    }
}
