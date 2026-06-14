//! Intro / elim rules for HOL's propositional connectives — **all
//! derived, no postulates.**
//!
//! The connectives are ordinary defined constants in
//! `covalence_core::defs::logic` (`∧ ≡ λp q. (λf. f p q) = (λf. f T T)`,
//! `¬ ≡ λp. p ⟹ F`, …). [`Thm::unfold_term_spec`] hands back each
//! defining equation `⊢ op = <body>`, and from there the standard
//! HOL Light `bool.ml` derivations reconstruct every intro / elim
//! rule using only kernel inference rules. Soundness is therefore the
//! soundness of the kernel itself — nothing here is assumed.
//!
//! ## Relationship to the kernel methods
//!
//! For efficiency the kernel also exposes these rules as direct
//! constructors ([`Thm::and_intro`], [`Thm::not_elim`], …) that build
//! the conclusion in one step. The derivations in *this* module are
//! the **soundness witnesses** for those fast methods (and the basis
//! for a future "paranoid mode" that runs them instead of trusting the
//! constructor). The `kernel_methods_match_derivations` test pins the
//! two together.
//!
//! The bootstrap chain:
//!
//! * [`truth`] — `⊢ T`, from `reduce_prim` on `T = T`.
//! * [`eqt_intro`] / [`eqt_elim`] — `⊢ p` ↔ `⊢ p = T`, via
//!   `deduct_antisym` / `eq_mp`.
//! * conjunction/negation rules — congruence + β-normalisation
//!   (`unfold_at_*` / `beta_nf` in [`super::rewrite`]) folding the
//!   definitions in and out.

use covalence_core::{defs, Term, Thm, Type};

use super::rewrite::{beta_nf, cong_at_fn, eq_sides, unfold_at_1, unfold_at_2};

/// A fresh-ish bound-variable name for the `∧` definition's inner
/// `λf`. `Thm::abs` rejects (soundly) any collision with a free var
/// in the hypotheses, so a distinctive name keeps the common case
/// working without a genvar facility.
const CONJ_F: &str = "_conj_f";

fn bool_ty() -> Type {
    Type::bool()
}

// ============================================================================
// Bootstrap: TRUTH and the `p ⟺ (p = T)` bridge
// ============================================================================

/// `⊢ T`. Derived: `reduce_prim` decides `(T = T) = T` on the closed
/// literals, and `refl T : ⊢ T = T` discharges the antecedent.
pub fn truth() -> Thm {
    let t = Term::bool_lit(true);
    let refl_t = Thm::refl(t.clone()).expect("truth: refl T");
    // ⊢ (T = T) = T
    let t_eq_t = refl_t.concl().clone();
    let reduced =
        Thm::reduce_prim(t_eq_t).expect("truth: reduce_prim (T=T)");
    reduced.eq_mp(refl_t).expect("truth: eq_mp")
}

/// `Γ ⊢ p` → `Γ ⊢ p = T` (HOL Light's `EQT_INTRO`). Via
/// `deduct_antisym` against [`truth`].
pub fn eqt_intro(th: Thm) -> Thm {
    th.deduct_antisym(truth()).expect("eqt_intro: deduct_antisym")
}

/// `Γ ⊢ p = T` → `Γ ⊢ p` (HOL Light's `EQT_ELIM`). Via `eq_mp` of
/// the symmetric equation against [`truth`].
pub fn eqt_elim(th: Thm) -> Thm {
    th.sym()
        .expect("eqt_elim: not an equation")
        .eq_mp(truth())
        .expect("eqt_elim: eq_mp")
}

// ============================================================================
// Conjunction — `p ∧ q ≡ (λf. f p q) = (λf. f T T)`
// ============================================================================

/// `⊢ (∧ p q) = ((λf. f p q) = (λf. f T T))` — the `∧` definition
/// unfolded at `p`, `q`.
fn and_body_at(p: Term, q: Term) -> Thm {
    unfold_at_2(defs::and(), p, q)
}

/// Build `Γ₁ ∪ Γ₂ ⊢ p ∧ q` from `Γ₁ ⊢ p` and `Γ₂ ⊢ q`.
///
/// Derivation (`CONJ`): from `⊢ p` and `⊢ q` get `⊢ p = T`, `⊢ q = T`;
/// congruence + `abs` build `⊢ (λf. f p q) = (λf. f T T)`, which is
/// the body of `p ∧ q` — fold it back through the definition.
pub fn and_intro(p_thm: Thm, q_thm: Thm) -> Thm {
    let p = p_thm.concl().clone();
    let q = q_thm.concl().clone();

    let p_eq_t = eqt_intro(p_thm); // ⊢ p = T
    let q_eq_t = eqt_intro(q_thm); // ⊢ q = T

    // ⊢ (λf. f p q) = (λf. f T T)
    let bbb = Type::fun(bool_ty(), Type::fun(bool_ty(), bool_ty()));
    let f = Term::free(CONJ_F, bbb.clone());
    let refl_f = Thm::refl(f).expect("and_intro: refl f");
    let fpq_eq = refl_f
        .cong_app(p_eq_t)
        .expect("and_intro: cong f p")
        .cong_app(q_eq_t)
        .expect("and_intro: cong f q"); // ⊢ f p q = f T T
    let lam_eq = fpq_eq.abs(CONJ_F, bbb).expect("and_intro: abs f");

    // Fold: ⊢ (∧ p q) = <that body>, then eq_mp backwards.
    let body_eq = and_body_at(p, q);
    body_eq
        .sym()
        .expect("and_intro: sym")
        .eq_mp(lam_eq)
        .expect("and_intro: eq_mp")
}

/// Build `Γ ⊢ p` from `Γ ⊢ p ∧ q` (`CONJUNCT1`). Apply both sides of
/// the unfolded conjunction to the selector `λa b. a` and β-normalise:
/// the LHS collapses to `p`, the RHS to `T`.
pub fn and_elim_l(conj_thm: Thm) -> Thm {
    and_elim_with(conj_thm, fst_selector())
}

/// Build `Γ ⊢ q` from `Γ ⊢ p ∧ q` (`CONJUNCT2`); selector `λa b. b`.
pub fn and_elim_r(conj_thm: Thm) -> Thm {
    and_elim_with(conj_thm, snd_selector())
}

/// Shared core of `and_elim_l` / `and_elim_r`: apply the unfolded
/// conjunction body to `selector` and read off `⊢ <component> = T`.
fn and_elim_with(conj_thm: Thm, selector: Term) -> Thm {
    let (p, q) =
        parse_and(conj_thm.concl()).expect("and_elim: conclusion is not p ∧ q");
    // ⊢ (λf. f p q) = (λf. f T T)
    let body = and_body_at(p, q).eq_mp(conj_thm).expect("and_elim: eq_mp body");
    // ⊢ (λf. f p q) sel = (λf. f T T) sel
    let applied = cong_at_fn(body, selector);
    let (lhs, rhs) =
        eq_sides(applied.concl()).expect("and_elim: applied is an equation");
    // ⊢ component = T : sym(lhs_nf) · applied · rhs_nf
    let comp_eq_t = beta_nf(lhs)
        .sym()
        .expect("and_elim: sym lhs")
        .trans(applied)
        .expect("and_elim: trans applied")
        .trans(beta_nf(rhs))
        .expect("and_elim: trans rhs");
    eqt_elim(comp_eq_t)
}

/// `λa b:bool. a`.
fn fst_selector() -> Term {
    Term::abs(bool_ty(), Term::abs(bool_ty(), Term::bound(1)))
}

/// `λa b:bool. b`.
fn snd_selector() -> Term {
    Term::abs(bool_ty(), Term::abs(bool_ty(), Term::bound(0)))
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

/// `⊢ (¬ p) = (p ⟹ F)` — the `¬` definition unfolded at `p`.
fn not_body_at(p: Term) -> Thm {
    unfold_at_1(defs::not(), p)
}

/// Build `Γ ⊢ ¬p` from `Γ ⊢ p ⟹ F` (`NOT_INTRO`). Just fold the
/// definition `¬p ≡ (p ⟹ F)` backwards.
pub fn not_intro(p_imp_f_thm: Thm) -> Thm {
    let (p, _) = parse_imp(p_imp_f_thm.concl())
        .expect("not_intro: input is not `p ⟹ q`");
    not_body_at(p)
        .sym()
        .expect("not_intro: sym")
        .eq_mp(p_imp_f_thm)
        .expect("not_intro: eq_mp")
}

/// Build `Γ₁ ∪ Γ₂ ⊢ F` from `Γ₁ ⊢ ¬p` and `Γ₂ ⊢ p` (`NOT_ELIM`).
/// Unfold `¬p` to `p ⟹ F`, then modus ponens with `⊢ p`.
pub fn not_elim(not_p_thm: Thm, p_thm: Thm) -> Thm {
    let p = p_thm.concl().clone();
    not_body_at(p)
        .eq_mp(not_p_thm)
        .expect("not_elim: eq_mp ¬p → (p⟹F)")
        .imp_elim(p_thm)
        .expect("not_elim: imp_elim")
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
    use crate::HolLightCtx;

    fn ctx() -> HolLightCtx {
        HolLightCtx::new()
    }

    #[test]
    fn truth_is_provable_and_axiom_free() {
        let t = truth();
        assert!(t.hyps().is_empty(), "TRUTH must be axiom-free");
        assert_eq!(t.concl(), &Term::bool_lit(true));
    }

    #[test]
    fn and_rules_are_axiom_free() {
        // and_intro of two axiom-free truths is itself axiom-free —
        // the whole point of deriving rather than postulating.
        let conj = and_intro(truth(), truth());
        assert!(conj.hyps().is_empty(), "derived ∧-intro adds no hyps");
        assert!(and_elim_l(conj.clone()).hyps().is_empty());
        assert!(and_elim_r(conj).hyps().is_empty());
    }

    #[test]
    fn kernel_methods_match_derivations() {
        // The fast kernel constructors must agree with the witness
        // derivations in this module — this is the soundness link and
        // the seed of a "paranoid mode".
        let p = Thm::assume(Term::bool_lit(true)).unwrap();
        let q = Thm::assume(Term::bool_lit(true)).unwrap();

        // ∧-intro
        let derived = and_intro(p.clone(), q.clone());
        let fast = p.clone().and_intro(q.clone()).unwrap();
        assert_eq!(derived.concl(), fast.concl());

        // ∧-elim (both projections)
        assert_eq!(
            and_elim_l(derived.clone()).concl(),
            fast.clone().and_elim_l().unwrap().concl()
        );
        assert_eq!(
            and_elim_r(derived).concl(),
            fast.and_elim_r().unwrap().concl()
        );

        // ¬-intro / ¬-elim via `(0=1) ⟹ F`
        let imp_f = {
            let zero_eq_one = ctx()
                .mk_eq(
                    Term::nat_lit(covalence_types::Nat::zero()),
                    Term::nat_lit(covalence_types::Nat::one()),
                )
                .unwrap();
            let to_false = Thm::reduce_prim(zero_eq_one.clone()).unwrap();
            crate::proofs::rewrite::rewrite_with(
                Thm::assume(zero_eq_one.clone()).unwrap(),
                to_false,
            )
            .imp_intro(&zero_eq_one)
            .unwrap()
        };
        assert_eq!(
            not_intro(imp_f.clone()).concl(),
            imp_f.not_intro().unwrap().concl()
        );
    }

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
