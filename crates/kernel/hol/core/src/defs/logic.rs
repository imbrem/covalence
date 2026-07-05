//! The propositional connectives and quantifiers, as ordinary
//! `defs/` definitions over the two logical primitives `=`
//! ([`crate::TermKind::Eq`]) and `ε` ([`crate::TermKind::Select`]).
//!
//! This is the HOL Light bootstrap (`bool.ml`) expressed in the
//! catalogue: every connective is a let-style [`TermSpec`] whose body
//! is the standard definition. Two consequences follow for free:
//!
//! - [`crate::Thm::unfold_term_spec`] hands back the defining equation
//!   `⊢ c = <body>` — the same way it does for `natAdd` — so the
//!   connectives' introduction / elimination rules are *derived*
//!   downstream, never postulated.
//! - the certificate path evaluates a connective applied to `bool`
//!   literals by pointer-match on the spec handle, exactly like closed
//!   arithmetic.
//!
//! `T` / `F` remain `TermKind::Bool` literals; `⊢ T` is derivable via
//! the `LitEqCert` certificate, and the literals' distinctness is the
//! kernel's denotational commitment.
//!
//! ## Definition order
//!
//! The bodies reference each other, so the `LazyLock`s force in
//! dependency order (acyclic):
//!
//! ```text
//! and, forall  ←  (=, T)         (no connective deps)
//! imp          ←  and
//! not          ←  imp, F
//! or, exists   ←  forall, imp
//! iff          ←  (=)
//! ```
//!
//! Since stage L2 NO kernel rule destructures these definitions — the
//! connective / quantifier intro-elim rules are executable derivations
//! in `covalence-hol-eval::derived`. The staying axiom rules
//! (`succ_inj`, `select_ax`, `spec_ax`, the `spec_*` subtype laws,
//! `new_type_definition`) still *state* their conclusions with `imp` /
//! `not` / `or` / `exists` / `and` / `forall`, and the D3 residue type
//! catalogue quantifies with them — which is exactly why these
//! definitions are still core residue rather than eval catalogue: they
//! move out with the literal-leaf endgame (see `SKELETONS.md`).

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;

// ============================================================================
// Helpers
// ============================================================================

fn b() -> Type {
    Type::bool()
}

fn t_lit() -> Term {
    Term::bool_lit(true)
}

fn f_lit() -> Term {
    Term::bool_lit(false)
}

/// `p ⟹ q` built from the `imp` spec (for use inside the bodies that
/// need implication before `hol::hol_imp` would be circular-safe).
fn imp_app(p: Term, q: Term) -> Term {
    Term::app(Term::app(imp(), p), q)
}

// ============================================================================
// and — `λp q. (λf. f p q) = (λf. f T T)`
// ============================================================================

fn and_body() -> Term {
    // `f : bool → bool → bool`
    let bbb = Type::fun(b(), Type::fun(b(), b()));
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let f = Term::free("f", bbb.clone());

    // λf. f p q
    let f_p_q = Term::app(Term::app(f.clone(), p.clone()), q.clone());
    let lhs = hol::pub_abs("f", bbb.clone(), f_p_q);
    // λf. f T T
    let f_t_t = Term::app(Term::app(f, t_lit()), t_lit());
    let rhs = hol::pub_abs("f", bbb, f_t_t);

    let eq = hol::hol_eq(lhs, rhs);
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), eq))
}

let_term! {
    /// `(/\) : bool → bool → bool` ≡ `λp q. (λf. f p q) = (λf. f T T)`.
    and_spec, and, Canonical::And, and_body()
}

// ============================================================================
// imp — `λp q. (p /\ q) = p`
// ============================================================================

fn imp_body() -> Term {
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let and_pq = Term::app(Term::app(and(), p.clone()), q.clone());
    let eq = hol::hol_eq(and_pq, p.clone());
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), eq))
}

let_term! {
    /// `(==>) : bool → bool → bool` ≡ `λp q. (p /\ q) = p`.
    imp_spec, imp, Canonical::Imp, imp_body()
}

// ============================================================================
// not — `λp. p ==> F`
// ============================================================================

fn not_body() -> Term {
    let p = Term::free("p", b());
    let body = imp_app(p.clone(), f_lit());
    hol::pub_abs("p", b(), body)
}

let_term! {
    /// `(~) : bool → bool` ≡ `λp. p ==> F`.
    not_spec, not, Canonical::Not, not_body()
}

// ============================================================================
// iff — `λp q. p = q`
// ============================================================================

fn iff_body() -> Term {
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let eq = hol::hol_eq(p.clone(), q.clone());
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), eq))
}

let_term! {
    /// `(<=>) : bool → bool → bool` ≡ `λp q. p = q`.
    iff_spec, iff, Canonical::Iff, iff_body()
}

// ============================================================================
// forall — `λP. P = (λx. T)`
// ============================================================================

fn forall_body() -> Term {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), b());
    let pred = Term::free("P", pred_ty.clone());
    // λx:α. T  (x unused; `pub_abs` close is a no-op but keeps shape)
    let lam_x = hol::pub_abs("x", alpha, t_lit());
    let eq = hol::hol_eq(pred, lam_x);
    hol::pub_abs("P", pred_ty, eq)
}

poly_let_term! {
    /// `(!) : ('a → bool) → bool` ≡ `λP. P = (λx. T)`.
    forall_spec, forall(alpha), Canonical::Forall, forall_body()
}

// ============================================================================
// or — `λp q. !r. (p ==> r) ==> (q ==> r) ==> r`
// ============================================================================

fn or_body() -> Term {
    let p = Term::free("p", b());
    let q = Term::free("q", b());
    let r = Term::free("r", b());
    let p_r = imp_app(p.clone(), r.clone());
    let q_r = imp_app(q.clone(), r.clone());
    let inner = imp_app(p_r, imp_app(q_r, r.clone()));
    let forall_r = hol::hol_forall("r", b(), inner);
    hol::pub_abs("p", b(), hol::pub_abs("q", b(), forall_r))
}

let_term! {
    /// `(\/) : bool → bool → bool` ≡
    /// `λp q. !r. (p ==> r) ==> (q ==> r) ==> r`.
    or_spec, or, Canonical::Or, or_body()
}

// ============================================================================
// exists — `λP. !q. (!x. P x ==> q) ==> q`
// ============================================================================

fn exists_body() -> Term {
    let alpha = Type::tfree("a");
    let pred_ty = Type::fun(alpha.clone(), b());
    let pred = Term::free("P", pred_ty.clone());
    let q = Term::free("q", b());
    let x = Term::free("x", alpha.clone());
    let p_x = Term::app(pred.clone(), x);
    let p_x_q = imp_app(p_x, q.clone());
    let inner_forall = hol::hol_forall("x", alpha, p_x_q);
    let imp2 = imp_app(inner_forall, q.clone());
    let forall_q = hol::hol_forall("q", b(), imp2);
    hol::pub_abs("P", pred_ty, forall_q)
}

poly_let_term! {
    /// `(?) : ('a → bool) → bool` ≡ `λP. !q. (!x. P x ==> q) ==> q`.
    exists_spec, exists(alpha), Canonical::Exists, exists_body()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TermKind;

    /// Pin the pure tier: `Thm<CoreLang>` unit tests (stage E1).
    type Thm = crate::Thm;

    fn bin() -> Type {
        Type::fun(b(), Type::fun(b(), b()))
    }

    #[test]
    fn connectives_have_expected_types() {
        assert_eq!(and().type_of().unwrap(), bin());
        assert_eq!(or().type_of().unwrap(), bin());
        assert_eq!(imp().type_of().unwrap(), bin());
        assert_eq!(iff().type_of().unwrap(), bin());
        assert_eq!(not().type_of().unwrap(), Type::fun(b(), b()));
        // `!` / `?` at α: (α → bool) → bool.
        let a = Type::tfree("x");
        let quant = Type::fun(Type::fun(a.clone(), b()), b());
        assert_eq!(forall(a.clone()).type_of().unwrap(), quant);
        assert_eq!(exists(a).type_of().unwrap(), quant);
    }

    /// The whole point of making the connectives `defs/` specs: each
    /// one unfolds to its standard definition via `unfold_term_spec`
    /// — no postulate, sound by the let-style denotation. This is the
    /// hook downstream `covalence-hol` uses to *derive* the connective
    /// rules.
    #[test]
    fn connectives_unfold_to_their_definitions() {
        for op in [and(), or(), imp(), iff(), not()] {
            let thm = Thm::unfold_term_spec(op.clone()).unwrap();
            // `⊢ op = <body>`: empty hyps, conclusion is an equation
            // whose LHS is the connective itself.
            assert!(thm.hyps().is_empty(), "unfold must be axiom-free");
            let TermKind::App(eq_lhs, _body) = thm.concl().kind() else {
                panic!("unfold concl not an application: {:?}", thm.concl());
            };
            let TermKind::App(eq_head, lhs) = eq_lhs.kind() else {
                panic!("unfold concl LHS not an application");
            };
            assert!(matches!(eq_head.kind(), TermKind::Eq(_)));
            assert_eq!(lhs, &op);
        }
    }

    #[test]
    fn polymorphic_connectives_unfold() {
        for op in [forall(Type::nat()), exists(Type::nat())] {
            let thm = Thm::unfold_term_spec(op.clone()).unwrap();
            assert!(thm.hyps().is_empty());
            let TermKind::App(eq_lhs, _body) = thm.concl().kind() else {
                panic!("unfold concl not an application");
            };
            let TermKind::App(eq_head, lhs) = eq_lhs.kind() else {
                panic!("unfold concl LHS not an application");
            };
            assert!(matches!(eq_head.kind(), TermKind::Eq(_)));
            assert_eq!(lhs, &op);
        }
    }
}
