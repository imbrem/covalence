//! The propositional connectives and quantifiers, as ordinary
//! `defs/` definitions over the two logical primitives `=`
//! ([`crate::TermKind::Eq`]) and `ε` ([`crate::TermKind::Select`]).
//!
//! **Source of truth: [`core.cov`](super::cov).** The defining bodies
//! used to live here as hand-written `λ`-builders; they now live as
//! `(#def …)` directives in `defs/core.cov` and are parsed once into
//! [`super::cov::core_env`]. The accessors below are thin lookups that
//! read the parser-built [`TermSpec`] back out, so there is a single
//! shared `Arc` per connective and every reference (this module, the
//! kernel rules, downstream `covalence-hol`) gets the same object.
//!
//! This is the HOL Light bootstrap (`bool.ml`) expressed in the
//! catalogue: every connective is a let-style [`TermSpec`] whose body
//! is the standard definition. Two consequences follow for free:
//!
//! - [`crate::Thm::unfold_term_spec`] hands back the defining equation
//!   `⊢ c = <body>` — the same way it does for `natAdd` — so the
//!   connectives' introduction / elimination rules are *derived*
//!   downstream, never postulated.
//! - [`crate::Thm::reduce_prim`] evaluates a connective applied to
//!   `bool` literals by pointer-match on the spec handle (see
//!   `builtins::reduce_spec`), exactly like closed arithmetic.
//!
//! `T` / `F` remain `TermKind::Bool` literals; `⊢ T` is derivable via
//! `reduce_prim`, and the literals' distinctness is the kernel's
//! denotational commitment.
//!
//! The `imp_intro` / `imp_elim` / `all_intro` / `all_elim` kernel
//! rules operate on the `imp` / `forall` specs defined here; they
//! remain kernel-provided derived rules (sound by the standard HOL
//! Light derivations) rather than being re-derived from scratch.

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::TermSpec;

// ============================================================================
// Accessors — thin lookups into the parsed `core.cov` catalogue.
//
// Each `*_spec()` reads the `TermSpec` the parser built from the matching
// `(#def bool.xxx …)` directive; each term accessor instantiates its leaf
// at the supplied type arguments. The bodies (and the `Soundness:`-worthy
// HOL Light definitions they encode) live in `defs/core.cov`.
// ============================================================================

/// Fetch a migrated connective's `TermSpec` from `core.cov` by label.
/// Panics only if `core.cov` is missing the entry — a build-time
/// invariant the test suite exercises.
fn spec(label: &str) -> TermSpec {
    core_env()
        .term_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `(/\) : bool → bool → bool` ≡ `λp q. (λf. f p q) = (λf. f T T)`.
pub fn and_spec() -> TermSpec {
    spec("bool.and")
}
/// `(/\) : bool → bool → bool`.
pub fn and() -> Term {
    Term::term_spec(and_spec(), vec![])
}

/// `(==>) : bool → bool → bool` ≡ `λp q. (p /\ q) = p`.
pub fn imp_spec() -> TermSpec {
    spec("bool.imp")
}
/// `(==>) : bool → bool → bool`.
pub fn imp() -> Term {
    Term::term_spec(imp_spec(), vec![])
}

/// `(~) : bool → bool` ≡ `λp. p ==> F`.
pub fn not_spec() -> TermSpec {
    spec("bool.not")
}
/// `(~) : bool → bool`.
pub fn not() -> Term {
    Term::term_spec(not_spec(), vec![])
}

/// `(<=>) : bool → bool → bool` ≡ `λp q. p = q`.
pub fn iff_spec() -> TermSpec {
    spec("bool.iff")
}
/// `(<=>) : bool → bool → bool`.
pub fn iff() -> Term {
    Term::term_spec(iff_spec(), vec![])
}

/// `(\/) : bool → bool → bool` ≡
/// `λp q. !r. (p ==> r) ==> (q ==> r) ==> r`.
pub fn or_spec() -> TermSpec {
    spec("bool.or")
}
/// `(\/) : bool → bool → bool`.
pub fn or() -> Term {
    Term::term_spec(or_spec(), vec![])
}

/// `(!) : ('a → bool) → bool` ≡ `λP. P = (λx. T)`.
pub fn forall_spec() -> TermSpec {
    spec("bool.forall")
}
/// `(!) α : (α → bool) → bool`.
pub fn forall(alpha: Type) -> Term {
    Term::term_spec(forall_spec(), vec![alpha])
}

/// `(?) : ('a → bool) → bool` ≡ `λP. !q. (!x. P x ==> q) ==> q`.
pub fn exists_spec() -> TermSpec {
    spec("bool.exists")
}
/// `(?) α : (α → bool) → bool`.
pub fn exists(alpha: Type) -> Term {
    Term::term_spec(exists_spec(), vec![alpha])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{TermKind, Thm};

    fn b() -> Type {
        Type::bool()
    }

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

    /// Each connective `*_spec()` is the *same* `Arc` every call — it is
    /// the one the parser built from `core.cov`, shared process-wide.
    #[test]
    fn connective_specs_are_shared_singletons() {
        assert!(and_spec().ptr_eq(&and_spec()));
        assert!(forall_spec().ptr_eq(&forall_spec()));
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
