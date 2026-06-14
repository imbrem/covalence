//! `option 'a := coprod 'a unit` + constructors + eliminator.
//!
//! `option α` is an opaque newtype wrapper over `coprod α unit`. Its
//! constructors and eliminator are *defined* (not declaration-only)
//! in terms of the `coprod` injections/eliminator plus the spec
//! abstraction/representation coercions ([`Term::spec_abs`] /
//! [`Term::spec_rep`]):
//!
//! ```text
//!     some a       ≔ abs (inl a)
//!     none         ≔ abs (inr unit)
//!     optionCase d f o ≔ coprodCase f (λ_. d) (rep o)
//!     isSome o     ≔ coprodCase (λ_. T) (λ_. F) (rep o)
//!     fromSome o   ≔ coprodCase (λx. x) (λ_. ε(λx. T)) (rep o)
//! ```
//!
//! The characterizing equations
//!
//! ```text
//!     optionCase d f none      = d
//!     optionCase d f (some x)  = f x
//!     isSome none              = F      isSome (some x)   = T
//!     fromSome (some x)        = x      (fromSome none = ε, unspecified)
//! ```
//!
//! are **theorems** about these definitions (provable downstream in
//! `covalence-hol` from the abs/rep bijection + the `coprodCase`
//! equations), not postulates.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::coprod::{coprod, coprod_case, inl, inr};
use super::spec::{TermSpec, TypeSpec};
use super::unit::unit_nil;

/// `option 'a := coprod 'a unit`. Opaque newtype wrapper: its carrier
/// is `coprod α unit` and the predicate is trivially true, so
/// `option α` and `coprod α unit` have the same inhabitants — but they
/// are distinct types at the kernel-rule level (different `Canonical`
/// labels, distinct `Arc` identity, distinct `Spec` leaves). Cross the
/// boundary with `abs`/`rep` ([`Term::spec_abs`] / [`Term::spec_rep`]),
/// as the constructors below do.
pub fn option_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let carrier = coprod(alpha, Type::unit());
        TypeSpec::newtype(Canonical::Option, carrier)
    });
    LAZY.clone()
}
pub fn option(alpha: Type) -> Type {
    Type::spec(option_spec(), vec![alpha])
}

// ============================================================================
// Constructors
// ============================================================================

fn none_body() -> Term {
    let alpha = Type::tfree("a");
    // inr unit.nil : coprod α unit
    let inr_u = Term::app(inr(alpha.clone(), Type::unit()), unit_nil());
    let abs = Term::spec_abs(option_spec(), vec![alpha]);
    Term::app(abs, inr_u)
}

poly_let_term! {
    /// `none : option 'a` ≡ `abs (inr unit)`.
    none_spec, none(alpha), Canonical::None, none_body()
}

fn some_body() -> Term {
    let alpha = Type::tfree("a");
    let a = Term::free("a", alpha.clone());
    // inl a : coprod α unit
    let inl_a = Term::app(inl(alpha.clone(), Type::unit()), a);
    let abs = Term::spec_abs(option_spec(), vec![alpha.clone()]);
    let applied = Term::app(abs, inl_a);
    hol::pub_abs("a", alpha, applied)
}

poly_let_term! {
    /// `some : 'a → option 'a` ≡ `λa. abs (inl a)`.
    some_spec, some(alpha), Canonical::Some, some_body()
}

// ============================================================================
// Eliminator + accessors
// ============================================================================

fn option_case_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let f_ty = Type::fun(alpha.clone(), beta.clone());

    let d = Term::free("d", beta.clone());
    let f = Term::free("f", f_ty.clone());
    let o = Term::free("o", option(alpha.clone()));

    let rep_o = Term::app(Term::spec_rep(option_spec(), vec![alpha.clone()]), o);
    // λ_:unit. d  — the none branch ignores its (unit) argument.
    let g = Term::abs("_", Type::unit(), d.clone());
    let case = coprod_case(alpha.clone(), Type::unit(), beta.clone());
    let applied = Term::app(Term::app(Term::app(case, f.clone()), g), rep_o);

    let lam_o = hol::pub_abs("o", option(alpha.clone()), applied);
    let lam_f = hol::pub_abs("f", f_ty, lam_o);
    hol::pub_abs("d", beta, lam_f)
}

/// `optionCase : 'b → ('a → 'b) → option 'a → 'b` ≡
/// `λd f o. coprodCase f (λ_. d) (rep o)`. The fundamental
/// eliminator. The spec is parametric in `α` then `β` (alphabetical
/// `free_tvars()` order).
pub fn option_case_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = option_case_body();
        let ty = body.type_of().expect("optionCase body type-checks");
        TermSpec::new(Canonical::OptionCase, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `optionCase α β : β → (α → β) → option α → β`.
pub fn option_case(alpha: Type, beta: Type) -> Term {
    Term::term_spec(option_case_spec(), vec![alpha, beta])
}

fn is_some_body() -> Term {
    let alpha = Type::tfree("a");
    let o = Term::free("o", option(alpha.clone()));
    let rep_o = Term::app(Term::spec_rep(option_spec(), vec![alpha.clone()]), o);
    let f = Term::abs("_", alpha.clone(), Term::bool_lit(true)); // some _ ↦ T
    let g = Term::abs("_", Type::unit(), Term::bool_lit(false)); // none  ↦ F
    let case = coprod_case(alpha.clone(), Type::unit(), Type::bool());
    let applied = Term::app(Term::app(Term::app(case, f), g), rep_o);
    hol::pub_abs("o", option(alpha), applied)
}

poly_let_term! {
    /// `isSome : option 'a → bool` ≡
    /// `λo. coprodCase (λ_. T) (λ_. F) (rep o)`. True iff `some _`.
    is_some_spec, is_some(alpha), Canonical::IsSome, is_some_body()
}

fn from_some_body() -> Term {
    let alpha = Type::tfree("a");
    let o = Term::free("o", option(alpha.clone()));
    let rep_o = Term::app(Term::spec_rep(option_spec(), vec![alpha.clone()]), o);
    // some-branch: identity λx. x
    let f = hol::pub_abs("x", alpha.clone(), Term::free("x", alpha.clone()));
    // none-branch: the unspecified canonical ε(λx. T), ignoring unit.
    let arb = Term::app(
        Term::select_op(alpha.clone()),
        Term::abs("x", alpha.clone(), Term::bool_lit(true)),
    );
    let g = Term::abs("_", Type::unit(), arb);
    let case = coprod_case(alpha.clone(), Type::unit(), alpha.clone());
    let applied = Term::app(Term::app(Term::app(case, f), g), rep_o);
    hol::pub_abs("o", option(alpha), applied)
}

poly_let_term! {
    /// `fromSome : option 'a → 'a` ≡
    /// `λo. coprodCase (λx. x) (λ_. ε(λx. T)) (rep o)`. Extract the
    /// wrapped value if `some _`; for `none`, the Hilbert-ε value
    /// (unspecified at the kernel level).
    from_some_spec, from_some(alpha), Canonical::FromSome, from_some_body()
}
