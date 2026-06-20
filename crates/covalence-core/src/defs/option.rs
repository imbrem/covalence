//! `option 'a := coprod 'a unit` + constructors + eliminator.
//!
//! **Source of truth: [`core.cov`](super::cov).** `option` and its
//! `none`/`some`/`option.case`/`isSome`/`unwrap` definitions live as
//! directives in `defs/core.cov`; the accessors below are thin lookups
//! into [`super::cov::core_env`].
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
//!     isSome o     ≔ optionCase F (λ_. T) o
//!     unwrap o     ≔ optionCase fail (λx. x) o
//! ```
//!
//! The characterizing equations
//!
//! ```text
//!     optionCase d f none      = d
//!     optionCase d f (some x)  = f x
//!     isSome none              = F      isSome (some x)   = T
//!     unwrap (some x)          = x      (unwrap none = fail, unspecified)
//! ```
//!
//! are **theorems** about these definitions (provable downstream in
//! `covalence-hol` from the abs/rep bijection + the `coprodCase`
//! equations), not postulates.

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::{TermSpec, TypeSpec};

fn term_spec(label: &str) -> TermSpec {
    core_env()
        .term_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `option 'a := coprod 'a unit`. Opaque newtype wrapper: its carrier
/// is `coprod α unit` and the predicate is trivially true, so
/// `option α` and `coprod α unit` have the same inhabitants — but they
/// are distinct types at the kernel-rule level (different labels,
/// distinct `Arc` identity, distinct `Spec` leaves). Cross the boundary
/// with `abs`/`rep` ([`Term::spec_abs`] / [`Term::spec_rep`]), as the
/// constructors do.
pub fn option_spec() -> TypeSpec {
    core_env()
        .type_spec("option")
        .expect("core.cov must define `option`")
        .clone()
}
pub fn option(alpha: Type) -> Type {
    Type::spec(option_spec(), vec![alpha])
}

/// `none : option 'a` ≡ `abs (inr unit)`.
pub fn none_spec() -> TermSpec {
    term_spec("option.none")
}
/// `none α : option α`.
pub fn none(alpha: Type) -> Term {
    Term::term_spec(none_spec(), vec![alpha])
}

/// `some : 'a → option 'a` ≡ `λa. abs (inl a)`.
pub fn some_spec() -> TermSpec {
    term_spec("option.some")
}
/// `some α : α → option α`.
pub fn some(alpha: Type) -> Term {
    Term::term_spec(some_spec(), vec![alpha])
}

/// `optionCase : 'b → ('a → 'b) → option 'a → 'b` ≡
/// `λd f o. coprodCase f (λ_. d) (rep o)`. The fundamental eliminator.
/// The spec is parametric in `α` then `β` (alphabetical `free_tvars()`
/// order).
pub fn option_case_spec() -> TermSpec {
    term_spec("option.case")
}
/// `optionCase α β : β → (α → β) → option α → β`.
pub fn option_case(alpha: Type, beta: Type) -> Term {
    Term::term_spec(option_case_spec(), vec![alpha, beta])
}

/// `isSome : option 'a → bool` ≡ `λo. optionCase F (λ_. T) o`. True iff
/// `some _`.
pub fn is_some_spec() -> TermSpec {
    term_spec("option.isSome")
}
/// `isSome α : option α → bool`.
pub fn is_some(alpha: Type) -> Term {
    Term::term_spec(is_some_spec(), vec![alpha])
}

/// `unwrap : option 'a → 'a` ≡ `λo. optionCase fail (λx. x) o`. Extract
/// the wrapped value if `some _`; for `none`, the unspecified `fail`
/// value.
pub fn unwrap_spec() -> TermSpec {
    term_spec("option.unwrap")
}
/// `unwrap α : option α → α`.
pub fn unwrap(alpha: Type) -> Term {
    Term::term_spec(unwrap_spec(), vec![alpha])
}
