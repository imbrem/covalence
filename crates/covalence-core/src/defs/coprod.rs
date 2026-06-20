//! `coprod 'a 'b` (disjoint union) — type, injections, and eliminator.
//!
//! **Source of truth: [`core.cov`](super::cov).** The `coprod` subtype
//! and its `inl`/`inr`/`coprod.case` definitions live as directives in
//! `defs/core.cov`; the accessors below are thin lookups into
//! [`super::cov::core_env`].
//!
//! A `coprod α β` value is the abstraction of one of two **tagged**
//! carrier relations over `α → β → bool → bool`:
//!
//! ```text
//!   left  a := λx y z. z ∧ (x = a)        (discriminator z = T)
//!   right b := λx y z. ¬z ∧ (y = b)       (discriminator z = F)
//!   coprod  := { R | (∃a. R = left a) ∨ (∃b. R = right b) }
//!   inl a   := abs (left a)
//!   inr b   := abs (right b)
//!   coprodCase f g c := ε(λr. (∀a. rep c = left a  ⟹ r = f a)
//!                            ∧ (∀b. rep c = right b ⟹ r = g b))
//! ```
//!
//! The `z : bool` discriminator (`T` left, `F` right) is what keeps the
//! two injections disjoint and each injective for *all* carriers — even
//! singletons like `unit` (without it, `option unit` would identify
//! `some _` with `none`). The computation equations `coprodCase f g
//! (inl a) = f a` and `coprodCase f g (inr b) = g b` are theorems
//! (provable downstream from the abs/rep bijection + the disjoint-union
//! predicate), not committed here.
//!
//! The fixed-width unsigned chain (`bit`, `u2` … `u512`) lives in
//! `super::bits`.

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::{TermSpec, TypeSpec};

fn term_spec(label: &str) -> TermSpec {
    core_env()
        .term_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `coprod 'a 'b := rel 'a 'b where (∃a. R = left a) ∨ (∃b. R = right b)`.
pub fn coprod_spec() -> TypeSpec {
    core_env()
        .type_spec("coprod")
        .expect("core.cov must define `coprod`")
        .clone()
}
pub fn coprod(alpha: Type, beta: Type) -> Type {
    Type::spec(coprod_spec(), vec![alpha, beta])
}

/// `inl : 'a → coprod 'a 'b` ≡ `λa. abs (left a)`.
pub fn inl_spec() -> TermSpec {
    term_spec("coprod.inl")
}
/// `inl α β : α → coprod α β`.
pub fn inl(alpha: Type, beta: Type) -> Term {
    Term::term_spec(inl_spec(), vec![alpha, beta])
}

/// `inr : 'b → coprod 'a 'b` ≡ `λb. abs (right b)`.
pub fn inr_spec() -> TermSpec {
    term_spec("coprod.inr")
}
/// `inr α β : β → coprod α β`.
pub fn inr(alpha: Type, beta: Type) -> Term {
    Term::term_spec(inr_spec(), vec![alpha, beta])
}

/// `coprodCase : ('a → 'c) → ('b → 'c) → coprod 'a 'b → 'c` — the
/// disjoint-union eliminator, defined via Hilbert ε on the matching
/// branch. Equations `coprodCase f g (inl a) = f a` and
/// `coprodCase f g (inr b) = g b` are theorems proved downstream.
pub fn coprod_case_spec() -> TermSpec {
    term_spec("coprod.case")
}
/// `coprodCase α β γ : (α → γ) → (β → γ) → coprod α β → γ`.
pub fn coprod_case(alpha: Type, beta: Type, gamma: Type) -> Term {
    Term::term_spec(coprod_case_spec(), vec![alpha, beta, gamma])
}
