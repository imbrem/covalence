//! `prod 'a 'b` + `signed1 'a` / `signed2 'a`.
//!
//! **Source of truth: [`core.cov`](super::cov).** The `prod` type and
//! its `pair`/`fst`/`snd` constructors, plus the `signed1`/`signed2`
//! subtypes (`prod bit 'a`-shaped, reusing the product "singleton
//! relation" predicate over a `bit → 'a → bool` carrier), are all
//! `(#subtype …)` / `(#def …)` directives in `defs/core.cov`; the
//! accessors below are thin lookups into [`super::cov::core_env`].

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::{TermSpec, TypeSpec};

fn type_spec(label: &str) -> TypeSpec {
    core_env()
        .type_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `prod 'a 'b := rel 'a 'b where (∃a b. R = λx y. x = a ∧ y = b)`.
/// Sourced from the `(#subtype prod …)` directive in `core.cov`.
pub fn prod_spec() -> TypeSpec {
    type_spec("prod")
}
pub fn prod(alpha: Type, beta: Type) -> Type {
    Type::spec(prod_spec(), vec![alpha, beta])
}

/// `signed1 'a := prod bit 'a`.
pub fn signed1_spec() -> TypeSpec {
    type_spec("signed1")
}
pub fn signed1(alpha: Type) -> Type {
    Type::spec(signed1_spec(), vec![alpha])
}
/// `signed2 'a := prod bit 'a` — two's-complement-style.
pub fn signed2_spec() -> TypeSpec {
    type_spec("signed2")
}
pub fn signed2(alpha: Type) -> Type {
    Type::spec(signed2_spec(), vec![alpha])
}

// ============================================================================
// pair / fst / snd — constructor and projections (sourced from core.cov)
//
// A `prod α β` value is the abstraction of the "singleton relation"
// `λx y. x = a ∧ y = b`. The `(#def prod.pair/fst/snd …)` directives in
// `core.cov` encode:
//
//   pair a b ≔ abs (λx y. x = a ∧ y = b)
//   fst p    ≔ ε(λa. ∃b. rep p = λx y. x = a ∧ y = b)
//   snd p    ≔ ε(λb. ∃a. rep p = λx y. x = a ∧ y = b)
//
// The projection equations `fst (pair a b) = a`, `snd (pair a b) = b`
// are theorems (provable downstream from the abs/rep bijection plus
// the carrier predicate), not committed here.
// ============================================================================

fn term_spec(label: &str) -> TermSpec {
    core_env()
        .term_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `pair : 'a → 'b → prod 'a 'b` ≡ `λa b. abs (λx y. x = a ∧ y = b)`.
pub fn pair_spec() -> TermSpec {
    term_spec("prod.pair")
}
/// `pair α β : α → β → prod α β`.
pub fn pair(alpha: Type, beta: Type) -> Term {
    Term::term_spec(pair_spec(), vec![alpha, beta])
}

/// `fst : prod 'a 'b → 'a` ≡ `λp. ε(λa. ∃b. rep p = λx y. x = a ∧ y = b)`.
pub fn fst_spec() -> TermSpec {
    term_spec("prod.fst")
}
/// `fst α β : prod α β → α`.
pub fn fst(alpha: Type, beta: Type) -> Term {
    Term::term_spec(fst_spec(), vec![alpha, beta])
}

/// `snd : prod 'a 'b → 'b` ≡ `λp. ε(λb. ∃a. rep p = λx y. x = a ∧ y = b)`.
pub fn snd_spec() -> TermSpec {
    term_spec("prod.snd")
}
/// `snd α β : prod α β → β`.
pub fn snd(alpha: Type, beta: Type) -> Term {
    Term::term_spec(snd_spec(), vec![alpha, beta])
}
