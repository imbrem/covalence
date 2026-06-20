//! `result 'a 'b := coprod 'a 'b` + constructors `ok` / `err`.
//!
//! **Source of truth: [`core.cov`](super::cov).** The `result` newtype
//! and its `ok`/`err` constructors live as directives in
//! `defs/core.cov`; the accessors below are thin lookups into
//! [`super::cov::core_env`].
//!
//! The `result` type is a newtype over `coprod 'a 'b`; its constructors
//! are *defined* via the `coprod` injections plus the spec abstraction
//! coercion:
//!
//! ```text
//!     ok a  ≔ abs (inl a)        err e ≔ abs (inr e)
//! ```

use crate::term::{Term, Type};

use super::cov::core_env;
use super::spec::{TermSpec, TypeSpec};

fn term_spec(label: &str) -> TermSpec {
    core_env()
        .term_spec(label)
        .unwrap_or_else(|| panic!("core.cov must define `{label}`"))
        .clone()
}

/// `result 'a 'b := coprod 'a 'b` — WASM component-model result. Just
/// a distinct *symbol* whose carrier is `coprod 'a 'b`; the disjoint-
/// union structure is `coprod`'s, not duplicated here. Cross the
/// newtype boundary with `abs`/`rep`, as `ok`/`err` do.
pub fn result_spec() -> TypeSpec {
    core_env()
        .type_spec("result")
        .expect("core.cov must define `result`")
        .clone()
}
pub fn result(alpha: Type, beta: Type) -> Type {
    Type::spec(result_spec(), vec![alpha, beta])
}

/// `ok : 'a → result 'a 'b` ≡ `λa. abs (inl a)`.
pub fn ok_spec() -> TermSpec {
    term_spec("result.ok")
}
pub fn ok(alpha: Type, beta: Type) -> Term {
    Term::term_spec(ok_spec(), vec![alpha, beta])
}

/// `err : 'b → result 'a 'b` ≡ `λe. abs (inr e)`.
pub fn err_spec() -> TermSpec {
    term_spec("result.err")
}
pub fn err(alpha: Type, beta: Type) -> Term {
    Term::term_spec(err_spec(), vec![alpha, beta])
}
