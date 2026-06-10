//! `result 'a 'b` constructors: `ok` / `err`.
//!
//! The `result` type itself is defined in [`super::coprod`] as
//! `coprod 'a 'b`. This module just adds the term-level
//! constructors so users can build `ok x : result α β` and
//! `err e : result α β` directly.

use std::sync::LazyLock;

use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::coprod::result;
use super::spec::TermSpec;

/// `ok : 'a → result 'a 'b`.
pub fn ok_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        TermSpec::new(
            Canonical::Ok,
            Some(Type::fun(alpha.clone(), result(alpha, beta))),
            None,
        )
    });
    LAZY.clone()
}
pub fn ok(alpha: Type, beta: Type) -> Term {
    Term::term_spec(ok_spec(), vec![alpha, beta])
}

/// `err : 'b → result 'a 'b`.
pub fn err_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        TermSpec::new(
            Canonical::Err,
            Some(Type::fun(beta.clone(), result(alpha, beta))),
            None,
        )
    });
    LAZY.clone()
}
pub fn err(alpha: Type, beta: Type) -> Term {
    Term::term_spec(err_spec(), vec![alpha, beta])
}
