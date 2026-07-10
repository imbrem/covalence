//! `result 'a 'b := coprod 'a 'b` + constructors `ok` / `err`.
//!
//! The `result` type is a newtype over `coprod 'a 'b`; its
//! constructors are *defined* via the `coprod` injections plus the
//! spec abstraction coercion:
//!
//! ```text
//!     ok a  ≔ abs (inl a)        err e ≔ abs (inr e)
//! ```

use std::sync::LazyLock;

use crate::hol;
use covalence_core::term::{Term, Type};

use crate::defs::Canonical;
use crate::defs::{TermSpec, TypeSpec};
use crate::defs::{coprod, inl, inr};

/// `result 'a 'b := coprod 'a 'b` — WASM component-model result. Just
/// a distinct *symbol* whose carrier is `coprod 'a 'b`; the disjoint-
/// union structure is `coprod`'s, not duplicated here. Cross the
/// newtype boundary with `abs`/`rep`, as `ok`/`err` do.
pub fn result_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let carrier = coprod(Type::tfree("a"), Type::tfree("b"));
        TypeSpec::newtype(Canonical::Result, carrier)
    });
    LAZY.clone()
}
pub fn result(alpha: Type, beta: Type) -> Type {
    Type::spec(result_spec(), vec![alpha, beta])
}

fn ok_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let a = Term::free("a", alpha.clone());
    let inl_a = Term::app(inl(alpha.clone(), beta.clone()), a);
    let abs = Term::spec_abs(result_spec(), vec![alpha.clone(), beta.clone()]);
    let applied = Term::app(abs, inl_a);
    hol::pub_abs("a", alpha, applied)
}

/// `ok : 'a → result 'a 'b` ≡ `λa. abs (inl a)`.
pub fn ok_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = ok_body();
        let ty = body.type_of().expect("ok body type-checks");
        TermSpec::new(Canonical::Ok, Some(ty), Some(body))
    });
    LAZY.clone()
}
pub fn ok(alpha: Type, beta: Type) -> Term {
    Term::term_spec(ok_spec(), vec![alpha, beta])
}

fn err_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let e = Term::free("e", beta.clone());
    let inr_e = Term::app(inr(alpha.clone(), beta.clone()), e);
    let abs = Term::spec_abs(result_spec(), vec![alpha.clone(), beta.clone()]);
    let applied = Term::app(abs, inr_e);
    hol::pub_abs("e", beta, applied)
}

/// `err : 'b → result 'a 'b` ≡ `λe. abs (inr e)`.
pub fn err_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = err_body();
        let ty = body.type_of().expect("err body type-checks");
        TermSpec::new(Canonical::Err, Some(ty), Some(body))
    });
    LAZY.clone()
}
pub fn err(alpha: Type, beta: Type) -> Term {
    Term::term_spec(err_spec(), vec![alpha, beta])
}
