//! `coprod 'a 'b` (disjoint union) + `result 'a 'b` alias. The
//! fixed-width unsigned chain (`bit`, `u2` … `u512`) lives in
//! `super::bits`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::TypeSpec;

/// Build the coprod predicate at concrete carriers α, β.
pub(super) fn coprod_predicate_at(alpha: Type, beta: Type) -> Term {
    let rel_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    let r = Term::free("R", rel_ty.clone());

    let p1 = {
        let a_free = Term::free("a", alpha.clone());
        let x_free = Term::free("x", alpha.clone());
        let inner = hol::hol_eq(x_free, a_free);
        let lam_y = hol::pub_abs("y", beta.clone(), inner);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        hol::hol_exists("a", alpha.clone(), r_eq)
    };
    let p2 = {
        let b_free = Term::free("b", beta.clone());
        let y_free = Term::free("y", beta.clone());
        let inner = hol::hol_eq(y_free, b_free);
        let lam_y = hol::pub_abs("y", beta.clone(), inner);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        hol::hol_exists("b", beta.clone(), r_eq)
    };

    let body = hol::hol_or(p1, p2);
    hol::pub_abs("R", rel_ty, body)
}

fn coprod_predicate() -> Term {
    coprod_predicate_at(Type::tfree("a"), Type::tfree("b"))
}

/// `coprod 'a 'b := rel 'a 'b where (...)` — disjoint union.
pub fn coprod_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
        TypeSpec::subtype(Canonical::Coprod, carrier, coprod_predicate())
    });
    LAZY.clone()
}
pub fn coprod(alpha: Type, beta: Type) -> Type {
    Type::spec(coprod_spec(), vec![alpha, beta])
}
