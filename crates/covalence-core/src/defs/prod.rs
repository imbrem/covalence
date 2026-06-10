//! `prod 'a 'b` + `signed1 'a` / `signed2 'a`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::coprod::bit_ty;

/// Build the prod predicate at concrete carriers α, β:
/// `λR. ∃a b. R = λx y. (x = a ∧ y = b)`.
pub(super) fn prod_predicate_at(alpha: Type, beta: Type) -> Term {
    let rel_ty = Type::fun(alpha.clone(), Type::fun(beta.clone(), Type::bool()));
    let r = Term::free("R", rel_ty.clone());

    let body = {
        let a_free = Term::free("a", alpha.clone());
        let b_free = Term::free("b", beta.clone());
        let x_free = Term::free("x", alpha.clone());
        let y_free = Term::free("y", beta.clone());
        let eq_x_a = hol::hol_eq(x_free, a_free);
        let eq_y_b = hol::hol_eq(y_free, b_free);
        let conj = hol::hol_and(eq_x_a, eq_y_b);
        let lam_y = hol::pub_abs("y", beta.clone(), conj);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        let inner_exists = hol::hol_exists("b", beta.clone(), r_eq);
        hol::hol_exists("a", alpha.clone(), inner_exists)
    };

    hol::pub_abs("R", rel_ty, body)
}

fn prod_predicate() -> Term {
    prod_predicate_at(Type::tfree("a"), Type::tfree("b"))
}

static PROD_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Prod,
        ty: Some(carrier),
        tm: Some(prod_predicate()),
    })
});

/// `prod 'a 'b := rel 'a 'b where (∃a b. R = λx y. x = a ∧ y = b)`.
pub fn prod_spec() -> TypeSpecHandle {
    PROD_LAZY.clone()
}
pub fn prod(alpha: Type, beta: Type) -> Type {
    Type::spec(prod_spec(), vec![alpha, beta])
}

// ============================================================================
// signed1 / signed2
// ============================================================================

fn build_signed_spec(symbol: Canonical) -> TypeSpecHandle {
    let alpha = Type::tfree("a");
    let bit_t = bit_ty();
    let carrier = Type::fun(bit_t.clone(), Type::fun(alpha.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(prod_predicate_at(bit_t, alpha)),
    })
}

static SIGNED1_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| build_signed_spec(Canonical::Signed1));
static SIGNED2_LAZY: LazyLock<TypeSpecHandle> =
    LazyLock::new(|| build_signed_spec(Canonical::Signed2));

/// `signed1 'a := prod bit 'a` — value + sign bit.
pub fn signed1_spec() -> TypeSpecHandle {
    SIGNED1_LAZY.clone()
}
pub fn signed1(alpha: Type) -> Type {
    Type::spec(signed1_spec(), vec![alpha])
}
/// `signed2 'a := prod bit 'a` — two's-complement-style.
pub fn signed2_spec() -> TypeSpecHandle {
    SIGNED2_LAZY.clone()
}
pub fn signed2(alpha: Type) -> Type {
    Type::spec(signed2_spec(), vec![alpha])
}
