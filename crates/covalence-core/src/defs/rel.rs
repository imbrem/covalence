//! `rel 'a 'b` + relation properties (preord, pord, per, part).

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TypeSpec, TypeSpecHandle};
use super::helpers::any;

// ============================================================================
// rel 'a 'b := 'a → 'b → bool
// ============================================================================

static REL_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol: Canonical::Rel,
        ty: Some(carrier.clone()),
        tm: Some(any(&carrier)),
    })
});

/// `rel 'a 'b := 'a → 'b → bool`.
pub fn rel_spec() -> TypeSpecHandle {
    REL_LAZY.clone()
}
/// `rel α β`.
pub fn rel(alpha: Type, beta: Type) -> Type {
    Type::spec(rel_spec(), vec![alpha, beta])
}

// ============================================================================
// Relation properties
// ============================================================================

/// `λR:α→α→bool. ∀x y z. R x y ⟹ R y z ⟹ R x z`.
fn transitive_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let z = Term::free("z", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yz = Term::app(Term::app(r.clone(), y.clone()), z.clone());
    let r_xz = Term::app(Term::app(r.clone(), x.clone()), z.clone());
    let body = hol::hol_imp(r_xy, hol::hol_imp(r_yz, r_xz));
    let all_z = hol::hol_forall("z", alpha.clone(), body);
    let all_yz = hol::hol_forall("y", alpha.clone(), all_z);
    let all_xyz = hol::hol_forall("x", alpha.clone(), all_yz);
    hol::pub_abs("R", r_ty, all_xyz)
}

/// `λR:α→α→bool. ∀x. R x x`.
fn reflexive_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let r_xx = Term::app(Term::app(r.clone(), x.clone()), x);
    let body = hol::hol_forall("x", alpha.clone(), r_xx);
    hol::pub_abs("R", r_ty, body)
}

/// `λR:α→α→bool. ∀x y. R x y ⟹ R y x`.
fn symmetric_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yx = Term::app(Term::app(r.clone(), y.clone()), x.clone());
    let body = hol::hol_imp(r_xy, r_yx);
    let all_y = hol::hol_forall("y", alpha.clone(), body);
    let all_xy = hol::hol_forall("x", alpha.clone(), all_y);
    hol::pub_abs("R", r_ty, all_xy)
}

/// `λR:α→α→bool. ∀x y. R x y ⟹ R y x ⟹ x = y`.
fn antisymmetric_pred(alpha: Type) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", alpha.clone());
    let r_xy = Term::app(Term::app(r.clone(), x.clone()), y.clone());
    let r_yx = Term::app(Term::app(r.clone(), y.clone()), x.clone());
    let x_eq_y = hol::hol_eq(x.clone(), y.clone());
    let body = hol::hol_imp(r_xy, hol::hol_imp(r_yx, x_eq_y));
    let all_y = hol::hol_forall("y", alpha.clone(), body);
    let all_xy = hol::hol_forall("x", alpha.clone(), all_y);
    hol::pub_abs("R", r_ty, all_xy)
}

/// Combine property predicates over `α → α → bool` into a single
/// `λR. ∧ properties`.
fn combine_props(alpha: Type, props: &[fn(Type) -> Term]) -> Term {
    let r_ty = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    let r = Term::free("R", r_ty.clone());
    let mut applications: Vec<Term> = props
        .iter()
        .map(|p| Term::app(p(alpha.clone()), r.clone()))
        .collect();
    let mut result = applications.remove(0);
    for next in applications {
        result = hol::hol_and(result, next);
    }
    hol::pub_abs("R", r_ty, result)
}

fn rel_property_spec(symbol: Canonical, props: &[fn(Type) -> Term]) -> TypeSpecHandle {
    let alpha = Type::tfree("a");
    let carrier = Type::fun(alpha.clone(), Type::fun(alpha.clone(), Type::bool()));
    TypeSpecHandle::new(TypeSpec {
        symbol,
        ty: Some(carrier),
        tm: Some(combine_props(alpha, props)),
    })
}

static PREORD_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(Canonical::Preord, &[transitive_pred, reflexive_pred])
});
static POR_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(
        Canonical::Pord,
        &[transitive_pred, reflexive_pred, antisymmetric_pred],
    )
});
static PER_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(Canonical::Per, &[transitive_pred, symmetric_pred])
});
static PART_LAZY: LazyLock<TypeSpecHandle> = LazyLock::new(|| {
    rel_property_spec(
        Canonical::Part,
        &[transitive_pred, symmetric_pred, reflexive_pred],
    )
});

/// `preord 'a := rel 'a 'a where (transitive ∧ reflexive)`.
pub fn preord_spec() -> TypeSpecHandle {
    PREORD_LAZY.clone()
}
pub fn preord(alpha: Type) -> Type {
    Type::spec(preord_spec(), vec![alpha])
}
/// `pord 'a := rel 'a 'a where (transitive ∧ reflexive ∧ antisymmetric)`.
pub fn pord_spec() -> TypeSpecHandle {
    POR_LAZY.clone()
}
pub fn pord(alpha: Type) -> Type {
    Type::spec(pord_spec(), vec![alpha])
}
/// `per 'a := rel 'a 'a where (transitive ∧ symmetric)`.
pub fn per_spec() -> TypeSpecHandle {
    PER_LAZY.clone()
}
pub fn per(alpha: Type) -> Type {
    Type::spec(per_spec(), vec![alpha])
}
/// `part 'a := rel 'a 'a where (transitive ∧ symmetric ∧ reflexive)`.
pub fn part_spec() -> TypeSpecHandle {
    PART_LAZY.clone()
}
pub fn part(alpha: Type) -> Type {
    Type::spec(part_spec(), vec![alpha])
}
