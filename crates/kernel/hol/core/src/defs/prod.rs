//! `prod 'a 'b` + `signed1 'a` / `signed2 'a`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::bits::bit_ty;
use super::canonical::Canonical;
use super::logic;
use super::spec::{TermSpec, TypeSpec};

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
        let conj = logic::hol_and(eq_x_a, eq_y_b);
        let lam_y = hol::pub_abs("y", beta.clone(), conj);
        let lam_xy = hol::pub_abs("x", alpha.clone(), lam_y);
        let r_eq = hol::hol_eq(r.clone(), lam_xy);
        let inner_exists = logic::hol_exists("b", beta.clone(), r_eq);
        logic::hol_exists("a", alpha.clone(), inner_exists)
    };

    hol::pub_abs("R", rel_ty, body)
}

fn prod_predicate() -> Term {
    prod_predicate_at(Type::tfree("a"), Type::tfree("b"))
}

/// `prod 'a 'b := rel 'a 'b where (∃a b. R = λx y. x = a ∧ y = b)`.
pub fn prod_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| {
        let alpha = Type::tfree("a");
        let beta = Type::tfree("b");
        let carrier = Type::fun(alpha, Type::fun(beta, Type::bool()));
        TypeSpec::subtype(Canonical::Prod, carrier, prod_predicate())
    });
    LAZY.clone()
}
pub fn prod(alpha: Type, beta: Type) -> Type {
    Type::spec(prod_spec(), vec![alpha, beta])
}

fn build_signed_spec(symbol: Canonical) -> TypeSpec {
    let alpha = Type::tfree("a");
    let bit_t = bit_ty();
    let carrier = Type::fun(bit_t.clone(), Type::fun(alpha.clone(), Type::bool()));
    TypeSpec::subtype(symbol, carrier, prod_predicate_at(bit_t, alpha))
}

/// `signed1 'a := prod bit 'a`.
pub fn signed1_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| build_signed_spec(Canonical::Signed1));
    LAZY.clone()
}
pub fn signed1(alpha: Type) -> Type {
    Type::spec(signed1_spec(), vec![alpha])
}
/// `signed2 'a := prod bit 'a` — two's-complement-style.
pub fn signed2_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| build_signed_spec(Canonical::Signed2));
    LAZY.clone()
}
pub fn signed2(alpha: Type) -> Type {
    Type::spec(signed2_spec(), vec![alpha])
}

// ============================================================================
// pair / fst / snd — constructor and projections
//
// A `prod α β` value is the abstraction of the "singleton relation"
// `λx y. x = a ∧ y = b`. So:
//
//   pair a b ≔ abs (λx y. x = a ∧ y = b)
//   fst p    ≔ ε(λa. ∃b. rep p = λx y. x = a ∧ y = b)
//   snd p    ≔ ε(λb. ∃a. rep p = λx y. x = a ∧ y = b)
//
// The projection equations `fst (pair a b) = a`, `snd (pair a b) = b`
// are theorems (provable downstream from the abs/rep bijection plus
// the carrier predicate), not committed here.
// ============================================================================

/// `λx y. x = a ∧ y = b` — the carrier relation a `pair a b` abstracts.
fn pair_rel(a: Term, b: Term, alpha: Type, beta: Type) -> Term {
    let x = Term::free("x", alpha.clone());
    let y = Term::free("y", beta.clone());
    let conj = logic::hol_and(hol::hol_eq(x, a), hol::hol_eq(y, b));
    let lam_y = hol::pub_abs("y", beta, conj);
    hol::pub_abs("x", alpha, lam_y)
}

fn pair_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let a = Term::free("a", alpha.clone());
    let b = Term::free("b", beta.clone());
    let rel = pair_rel(a, b, alpha.clone(), beta.clone());
    let abs = Term::spec_abs(prod_spec(), vec![alpha.clone(), beta.clone()]);
    let applied = Term::app(abs, rel);
    let lam_b = hol::pub_abs("b", beta, applied);
    hol::pub_abs("a", alpha, lam_b)
}

/// `pair : 'a → 'b → prod 'a 'b` ≡ `λa b. abs (λx y. x = a ∧ y = b)`.
pub fn pair_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = pair_body();
        let ty = body.type_of().expect("pair body type-checks");
        TermSpec::new(Canonical::Pair, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `pair α β : α → β → prod α β`.
pub fn pair(alpha: Type, beta: Type) -> Term {
    Term::term_spec(pair_spec(), vec![alpha, beta])
}

/// Body of `fst`/`snd`: `λp. ε(λsel. ∃other. rep p = pairRel …)`. The
/// boolean `select_first` picks which component the ε ranges over.
fn projection_body(select_first: bool) -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let prod_ab = prod(alpha.clone(), beta.clone());
    let p = Term::free("p", prod_ab.clone());
    let rep = Term::spec_rep(prod_spec(), vec![alpha.clone(), beta.clone()]);
    let rep_p = Term::app(rep, p);
    let rel = pair_rel(
        Term::free("a", alpha.clone()),
        Term::free("b", beta.clone()),
        alpha.clone(),
        beta.clone(),
    );
    let eq = hol::hol_eq(rep_p, rel);
    let (sel_name, sel_ty, other_name, other_ty) = if select_first {
        ("a", alpha.clone(), "b", beta.clone())
    } else {
        ("b", beta.clone(), "a", alpha.clone())
    };
    let ex_other = logic::hol_exists(other_name, other_ty, eq);
    let sel = hol::pub_abs(sel_name, sel_ty.clone(), ex_other);
    let eps = Term::app(Term::select_op(sel_ty), sel);
    hol::pub_abs("p", prod_ab, eps)
}

/// `fst : prod 'a 'b → 'a` ≡ `λp. ε(λa. ∃b. rep p = λx y. x = a ∧ y = b)`.
pub fn fst_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = projection_body(true);
        let ty = body.type_of().expect("fst body type-checks");
        TermSpec::new(Canonical::Fst, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `fst α β : prod α β → α`.
pub fn fst(alpha: Type, beta: Type) -> Term {
    Term::term_spec(fst_spec(), vec![alpha, beta])
}

/// `snd : prod 'a 'b → 'b` ≡ `λp. ε(λb. ∃a. rep p = λx y. x = a ∧ y = b)`.
pub fn snd_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = projection_body(false);
        let ty = body.type_of().expect("snd body type-checks");
        TermSpec::new(Canonical::Snd, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `snd α β : prod α β → β`.
pub fn snd(alpha: Type, beta: Type) -> Term {
    Term::term_spec(snd_spec(), vec![alpha, beta])
}
