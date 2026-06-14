//! `coprod 'a 'b` (disjoint union) + `result 'a 'b` alias. The
//! fixed-width unsigned chain (`bit`, `u2` … `u512`) lives in
//! `super::bits`.

use std::sync::LazyLock;

use crate::hol;
use crate::term::{Term, Type};

use super::canonical::Canonical;
use super::spec::{TermSpec, TypeSpec};

/// The carrier relation type `α → β → bool → bool` — a relation on
/// `(α, β)` with an extra `bool` discriminator slot (see [`left_rel`]).
fn coprod_carrier(alpha: Type, beta: Type) -> Type {
    Type::fun(alpha, Type::fun(beta, Type::fun(Type::bool(), Type::bool())))
}

/// Build the coprod predicate at concrete carriers α, β:
/// `λR. (∃a. R = left_rel a) ∨ (∃b. R = right_rel b)`.
pub(super) fn coprod_predicate_at(alpha: Type, beta: Type) -> Term {
    let rel_ty = coprod_carrier(alpha.clone(), beta.clone());
    let r = Term::free("R", rel_ty.clone());

    let p1 = {
        let a_free = Term::free("a", alpha.clone());
        let r_eq = hol::hol_eq(r.clone(), left_rel(a_free, alpha.clone(), beta.clone()));
        hol::hol_exists("a", alpha.clone(), r_eq)
    };
    let p2 = {
        let b_free = Term::free("b", beta.clone());
        let r_eq = hol::hol_eq(r.clone(), right_rel(b_free, alpha.clone(), beta.clone()));
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
        let carrier = coprod_carrier(alpha, beta);
        TypeSpec::subtype(Canonical::Coprod, carrier, coprod_predicate())
    });
    LAZY.clone()
}
pub fn coprod(alpha: Type, beta: Type) -> Type {
    Type::spec(coprod_spec(), vec![alpha, beta])
}

// ============================================================================
// inl / inr / coprodCase — injections and eliminator
//
// A `coprod α β` value is the abstraction of one of two **tagged**
// carrier relations: `λx y z. z ∧ (x = a)` (left, witnessing `a : α`)
// or `λx y z. ¬z ∧ (y = b)` (right, witnessing `b : β`). So:
//
//   inl a ≔ abs (λx y z. z ∧ (x = a))
//   inr b ≔ abs (λx y z. ¬z ∧ (y = b))
//
// The `z : bool` discriminator (`T` left, `F` right) is what keeps the
// two injections disjoint and injective for *all* carriers — without it
// (`λx y. x = a` / `λx y. y = b`) `inl a` and `inr b` collapse to the
// same relation whenever both α and β are singletons, which made e.g.
// `option unit` identify `some _` with `none`. See `left_rel`.
//
// The eliminator is the ε that returns the matching branch:
//
//   coprodCase f g c ≔ ε(λr. (∀a. rep c = leftRel a  ⟹ r = f a)
//                          ∧ (∀b. rep c = rightRel b ⟹ r = g b))
//
// The computation equations `coprodCase f g (inl a) = f a` and
// `coprodCase f g (inr b) = g b` are theorems (provable downstream
// from the abs/rep bijection + the disjoint-union predicate), not
// committed here.
// ============================================================================

/// `λx y z. z ∧ (x = a)` — the left injection's carrier relation (`y`
/// unused). The `z : bool` **discriminator** is `T` on the left; it
/// makes `inl`/`inr` disjoint and each injective *unconditionally* (for
/// any carriers, including singletons like `unit`), which the untagged
/// `λx y. x = a` failed to do — there `inl a = inr b` whenever both
/// carriers were singletons (so `option unit` collapsed `some _` into
/// `none`).
fn left_rel(a: Term, alpha: Type, beta: Type) -> Term {
    let x = Term::free("x", alpha.clone());
    let z = Term::free("z", Type::bool());
    let inner = hol::hol_and(z, hol::hol_eq(x, a)); // z ∧ (x = a)
    let lam_z = hol::pub_abs("z", Type::bool(), inner);
    let lam_yz = hol::pub_abs("y", beta, lam_z);
    hol::pub_abs("x", alpha, lam_yz)
}

/// `λx y z. (¬z) ∧ (y = b)` — the right injection's carrier relation
/// (`x` unused). The discriminator `z` is `F` on the right.
fn right_rel(b: Term, alpha: Type, beta: Type) -> Term {
    let y = Term::free("y", beta.clone());
    let z = Term::free("z", Type::bool());
    let inner = hol::hol_and(hol::hol_not(z), hol::hol_eq(y, b)); // ¬z ∧ (y = b)
    let lam_z = hol::pub_abs("z", Type::bool(), inner);
    let lam_yz = hol::pub_abs("y", beta, lam_z);
    hol::pub_abs("x", alpha, lam_yz)
}

fn inl_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let a = Term::free("a", alpha.clone());
    let rel = left_rel(a, alpha.clone(), beta.clone());
    let abs = Term::spec_abs(coprod_spec(), vec![alpha.clone(), beta.clone()]);
    let applied = Term::app(abs, rel);
    hol::pub_abs("a", alpha, applied)
}

/// `inl : 'a → coprod 'a 'b` ≡ `λa. abs (λx y. x = a)`.
pub fn inl_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = inl_body();
        let ty = body.type_of().expect("inl body type-checks");
        TermSpec::new(Canonical::Inl, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `inl α β : α → coprod α β`.
pub fn inl(alpha: Type, beta: Type) -> Term {
    Term::term_spec(inl_spec(), vec![alpha, beta])
}

fn inr_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let b = Term::free("b", beta.clone());
    let rel = right_rel(b, alpha.clone(), beta.clone());
    let abs = Term::spec_abs(coprod_spec(), vec![alpha.clone(), beta.clone()]);
    let applied = Term::app(abs, rel);
    hol::pub_abs("b", beta, applied)
}

/// `inr : 'b → coprod 'a 'b` ≡ `λb. abs (λx y. y = b)`.
pub fn inr_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = inr_body();
        let ty = body.type_of().expect("inr body type-checks");
        TermSpec::new(Canonical::Inr, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `inr α β : β → coprod α β`.
pub fn inr(alpha: Type, beta: Type) -> Term {
    Term::term_spec(inr_spec(), vec![alpha, beta])
}

fn coprod_case_body() -> Term {
    let alpha = Type::tfree("a");
    let beta = Type::tfree("b");
    let gamma = Type::tfree("c");
    let f_ty = Type::fun(alpha.clone(), gamma.clone());
    let g_ty = Type::fun(beta.clone(), gamma.clone());
    let coprod_ab = coprod(alpha.clone(), beta.clone());

    let f = Term::free("f", f_ty.clone());
    let g = Term::free("g", g_ty.clone());
    let c = Term::free("c", coprod_ab.clone());
    let r = Term::free("r", gamma.clone());

    let rep = Term::spec_rep(coprod_spec(), vec![alpha.clone(), beta.clone()]);
    let rep_c = Term::app(rep, c);

    // ∀a. rep c = (λx y. x = a) ⟹ r = f a
    let a = Term::free("a", alpha.clone());
    let left_eq = hol::hol_eq(rep_c.clone(), left_rel(a.clone(), alpha.clone(), beta.clone()));
    let r_eq_fa = hol::hol_eq(r.clone(), Term::app(f.clone(), a));
    let left_clause = hol::hol_forall("a", alpha.clone(), hol::hol_imp(left_eq, r_eq_fa));

    // ∀b. rep c = (λx y. y = b) ⟹ r = g b
    let b = Term::free("b", beta.clone());
    let right_eq = hol::hol_eq(rep_c, right_rel(b.clone(), alpha.clone(), beta.clone()));
    let r_eq_gb = hol::hol_eq(r.clone(), Term::app(g.clone(), b));
    let right_clause = hol::hol_forall("b", beta.clone(), hol::hol_imp(right_eq, r_eq_gb));

    let pred = hol::hol_and(left_clause, right_clause);
    let sel = hol::pub_abs("r", gamma.clone(), pred);
    let eps = Term::app(Term::select_op(gamma.clone()), sel);

    let lam_c = hol::pub_abs("c", coprod_ab, eps);
    let lam_g = hol::pub_abs("g", g_ty, lam_c);
    hol::pub_abs("f", f_ty, lam_g)
}

/// `coprodCase : ('a → 'c) → ('b → 'c) → coprod 'a 'b → 'c` — the
/// disjoint-union eliminator, defined via Hilbert ε on the matching
/// branch. Equations `coprodCase f g (inl a) = f a` and
/// `coprodCase f g (inr b) = g b` are theorems proved downstream.
pub fn coprod_case_spec() -> TermSpec {
    static LAZY: LazyLock<TermSpec> = LazyLock::new(|| {
        let body = coprod_case_body();
        let ty = body.type_of().expect("coprodCase body type-checks");
        TermSpec::new(Canonical::CoprodCase, Some(ty), Some(body))
    });
    LAZY.clone()
}
/// `coprodCase α β γ : (α → γ) → (β → γ) → coprod α β → γ`.
pub fn coprod_case(alpha: Type, beta: Type, gamma: Type) -> Term {
    Term::term_spec(coprod_case_spec(), vec![alpha, beta, gamma])
}
