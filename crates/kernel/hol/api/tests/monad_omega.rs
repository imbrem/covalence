//! End-to-end demonstration that a **properly polymorphic monad TYPE** shape is
//! expressible and kind-checkable through the [`HolOmega`] extension trait — the
//! gap that plain [`Hol`](covalence_hol_api::Hol) leaves open (its `tvar` is a
//! single kind-`⋆` carrier; there is no type-*operator* variable).
//!
//! Everything below is written against `O: HolOmega` and would carry over to any
//! backend implementing it. It proves:
//! - a type-operator variable `m : ⋆ ⇒ ⋆` and its application `m a` **kind-check**
//!   (`m a : ⋆`);
//! - the monad operation types `return : a → m a` and
//!   `bind : m a → (a → m b) → m b` are **well-kinded** (`: ⋆`);
//! - the closed schema `∀(m : ⋆ ⇒ ⋆). ∀(a : ⋆). a → m a` kind-checks and its rank
//!   is tracked;
//! - the base rank oracle **rejects an impredicative instantiation** à la Girard.

use covalence_hol_api::{HolOmega, InstError, NativeHolOmega};

/// Build `return`'s type `a → m a` as a reflected HOL-ω type, over a
/// type-operator variable `m : ⋆ ⇒ ⋆` and a kind-`⋆` variable `a`.
fn return_ty<O: HolOmega>(o: &O) -> O::TyRep {
    let star = o.star();
    let m = o.tyop_var("m", o.arrow(star.clone(), star)); // m : ⋆ ⇒ ⋆
    let a = o.ty_var("a"); // a : ⋆
    let m_a = o.ty_app(m, a.clone()); // m a
    o.ty_fun(a, m_a) // a → m a
}

/// Build `bind`'s type `m a → (a → m b) → m b`.
fn bind_ty<O: HolOmega>(o: &O) -> O::TyRep {
    let star = o.star();
    let m = o.tyop_var("m", o.arrow(star.clone(), star)); // m : ⋆ ⇒ ⋆
    let a = o.ty_var("a");
    let b = o.ty_var("b");
    let m_a = o.ty_app(m.clone(), a.clone()); // m a
    let m_b = o.ty_app(m, b); // m b
    let a_to_mb = o.ty_fun(a, m_b.clone()); // a → m b
    let tail = o.ty_fun(a_to_mb, m_b); // (a → m b) → m b
    o.ty_fun(m_a, tail) // m a → (a → m b) → m b
}

/// The **type-operator variable works**: `m : ⋆ ⇒ ⋆` applied to `a : ⋆` gives
/// `m a : ⋆`. This is exactly what plain HOL's single-carrier `tvar` cannot say.
#[test]
fn type_operator_variable_application_kind_checks() {
    let o = NativeHolOmega;
    let star = o.star();
    let op_kind = o.arrow(star.clone(), star.clone()); // ⋆ ⇒ ⋆

    let m = o.tyop_var("m", op_kind.clone());
    assert_eq!(o.kind_of(&m), Some(op_kind), "m : ⋆ ⇒ ⋆");

    let a = o.ty_var("a");
    assert_eq!(o.kind_of(&a), Some(star.clone()), "a : ⋆");

    let m_a = o.ty_app(m, a);
    assert_eq!(o.kind_of(&m_a), Some(star), "m a : ⋆");
    assert!(o.well_kinded(&m_a));
}

/// **Ill-kinded application is rejected**: applying `m : ⋆ ⇒ ⋆` to another
/// operator `n : ⋆ ⇒ ⋆` (kind `⋆ ⇒ ⋆ ≠ ⋆`) has no kind. Confirms `kind_of`
/// never returns a *wrong* kind — it returns `None`.
#[test]
fn ill_kinded_operator_application_is_rejected() {
    let o = NativeHolOmega;
    let star = o.star();
    let op_kind = o.arrow(star.clone(), star); // ⋆ ⇒ ⋆
    let m = o.tyop_var("m", op_kind.clone());
    let n = o.tyop_var("n", op_kind); // n : ⋆ ⇒ ⋆, not ⋆
    let bad = o.ty_app(m, n); // m n — arg kind ⋆⇒⋆ ≠ ⋆
    assert_eq!(o.kind_of(&bad), None);
    assert!(!o.well_kinded(&bad));
}

/// `return : a → m a` and `bind : m a → (a → m b) → m b` are both **well-kinded**
/// (`: ⋆`), built entirely through the trait over a type-operator variable.
#[test]
fn monad_operation_types_are_well_kinded() {
    let o = NativeHolOmega;
    let ret = return_ty(&o);
    let bind = bind_ty(&o);
    assert_eq!(o.kind_of(&ret), Some(o.star()), "return : a → m a  is ⋆");
    assert_eq!(o.kind_of(&bind), Some(o.star()), "bind type is ⋆");
    assert!(o.well_kinded(&bind));
}

/// The **closed monad schema** `∀(m : ⋆ ⇒ ⋆). ∀(a : ⋆). a → m a` kind-checks
/// (`: ⋆`) and its rank is tracked by the oracle. Uses de-Bruijn binders: under
/// the two `∀`s, `m` is `bound(1)` and `a` is `bound(0)`.
#[test]
fn closed_polymorphic_return_schema_kind_checks() {
    let o = NativeHolOmega;
    let star = o.star();
    let op_kind = o.arrow(star.clone(), star.clone()); // ⋆ ⇒ ⋆

    // body of the inner ∀: a → m a, with m = bound(1), a = bound(0).
    let m = o.bound(1);
    let a = o.bound(0);
    let m_a = o.ty_app(m, a.clone());
    let body = o.ty_fun(a, m_a); // a → m a

    // ∀(m : ⋆⇒⋆ : 0). ∀(a : ⋆ : 0). a → m a
    let inner = o.ty_all(star, 0, body); // binds a
    let schema = o.ty_all(op_kind, 0, inner); // binds m

    assert_eq!(o.kind_of(&schema), Some(o.star()), "schema : ⋆");
    // quantifiers raise the rank: rank(∀:0. ∀:0. ⋆-body) = max(0+1, 0+1) = 1.
    assert_eq!(o.rank_of(&schema), Some(1));
    assert!(o.well_kinded(&schema));
}

/// The **rank stratification bites** (Girard-blocking), end-to-end through the
/// trait: instantiating a rank-0 `∀α:⋆:0. α` at a *polymorphic* type
/// `σ = ∀β:⋆:0. β` (rank 1) is REFUSED, because the base `RankLe` oracle certifies
/// `1 ≤ 0 = F`. You cannot impredicatively instantiate at a higher-rank type.
#[test]
fn rank_stratification_rejects_impredicative_instantiation() {
    let o = NativeHolOmega;
    let star = o.star();
    let id_ty = o.ty_all(star.clone(), 0, o.bound(0)); // ∀α:⋆:0. α
    let sigma = o.ty_all(star, 0, o.bound(0)); // ∀β:⋆:0. β  (rank 1)

    assert_eq!(o.rank_of(&sigma), Some(1), "a polymorphic type has rank 1");
    assert_eq!(
        o.ty_inst(&id_ty, &sigma),
        Err(InstError::RankTooHigh {
            rank_sigma: 1,
            bound: 0,
        }),
    );
}

/// Raising the binder's rank to 1 admits the same polymorphic `σ` (rank `1 ≤ 1`):
/// stratification permits *predicative* instantiation at the higher rank, and the
/// (untrusted) substitution yields `σ → σ`.
#[test]
fn higher_rank_binder_admits_the_polymorphic_type() {
    let o = NativeHolOmega;
    let star = o.star();
    // ∀α:⋆:1. (α → α)
    let all = o.ty_all(star.clone(), 1, o.ty_fun(o.bound(0), o.bound(0)));
    let sigma = o.ty_all(star, 0, o.bound(0)); // rank 1

    let out = o.ty_inst(&all, &sigma).expect("rank 1 ≤ 1");
    assert_eq!(out, o.ty_fun(sigma.clone(), sigma), "σ → σ");
}

/// A **kind mismatch** in instantiation is rejected by the base `KindOf` cert: a
/// `∀` expecting `⋆` cannot be instantiated at an operator `m : ⋆ ⇒ ⋆`.
#[test]
fn ty_inst_kind_mismatch_is_rejected() {
    let o = NativeHolOmega;
    let star = o.star();
    let all = o.ty_all(star.clone(), 0, o.bound(0)); // ∀α:⋆:0. α
    let op = o.tyop_var("m", o.arrow(star.clone(), star.clone())); // kind ⋆⇒⋆
    match o.ty_inst(&all, &op) {
        Err(InstError::KindMismatch { want, got }) => {
            assert_eq!(want, o.star());
            assert_eq!(got, o.arrow(o.star(), o.star()));
        }
        other => panic!("expected KindMismatch, got {other:?}"),
    }
}
