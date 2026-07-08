//! **`Ty` reflected into the base** — the generic type-representation sort
//! (§3B / F7 / MF1 of `notes/vibes/base-relcalc-holomega-design.md`).
//!
//! Types become ordinary base *terms*: a concrete type rep enters as a
//! [`Val`](crate::Val)`<C>` leaf at a reflected sort `C`, and the type
//! constructors are the ops [`TyFn`]/[`TyApp`]` : Op<(C, C), C>`. A composite
//! type is then an [`App`](crate::App) spine over `Val<C>` leaves, and a type
//! *equation* transports through the **existing** `refl`/`cong_pair`/`cong_app`
//! calculus — **no new rule**.
//!
//! ## Generic over the rep `C` — the base names no concrete type (MF1)
//!
//! The constructors are generic in the rep `T`: the base cannot name
//! `covalence-core`'s `Type` (the crate hierarchy is `base → core`, not the
//! reverse), so the base stays parametric and the *consumer* picks `C`. Phase 0
//! exercises the identical `App`-spine transport with an **in-base demo rep**
//! [`TyRepDemo`], so the slice builds with **no `core` dependency**. Full
//! `core::Type` integration (`core` supplying `C = core::Type`, i.e.
//! `type TyRep = core::Type`) is a later step *in `core`*, not here.
//!
//! ## Why the equation is meaningful (F7)
//!
//! Leaf equality `⊢ Val(a) = Val(a')` fires only via
//! [`of_eq`](crate::of_eq) when `a == a'` (the rep's own [`Eq`]); distinct reps
//! are **not** provably equal. So `⊢ TyFn(a, b) = TyFn(a', b)` genuinely tracks
//! rep equality rather than being vacuous.

use std::marker::PhantomData;

use crate::op::Op;

/// The function-type constructor `(T, T) → T` over a reflected type-rep sort `T`
/// — `TyFn(dom, cod)` reflects `dom ⇒ cod` as a base term.
pub struct TyFn<T>(pub PhantomData<T>);

/// The type-application constructor `(T, T) → T` over a reflected type-rep sort
/// `T` — `TyApp(f, x)` reflects the application of a type operator.
pub struct TyApp<T>(pub PhantomData<T>);

// Hand-written trait impls: `PhantomData<T>` needs no `T: Trait` bound, so these
// are unconditional (a derive would spuriously require `T: Clone`/`Eq`/… and
// break `cong_app`, which needs `TyFn<T>: Clone` for *every* rep `T`).
impl<T> Copy for TyFn<T> {}
impl<T> Clone for TyFn<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for TyApp<T> {}
impl<T> Clone for TyApp<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> std::fmt::Debug for TyFn<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TyFn")
    }
}
impl<T> std::fmt::Debug for TyApp<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TyApp")
    }
}
impl<T> PartialEq for TyFn<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for TyFn<T> {}
impl<T> PartialEq for TyApp<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for TyApp<T> {}

impl<T: 'static> Op for TyFn<T> {
    type In = (T, T);
    type Out = T;
}
impl<T: 'static> Op for TyApp<T> {
    type In = (T, T);
    type Out = T;
}

/// `TyFn::<T>` (no `PhantomData` boilerplate at the call site).
pub fn ty_fn<T>() -> TyFn<T> {
    TyFn(PhantomData)
}
/// `TyApp::<T>` (no `PhantomData` boilerplate at the call site).
pub fn ty_app<T>() -> TyApp<T> {
    TyApp(PhantomData)
}

// ============================================================================
// Higher-rank binder syntax (stage B-K2) — reflected, DE-BRUIJN, INERT.
//
// These give the middle a HOL-ω type language with type quantification and
// type-level abstraction. They are **reflected syntax only**: there is NO
// reduction op in the base (β-substitution `TyBeta` lives in the middle), so the
// base stays operationally binder-free and every op here is inert (no
// `CanonRule`) ⇒ sound by vacuity, exactly like `TyFn`/`TyApp`.
//
// Variables are DE-BRUIJN indices ([`TyBound`] over a `u32` leaf), so structural
// equality on a spine **is** α-equivalence — no names, no capture, no α-renaming
// machinery. A malformed spine (dangling index, wrong kind) is *inert*, not
// *unsound*: it just fails to be provably equal to anything meaningful. `K` is the
// reflected kind-rep sort (see [`kind`](crate::kind)); the rank is a `u32` leaf,
// making rank-N quantification expressible (the rank *stratification* that
// consistency requires is enforced later, middle-side — B-K3 synthesises
// kind/rank as `CanonRule`s, and `TyInst` checks the side-condition).
// ============================================================================

/// A **de-Bruijn type variable** reference `u32 → T` — `App(TyBound, Val(i))` is
/// the bound tyvar at index `i` (0 = innermost binder).
pub struct TyBound<T>(pub PhantomData<T>);

/// **Rank-N universal type** `(K, u32, T) → T` — `TyAll(κ, r, τ)` reflects
/// `∀(α : κ : r). τ` (binding one de-Bruijn tyvar of kind `κ` at rank `r`).
pub struct TyAll<T, K>(pub PhantomData<(T, K)>);

/// **Type-level abstraction** `(K, T) → T` — `TyAbs(κ, τ)` reflects `λ(α : κ). τ`
/// (a type operator binding one de-Bruijn tyvar of kind `κ`).
pub struct TyAbs<T, K>(pub PhantomData<(T, K)>);

// Hand-written impls (never `derive` — spurious `T: Clone`/`K: Clone` bounds would
// break `cong_app`); mirrors `TyFn`/`TyApp` above.
impl<T> Copy for TyBound<T> {}
impl<T> Clone for TyBound<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T, K> Copy for TyAll<T, K> {}
impl<T, K> Clone for TyAll<T, K> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T, K> Copy for TyAbs<T, K> {}
impl<T, K> Clone for TyAbs<T, K> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> std::fmt::Debug for TyBound<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TyBound")
    }
}
impl<T, K> std::fmt::Debug for TyAll<T, K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TyAll")
    }
}
impl<T, K> std::fmt::Debug for TyAbs<T, K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TyAbs")
    }
}
impl<T> PartialEq for TyBound<T> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T> Eq for TyBound<T> {}
impl<T, K> PartialEq for TyAll<T, K> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T, K> Eq for TyAll<T, K> {}
impl<T, K> PartialEq for TyAbs<T, K> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<T, K> Eq for TyAbs<T, K> {}

impl<T: 'static> Op for TyBound<T> {
    type In = u32;
    type Out = T;
}
impl<T: 'static, K: 'static> Op for TyAll<T, K> {
    type In = (K, u32, T);
    type Out = T;
}
impl<T: 'static, K: 'static> Op for TyAbs<T, K> {
    type In = (K, T);
    type Out = T;
}

/// `TyBound::<T>` op (a de-Bruijn tyvar constructor).
pub fn ty_bound<T>() -> TyBound<T> {
    TyBound(PhantomData)
}
/// `TyAll::<T, K>` op (rank-N universal type).
pub fn ty_all<T, K>() -> TyAll<T, K> {
    TyAll(PhantomData)
}
/// `TyAbs::<T, K>` op (type-level abstraction).
pub fn ty_abs<T, K>() -> TyAbs<T, K> {
    TyAbs(PhantomData)
}
