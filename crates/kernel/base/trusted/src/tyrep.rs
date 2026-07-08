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
