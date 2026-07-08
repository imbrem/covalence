//! **HOL-ω kinds reflected into the base** — the reflected Kind sort (stage B-K1
//! of [`notes/vibes/tcb-holomega-roadmap.md`](../../../../notes/vibes/tcb-holomega-roadmap.md)).
//!
//! Kinds `κ ::= ⋆ | κ ⇒ κ` are **binder-free**, so they reflect into the ground
//! base grammar exactly as type reps do ([`tyrep`](crate::tyrep)): a kind is a base
//! term of a reflected kind-rep sort `K`, built from two inert constructor ops —
//! [`KStar`]`: () → K` (the base kind `⋆` of proper types) and [`KArrow`]`: (K, K)
//! → K` (the function kind `κ₁ ⇒ κ₂` of a type operator). Kind equality and
//! congruence come **free** from the existing `refl`/`cong_pair`/`cong_app`
//! calculus — no new rule and **no [`Thm::new`](crate::Thm) site**.
//!
//! The ops are **uninterpreted** (no [`CanonRule`](crate::CanonRule)) ⇒ inert ⇒
//! sound by vacuity: writing `App<KArrow, _>` proves nothing on its own. Kind/rank
//! *synthesis* (`KindOf`/`RankOf`/`RankLe`) arrives later (stage B-K3) as
//! `CanonRule`s that a middle kind-checker consumes as base-minted equations.
//!
//! Generic over the kind-rep `K` for the same reason [`tyrep`](crate::tyrep) is
//! generic over `T`: the base names no concrete rep; the consumer (later, `core`)
//! picks `K`.

use std::marker::PhantomData;

use crate::expr::{App, Val};
use crate::op::Op;

/// The base kind `⋆` (the kind of proper types), as a **nullary** constructor
/// `() → K` over a reflected kind-rep sort `K`. The `⋆` *term* is
/// `App(KStar, Val(()))` — see [`star`].
pub struct KStar<K>(pub PhantomData<K>);

/// The function-kind constructor `(K, K) → K` — `KArrow(κ₁, κ₂)` reflects
/// `κ₁ ⇒ κ₂` (the kind of a type operator).
pub struct KArrow<K>(pub PhantomData<K>);

// Hand-written impls (never `derive` — it would spuriously require `K: Clone`/`Eq`
// and break `cong_app`, which needs the op `Clone` for *every* rep `K`); mirrors
// [`tyrep`](crate::tyrep).
impl<K> Copy for KStar<K> {}
impl<K> Clone for KStar<K> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K> Copy for KArrow<K> {}
impl<K> Clone for KArrow<K> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K> std::fmt::Debug for KStar<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("KStar")
    }
}
impl<K> std::fmt::Debug for KArrow<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("KArrow")
    }
}
impl<K> PartialEq for KStar<K> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<K> Eq for KStar<K> {}
impl<K> PartialEq for KArrow<K> {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl<K> Eq for KArrow<K> {}

impl<K: 'static> Op for KStar<K> {
    type In = ();
    type Out = K;
}
impl<K: 'static> Op for KArrow<K> {
    type In = (K, K);
    type Out = K;
}

/// `KStar::<K>` op (no `PhantomData` boilerplate at the call site).
pub fn k_star<K>() -> KStar<K> {
    KStar(PhantomData)
}
/// `KArrow::<K>` op.
pub fn k_arrow<K>() -> KArrow<K> {
    KArrow(PhantomData)
}

/// The `⋆` kind as a base **term** `App(KStar, Val(()))` at the reflected sort `K`
/// (the nullary [`KStar`] applied to the unit leaf — `()` itself is not an `Expr`,
/// so the argument is `Val(())`).
pub fn star<K: 'static>() -> App<KStar<K>, Val<()>> {
    App(k_star::<K>(), Val(()))
}
