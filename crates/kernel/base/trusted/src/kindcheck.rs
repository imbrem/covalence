//! **B-K3 — kind & rank synthesis as `CanonRule`s** over a flat demo type rep
//! (stage B-K3 of [`notes/vibes/tcb-holomega-roadmap.md`](../../../../notes/vibes/tcb-holomega-roadmap.md)).
//!
//! The HOL-ω middle's kind/rank checker becomes a **consumer of base-minted
//! equations** rather than trusted middle code: the base provides three
//! [`CanonRule`]s that *compute and certify* the kind, the rank, and rank-`≤` of a
//! reflected type. `TyInst`'s rank side-condition (middle, later) then discharges
//! its `rank(σ) ≤ r` premise against a base-minted `⊢ (rankof(σ) ≤ r) = T`, keeping
//! the rank arithmetic out of the middle TCB.
//!
//! ## Representation
//!
//! A `CanonRule` evaluates over a [`Val`](crate::Val) *leaf*, so a whole type term
//! is encoded as one flat value [`TyC`] (a **de-Bruijn**, binder-explicit rep) —
//! distinct from the App-spine reflection ([`tyrep`](crate::tyrep)/[`kind`](crate::kind)),
//! which is the middle's *syntax*. The two are bridged later when a concrete rep
//! (`C = core::Type`) is wired in; here [`TyC`]/[`KindC`] are the in-base **demo**.
//!
//! ## Soundness (the audit contract)
//!
//! Each rule denotes exactly the total function its `eval` computes (the standard
//! `CanonRule` denotation, as for the arithmetic certs). The load-bearing contract:
//! - [`KindOf`] returns the **actual** kind of a well-kinded type, or `None` on any
//!   ill-kinded input — **never a wrong kind** (a wrong kind would, once this is the
//!   oracle for the middle, mint a false rank premise and defeat the `TyInst` gate).
//!   Kind synthesis is the standard simply-kinded discipline: `Fn` needs both sides
//!   `⋆`; `App` needs an operator kind `κ₁ ⇒ κ₂` applied at `κ₁`; `∀` needs a `⋆`
//!   body; `λ` forms `κ ⇒ kind(body)`; a dangling de-Bruijn index is `None`.
//! - [`RankOf`] is **gated on well-kindedness** (returns `None` unless [`KindOf`]
//!   succeeds) and then returns the structural rank with `rank(∀α:κ:r.τ) =
//!   max(r+1, rank τ)` — quantification raises the rank (the stratification that
//!   blocks impredicative self-instantiation). `InstTFree` is the rank-0 case.
//! - [`RankLe`] decides `a ≤ b` on `u32` (total).
//!
//! **Note (scope):** these rules *compute and certify*; they do **not** enforce the
//! stratification — that is the middle-side `TyInst` side-condition, gated behind
//! the full Homeier-aligned consistency proof (vs `SelectAx`/`bool`) before any
//! higher-rank rule enters `CORE_MANIFEST`. The rank formula here (esp. for `λ`) is
//! the **demo** discipline; the authoritative alignment lands with that proof.

use crate::lang::CanonRule;
use crate::op::Op;

/// A reflected **kind** `κ ::= ⋆ | κ ⇒ κ` (flat demo rep).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum KindC {
    /// The kind `⋆` of proper types.
    Star,
    /// The function kind `κ₁ ⇒ κ₂` of a type operator.
    Arrow(Box<KindC>, Box<KindC>),
}

/// A reflected **type** (flat, de-Bruijn demo rep). Binders (`All`/`Abs`) bind one
/// de-Bruijn tyvar; [`TyC::Bound`]`(0)` is the innermost binder.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TyC {
    /// De-Bruijn type variable (index into the enclosing binders).
    Bound(u32),
    /// A type constant tagged by id, carrying its declared kind.
    Con(u32, KindC),
    /// Arrow type `σ ⇒ τ` (both `σ`, `τ` must be `⋆`).
    Fn(Box<TyC>, Box<TyC>),
    /// Type-operator application `f x` (`f : κ₁ ⇒ κ₂`, `x : κ₁`).
    App(Box<TyC>, Box<TyC>),
    /// Rank-N universal `∀(α : κ : r). τ` (`τ` kinded with `α : κ` in scope).
    All(KindC, u32, Box<TyC>),
    /// Type-level abstraction `λ(α : κ : r). τ` (a type operator).
    Abs(KindC, u32, Box<TyC>),
}

/// De-Bruijn lookup: index `i` (0 = innermost) into a binder stack (`ctx` grows on
/// binder entry, innermost last). `None` if `i` is out of range (a dangling index).
fn lookup<T>(ctx: &[T], i: u32) -> Option<&T> {
    let n = ctx.len();
    let idx = (i as usize).checked_add(1)?;
    if idx > n {
        return None;
    }
    ctx.get(n - idx)
}

/// Kind synthesis: the actual kind of `t` in binder-kind context `ctx`, or `None`
/// if `t` is ill-kinded. Total (structural recursion; `ctx` is push/pop balanced).
fn kind_of(t: &TyC, ctx: &mut Vec<KindC>) -> Option<KindC> {
    match t {
        TyC::Bound(i) => lookup(ctx, *i).cloned(),
        TyC::Con(_, k) => Some(k.clone()),
        TyC::Fn(a, b) => {
            let ka = kind_of(a, ctx)?;
            let kb = kind_of(b, ctx)?;
            (ka == KindC::Star && kb == KindC::Star).then_some(KindC::Star)
        }
        TyC::App(f, x) => {
            let kf = kind_of(f, ctx)?;
            let kx = kind_of(x, ctx)?;
            match kf {
                KindC::Arrow(k1, k2) if *k1 == kx => Some(*k2),
                _ => None,
            }
        }
        TyC::All(k, _r, body) => {
            ctx.push(k.clone());
            let kb = kind_of(body, ctx);
            ctx.pop();
            (kb? == KindC::Star).then_some(KindC::Star)
        }
        TyC::Abs(k, _r, body) => {
            ctx.push(k.clone());
            let kb = kind_of(body, ctx);
            ctx.pop();
            Some(KindC::Arrow(Box::new(k.clone()), Box::new(kb?)))
        }
    }
}

/// Structural rank of `t` in binder-rank context `ctx`. `None` only on a dangling
/// de-Bruijn index (which [`kind_of`] also rejects, so on well-kinded input this is
/// always `Some`). `rank(∀α:κ:r.τ) = max(r+1, rank τ)`; `rank(λα:κ:r.τ) =
/// max(r, rank τ)`.
fn rank_of(t: &TyC, ctx: &mut Vec<u32>) -> Option<u32> {
    match t {
        TyC::Bound(i) => lookup(ctx, *i).copied(),
        TyC::Con(..) => Some(0),
        TyC::Fn(a, b) => Some(rank_of(a, ctx)?.max(rank_of(b, ctx)?)),
        TyC::App(f, x) => Some(rank_of(f, ctx)?.max(rank_of(x, ctx)?)),
        TyC::All(_k, r, body) => {
            ctx.push(*r);
            let rb = rank_of(body, ctx);
            ctx.pop();
            Some((r + 1).max(rb?))
        }
        TyC::Abs(_k, r, body) => {
            ctx.push(*r);
            let rb = rank_of(body, ctx);
            ctx.pop();
            Some((*r).max(rb?))
        }
    }
}

/// `kindof : TyC → KindC` — the reflected kind of a type (`None` ⇒ ill-kinded,
/// never a wrong kind). Used via [`canon`](crate::canon), gated on its `TypeId`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KindOf;
impl Op for KindOf {
    type In = TyC;
    type Out = KindC;
}
impl CanonRule for KindOf {
    fn eval(&self, t: &TyC) -> Option<KindC> {
        kind_of(t, &mut Vec::new())
    }
}

/// `rankof : TyC → u32` — the reflected rank of a **well-kinded** type (`None` on
/// ill-kinded input, so `rankof` and `kindof` share a domain).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RankOf;
impl Op for RankOf {
    type In = TyC;
    type Out = u32;
}
impl CanonRule for RankOf {
    fn eval(&self, t: &TyC) -> Option<u32> {
        kind_of(t, &mut Vec::new())?; // gate on well-kindedness
        rank_of(t, &mut Vec::new())
    }
}

/// `rankle : (u32, u32) → bool` — decides `a ≤ b` (total). The premise a middle
/// `TyInst` discharges as `⊢ (rankof(σ) ≤ r) = T`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RankLe;
impl Op for RankLe {
    type In = (u32, u32);
    type Out = bool;
}
impl CanonRule for RankLe {
    fn eval(&self, &(a, b): &(u32, u32)) -> Option<bool> {
        Some(a <= b)
    }
}
