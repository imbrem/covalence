//! **Relations as untrusted functions** — the additive relation-calculus slice
//! (Phase 0 of `notes/vibes/base-relcalc-holomega-design.md`).
//!
//! An untrusted relation `R : (In, Out) → bool` is a user-supplied function
//! `F : In → Result<Out, RelErr>`, with `a R b` meaning "running `f` on `a`
//! *produced* `b`". [`execute`] runs the function and mints the **positive
//! membership** witness `⊢ (a, b) ∈ R` through the sole [`Thm::new`] gate.
//!
//! ## The soundness asymmetry (the whole point)
//!
//! [`execute`] mints only **observed graph pairs**, so it is sound for **any**
//! `f` — *including a nondeterministic or partial one*. It can prove `a R b`
//! (the function returned `b`) but can **never** prove `¬(a R b)`: absence /
//! negation / functionality is unobservable by execution and needs an *admitted
//! axiom* whose soundness is the user's burden (never framework-granted — see the
//! design's §3A-negation). A nondeterministic `f` that returns `b₀` then `b₁` for
//! the same `a` soundly yields **both** `⊢ a R b₀` and `⊢ a R b₁`; this is exactly
//! where [`canon`](crate::canon)'s *functional* equation `f(a) = b` would be
//! unsound while membership stays sound.
//!
//! ## Zero-copy leaves (the efficiency north star)
//!
//! [`execute`] seats each operand behind one [`std::sync::Arc`] as a
//! [`Ref`]`<Arc<_>>` leaf — it never copies the payload. A megabyte WASM buffer
//! or store blob is moved once into an `Arc`; every subsequent calculus step
//! (`refl`/`cong_app`/`cong_pair`) that transports the theorem bumps a refcount
//! rather than deep-copying the buffer. Contrast [`canon`](crate::canon), which
//! owns a [`Val`](crate::Val)`<F::In>` and *does* copy its argument — so only the
//! `execute` membership form is zero-copy (see the design's MF2).
//!
//! ## Trust surface (audited mint sites — F8 of the design)
//!
//! Two new [`Thm::new`] call sites, both real TCB additions:
//! - [`execute`] — **gated** on `TypeId::of::<Rel<F>>()` (a language admits the
//!   relations it vouches for), like [`canon`](crate::canon)/[`apply`](crate::apply);
//! - [`Thm::transpose`] — **ungated-but-trusted** (sound in every language: it
//!   only recombines an already-proven positive fact), like
//!   [`and_intro`](crate::Thm::and_intro). Ungated ≠ untrusted.

use std::any::{Any, TypeId};
use std::sync::Arc;

use crate::eqn::{Error, Thm};
use crate::expr::{App, Expr, Ref};
use crate::lang::Language;
use crate::op::Op;

/// An **untrusted** function `In → Result<Out, RelErr>` — the computational
/// content of a relation. May be effectful, nondeterministic, or partial; the
/// kernel trusts nothing about it beyond "when `run` returns `Ok(b)`, the pair
/// `(a, b)` was observed in the graph". `Any` (⇒ `'static`) so `Rel<Self>` has a
/// stable [`TypeId`] for the [`execute`] gate.
pub trait UntrustedFn: Any {
    /// The input sort.
    type In;
    /// The output sort.
    type Out;
    /// Run the function on `a`. `Ok(b)` records the observed pair `(a, b)`;
    /// `Err` refuses (a partial/trapped call) and mints **nothing**.
    fn run(&self, a: &Self::In) -> Result<Self::Out, RelErr>;
}

/// An untrusted error from a relation's [`run`](UntrustedFn::run) — carries **no
/// trust** (it never mints a theorem; a refused call proves no absence).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelErr {
    /// The function declined on this input (a genuinely partial relation).
    Refused,
    /// The function trapped / errored (e.g. a WASM trap), with a message.
    Trapped(String),
}

/// A **relation op** `(In, Out) → bool` backed by the untrusted function `F`.
/// Writing `App<Rel<F>, _>` is always sound (uninterpreted ⇒ inert); the only way
/// to *populate* its graph is [`execute`], gated on this op's [`TypeId`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rel<F>(pub F);

impl<F: UntrustedFn> Op for Rel<F> {
    type In = (F::In, F::Out);
    type Out = bool;
}

/// Run the untrusted relation `rel` on input `a` and mint the **positive
/// membership** witness `⊢ (a, b) ∈ R` — where `b` is the *observed* output of
/// `rel.run(a)` — through the sole [`Thm::new`] gate.
///
/// **Gated** on `TypeId::of::<Rel<F>>()`: the language must admit this relation
/// (declare it part of its vocabulary). The untrusted `run` executes only *after*
/// the gate passes; its output is unused until minted here.
///
/// **Zero-copy** (F1/MF2 of the design): both operands are seated behind one
/// [`Arc`] each ([`Ref`]`<Arc<_>>` leaves) — the payload is moved once, never
/// copied. `Ok` mints the membership; `Err` returns without minting (a partial /
/// refused call proves no absence).
///
/// Soundness: membership records only an *observed* graph pair, so it holds for
/// **any** `f` (deterministic, nondeterministic, or partial). There is no path
/// here — or anywhere in the base — that mints `¬(a R b)`.
pub fn execute<L, F>(
    rel: Rel<F>,
    a: F::In,
    lang: L,
) -> Result<Thm<L, App<Rel<F>, (Ref<Arc<F::In>>, Ref<Arc<F::Out>>)>>, Error>
where
    L: Language,
    F: UntrustedFn,
    F::In: 'static,
    F::Out: 'static,
{
    let rule = TypeId::of::<Rel<F>>();
    if !lang.admits(rule) {
        return Err(Error::NotAdmitted(rule));
    }
    // Untrusted run — borrows `a`, then `a` is moved into the Arc leaf below.
    let b = rel
        .0
        .run(&a)
        .map_err(|e| Error::RuleFailed(format!("relation refused: {e:?}")))?;
    // Zero-copy leaves: move each payload into exactly one Arc (no deep copy).
    let a_ref = Ref(Arc::new(a));
    let b_ref = Ref(Arc::new(b));
    Ok(Thm::new(lang, App(rel, (a_ref, b_ref))))
}

/// The **transpose** (converse) of a relation op `R` — `R°` with swapped
/// input/output sorts. `⊢ a R b` ⟹ `⊢ b R° a`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Transpose<R>(pub R);

// `X`/`Y` are *determined* by `R::In = (X, Y)` (associated-type equality
// constrains them), so this impl is coherent — one `In`/`Out` per `R`.
impl<R, X, Y> Op for Transpose<R>
where
    R: Op<In = (X, Y), Out = bool>,
    X: 'static,
    Y: 'static,
{
    type In = (Y, X);
    type Out = bool;
}

impl<L, R, A, B, X, Y> Thm<L, App<R, (A, B)>>
where
    R: Op<In = (X, Y), Out = bool>,
    A: Expr<Ty = X>,
    B: Expr<Ty = Y>,
    X: 'static,
    Y: 'static,
{
    /// **Transpose** a proven positive membership: from `⊢ a R b` get `⊢ b R° a`.
    ///
    /// Ungated-but-trusted (F8): sound in **every** language — it only recombines
    /// an already-proven positive fact by swapping the pair and wrapping the op in
    /// [`Transpose`], introducing no new equality and no evaluation. Still a real
    /// [`Thm::new`] site (a TCB addition audited like
    /// [`and_intro`](Thm::and_intro)). (Compose/join/meet follow the same pattern;
    /// Phase 0 ships only `transpose`.)
    pub fn transpose(self) -> Thm<L, App<Transpose<R>, (B, A)>> {
        let (lang, App(r, (a, b))) = self.into_parts();
        Thm::new(lang, App(Transpose(r), (b, a)))
    }
}
