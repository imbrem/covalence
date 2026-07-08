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
//! New [`Thm::new`] call sites, all real TCB additions:
//! - [`execute`] — **gated** on `TypeId::of::<Rel<F>>()` (a language admits the
//!   relations it vouches for), like [`canon`](crate::canon)/[`apply`](crate::apply);
//! - the **positive calculus** [`Thm::transpose`]/[`Thm::compose`]/[`Thm::meet`]/
//!   [`Thm::join_l`]/[`Thm::join_r`] — **ungated-but-trusted** (sound in every
//!   language: each only recombines already-proven positive facts), like
//!   [`and_intro`](crate::Thm::and_intro). Ungated ≠ untrusted. **Complement is
//!   deliberately absent** — negation needs an admitted axiom, not a mint.

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
    /// [`and_intro`](Thm::and_intro)).
    pub fn transpose(self) -> Thm<L, App<Transpose<R>, (B, A)>> {
        let (lang, App(r, (a, b))) = self.into_parts();
        Thm::new(lang, App(Transpose(r), (b, a)))
    }
}

// ============================================================================
// The rest of the POSITIVE relation calculus — composition, union (join), and
// intersection (meet). All ungated-but-trusted (sound in every language: each
// recombines already-proven positive facts), like `transpose`/`or_inl`/
// `and_intro`. **Complement is deliberately absent**: it is negation, which no
// execution can witness — it needs the admitted-axiom discipline (§3A-negation),
// not a mint here.
// ============================================================================

/// **Composition** `R ; S` — `⊢ a R b` ∧ `⊢ b S c` ⟹ `⊢ a (R;S) c`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Compose<R, S>(pub R, pub S);

// `X`/`Y`/`Z` are determined by `R::In = (X, Y)` and `S::In = (Y, Z)` (the shared
// `Y` is the composition middle) — coherent, one `In`/`Out` per `(R, S)`.
impl<R, S, X, Y, Z> Op for Compose<R, S>
where
    R: Op<In = (X, Y), Out = bool>,
    S: Op<In = (Y, Z), Out = bool>,
    X: 'static,
    Y: 'static,
    Z: 'static,
{
    type In = (X, Z);
    type Out = bool;
}

/// **Union** `R ∪ S` — `⊢ a R b` ⟹ `⊢ a (R∪S) b` (either injection).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Join<R, S>(pub R, pub S);

impl<R, S, X, Y> Op for Join<R, S>
where
    R: Op<In = (X, Y), Out = bool>,
    S: Op<In = (X, Y), Out = bool>,
    X: 'static,
    Y: 'static,
{
    type In = (X, Y);
    type Out = bool;
}

/// **Intersection** `R ∩ S` — `⊢ a R b` ∧ `⊢ a S b` ⟹ `⊢ a (R∩S) b`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Meet<R, S>(pub R, pub S);

impl<R, S, X, Y> Op for Meet<R, S>
where
    R: Op<In = (X, Y), Out = bool>,
    S: Op<In = (X, Y), Out = bool>,
    X: 'static,
    Y: 'static,
{
    type In = (X, Y);
    type Out = bool;
}

impl<L: Language, R, A, B, X, Y> Thm<L, App<R, (A, B)>>
where
    R: Op<In = (X, Y), Out = bool>,
    A: Expr<Ty = X>,
    B: Expr<Ty = Y>,
    X: 'static,
    Y: 'static,
{
    /// **Compose** `⊢ a R b` with `⊢ b S c` (the middle `b` matched, exactly as
    /// [`trans`](Thm::trans) matches its middle) to get `⊢ a (R;S) c`, under the
    /// **union** of the two contexts.
    ///
    /// Ungated-but-trusted: sound in every language (relational composition is a
    /// positive fact). `Err` if the middles differ (`B: Eq`, the same structural
    /// match `trans` uses — for `Ref<Arc<_>>` leaves this compares the shared
    /// pointees, i.e. the values) or the contexts cannot be combined.
    pub fn compose<S, C, Z>(
        self,
        other: Thm<L, App<S, (B, C)>>,
    ) -> Result<Thm<L, App<Compose<R, S>, (A, C)>>, Error>
    where
        B: Eq,
        S: Op<In = (Y, Z), Out = bool>,
        C: Expr<Ty = Z>,
        Z: 'static,
    {
        let (l1, App(r, (a, b1))) = self.into_parts();
        let (l2, App(s, (b2, c))) = other.into_parts();
        // NB `!(b1 == b2)`, not `b1 != b2`: `ne` is independently overridable on
        // `PartialEq`, so the trusted middle-match must use the same `eq` the
        // calculus uses (the `eq_mp` discipline).
        if !(b1 == b2) {
            return Err(Error::TransMismatch);
        }
        let lang = l1.union(l2).ok_or(Error::LangMismatch)?;
        Ok(Thm::new(lang, App(Compose(r, s), (a, c))))
    }

    /// **Meet** `⊢ a R b` with `⊢ a S b` (both operands matched) to get
    /// `⊢ a (R∩S) b`, under the **union** of the two contexts. `Err` if the
    /// operands differ (`A: Eq`, `B: Eq`) or the contexts cannot be combined.
    pub fn meet<S>(
        self,
        other: Thm<L, App<S, (A, B)>>,
    ) -> Result<Thm<L, App<Meet<R, S>, (A, B)>>, Error>
    where
        A: Eq,
        B: Eq,
        S: Op<In = (X, Y), Out = bool>,
    {
        let (l1, App(r, (a1, b1))) = self.into_parts();
        let (l2, App(s, (a2, b2))) = other.into_parts();
        // `!(x == y)`, not `x != y` — same `eq_mp` discipline as `compose`.
        if !(a1 == a2) || !(b1 == b2) {
            return Err(Error::TransMismatch);
        }
        let lang = l1.union(l2).ok_or(Error::LangMismatch)?;
        Ok(Thm::new(lang, App(Meet(r, s), (a1, b1))))
    }
}

impl<L, R, A, B, X, Y> Thm<L, App<R, (A, B)>>
where
    R: Op<In = (X, Y), Out = bool>,
    A: Expr<Ty = X>,
    B: Expr<Ty = Y>,
    X: 'static,
    Y: 'static,
{
    /// **Union-left**: from `⊢ a R b` get `⊢ a (R∪S) b` for any relation `s: S`
    /// (you supply the other disjunct op). Ungated, one-sided — like
    /// [`or_inl`](Thm::or_inl).
    pub fn join_l<S>(self, s: S) -> Thm<L, App<Join<R, S>, (A, B)>>
    where
        S: Op<In = (X, Y), Out = bool>,
    {
        let (lang, App(r, (a, b))) = self.into_parts();
        Thm::new(lang, App(Join(r, s), (a, b)))
    }

    /// **Union-right**: from `⊢ a S b` get `⊢ a (R∪S) b` for any relation `r: R`.
    pub fn join_r<R2>(self, r: R2) -> Thm<L, App<Join<R2, R>, (A, B)>>
    where
        R2: Op<In = (X, Y), Out = bool>,
    {
        let (lang, App(s, (a, b))) = self.into_parts();
        Thm::new(lang, App(Join(r, s), (a, b)))
    }
}
