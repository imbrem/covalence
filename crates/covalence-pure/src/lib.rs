//! # `covalence-pure` — the base logic (the TCB floor)
//!
//! A very small **constructive first-order logic**, encoded directly in Rust's
//! own type system (propositions-as-types, Curry–Howard at the host level). It
//! is the bottom of the three-layer kernel stack (`notes/refactor-plan.md`):
//! `covalence-pure` (this crate, trusted *unconditionally*) → `covalence-core`
//! (the HOL TCB) → `covalence-init` (the semi-trusted catalogue).
//!
//! ## The judgement: [`Thm<C, P>`]
//!
//! A [`Thm<C, P>`] is a proof of the sequent **`C ⊢ P`**: the proposition `P`
//! holds under the **trust-context** `C`. The two parameters play very
//! different roles:
//!
//! - **`P` is the logic.** Propositions are *types* and proofs are *values*:
//!   `(P, Q)` is `P ∧ Q`, [`Either<P, Q>`] is `P ∨ Q`, `()` is `⊤`. Because a
//!   proof literally *is* its witness data, the logic is constructive — a proof
//!   of `P ∨ Q` is an actual [`Either`] whose tag is decidable by `match`.
//! - **`C` is the TCB.** `C` is the *meta-assumption context* / dynamic TCB
//!   (the `Ker` of `refactor-plan.md §2.2`): it names what is trusted to mint
//!   theorems. Adding a feature to the trusted base = a richer `C` on the
//!   **left**; the actual logical content stays in `P`. The contexts to come:
//!     - `Hol` — "true in HOL": one proves `Thm<Hol, HolThm>`, where the prop
//!       `HolThm` carries the HOL sequent `φ ⊢ p`.
//!     - `WasmEval` — facts attested by evaluating WASM: `WasmEval ⊢ …`.
//!     - `WasmTrusted` — extends `Hol` with *lifts* of `WasmEval` facts: a
//!       context whose rules accept both `Hol`- and `WasmEval`-theorems.
//!     - `Any` (later) — a dynamic, inspectable multi-TCB (`Arc<dyn …>`), for
//!       reasoning across several TCBs at once.
//!
//! ## Why this is sound
//!
//! The whole argument rests on **two** facts, only one of which is visible in
//! the code:
//!
//! 1. **Private fields.** `Thm`'s fields are private and there is *no* public
//!    constructor, so outside this crate the only way to obtain a `Thm` is
//!    through the methods here. Consequently **every line of `covalence-pure`
//!    is TCB** — keep it minimal, and never define a concrete context here.
//! 2. **The orphan rule (load-bearing!).** A `Thm<C, _>` is minted *only*
//!    through `C`'s own impls of [`Intro`] / [`Infer1`] / [`Infer2`] / [`RwIn`].
//!    Because `C` is the `Self` type of those impls, Rust's orphan rule lets
//!    **only `C`'s defining crate** write them: no foreign crate can forge a
//!    `C`-theorem. A theorem crosses from one context to another *only* when the
//!    **target** context opts in by implementing a rule that consumes the source
//!    theorem — including context [`Union`] (conjunction via [`Thm::apply`] /
//!    [`Prod`]). Trust is therefore explicit, consensual, and its blame
//!    localizes to whoever wrote the rule.
//!
//! Conversely, **consuming** a theorem is unrestricted: holding a `Thm<C, P>`
//! you may always build your *own* context's theorem from it. You still cannot
//! fabricate a `C`-theorem you were not handed.
//!
//! ## Reserved structural rules
//!
//! `covalence-pure` itself grants a fixed, sound set of **constructive
//! structural rules** to *every* context (the blanket impls below): `⊤`-intro
//! (`()`), identity ([`Id`]), `∧`/`∨` introduction ([`Inl`] / [`Inr`] /
//! [`Prod`]) and elimination ([`Thm::or_elim`], [`Thm::fst`] / [`Thm::snd`],
//! the [`Fst`] / [`Snd`] rule projections), and context-sum intro/elim
//! ([`Thm::ctx_inl`] / [`Thm::ctx_or_elim`]). These are sound *because the prop
//! is the witness data* — an eliminator merely `match`es a value whose
//! constructor was already fixed at introduction time. The consequence:
//! `Either` / tuple mean **constructive** `∨` / `∧`; a context wanting a
//! *classical* connective (one provable without committing to a side) must use
//! its **own opaque prop type**, not Rust's `Either` / tuple.
//!
//! ## A note on mutation
//!
//! In-place rewriting is confined to [`RwIn`]: [`Thm::rw_in`] threads `&mut P`
//! into a context's *own* trusted rule and never lets that `&mut` escape. There
//! is deliberately **no** `&mut`-returning accessor and **no** reborrow that
//! yields a `Thm<_, &mut _>`, so a live theorem's witness cannot be aliased and
//! overwritten from userspace. The owned destructure [`Thm::into_parts`] is
//! sound precisely because it *consumes* the theorem: it returns the context
//! and the bare witness data, which — absent a public constructor — cannot be
//! recombined into a forged `Thm`. Read access without consuming is via the
//! shared borrows [`Thm::ctx`] / [`Thm::prop`] / [`Thm::as_ref`].

use std::{convert::Infallible, fmt::Debug};

use covalence_types::Either;

/// An **introduction** rule for a context: `Self` mints a fresh `Thm<Self, P>`
/// on its own authority, consuming a rule witness `R`.
///
/// Soundness: implementing this for `Self = C` asserts that `C` may soundly
/// assert `P`. The orphan rule reserves this impl to `C`'s defining crate, so
/// no foreign crate can introduce a `C`-theorem.
pub trait Intro<R, P>: Sized {
    type Err;

    fn intro(self, rule: R) -> Result<(Self, P), Self::Err>;
}

/// A **unary inference** rule: build a `Self`-theorem (prop `Q`) from one
/// premise theorem (context `C`, prop `P`). The *output* context `Self` chooses
/// to consume the input — this is how a theorem crosses contexts.
///
/// Soundness: reserved to `Self`'s crate by the orphan rule. When `Self = C`
/// it is an intra-context rule (e.g. [`Id`], [`Inl`]); when `Self ≠ C`, `Self`
/// is vouching for `C`'s theorem as it lifts it in.
pub trait Infer1<C, R, P, Q>: Sized {
    type Err;

    fn infer_from(ctx: C, rule: R, prem: P) -> Result<(Self, Q), Self::Err>;
}

/// A **binary inference** rule: combine two premise theorems (possibly from
/// different contexts `C1`, `C2`) into a `Self`-theorem. The vehicle for
/// `∧`-style merges across contexts; see [`Prod`] + [`Union`] and [`Thm::apply`].
pub trait Infer2<C1, C2, R, P1, P2, Q>: Sized {
    type Err;

    fn infer_from(ctx: (C1, C2), rule: R, prem: (P1, P2)) -> Result<(Self, Q), Self::Err>;
}

/// An **in-place rewrite** rule: a context mutates its own theorem's witness
/// `P`, returning auxiliary data `D`. The `&mut P` is confined to this trusted
/// rule (cf. [`Thm::rw_in`]); userspace never receives it.
pub trait RwIn<R, P, D>: Sized {
    type Err;

    fn rw_in(&mut self, rule: R, prem: &mut P) -> Result<D, Self::Err>;
}

/// A `covalence-pure` theorem: a proof of `C ⊢ P` — proposition/witness `P`
/// holds under trust-context `C`.
///
/// The fields are **private with no public constructor** — this is load-bearing
/// (see the crate docs). A `Thm` is producible only by the rules in this crate,
/// and a `C`-theorem only via `C`'s own [`Intro`] / [`Infer1`] / [`Infer2`] /
/// [`RwIn`] impls. The derived traits only *operate on* existing theorems; they
/// cannot mint one. Note the conditional bounds: a non-`Clone` (e.g. linear)
/// context automatically makes its theorems non-`Clone`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Thm<C, P> {
    ctx: C,
    prop: P,
}

impl<C, P> Thm<C, P> {
    /// Panicking [`Thm::intro`], for infallible contexts and tests.
    pub fn new<R>(ctx: C, rule: R) -> Thm<C, P>
    where
        C: Intro<R, P>,
        C::Err: Debug,
    {
        Self::intro(ctx, rule).expect("Thm::new: intro failed")
    }

    /// Introduce a theorem on context `C`'s own authority ([`Intro`]).
    pub fn intro<R>(ctx: C, rule: R) -> Result<Thm<C, P>, C::Err>
    where
        C: Intro<R, P>,
    {
        let (ctx, prop) = ctx.intro(rule)?;
        Ok(Thm { ctx, prop })
    }

    /// Borrow the trust-context.
    ///
    /// Read-only: reading mints no theorem, and with no public constructor the
    /// borrow cannot be recombined into a forged `Thm`.
    pub fn ctx(&self) -> &C {
        &self.ctx
    }

    /// Borrow the proposition/witness. Read-only; see [`Thm::ctx`].
    pub fn prop(&self) -> &P {
        &self.prop
    }

    /// Reborrow as a theorem of references (read access without consuming).
    pub fn as_ref(&self) -> Thm<&C, &P> {
        Thm {
            ctx: &self.ctx,
            prop: &self.prop,
        }
    }

    /// Destructure into the owned trust-context and witness.
    ///
    /// Sound because it *consumes* the theorem: the returned `P` is bare witness
    /// data, not a `Thm`, and cannot be recombined into one outside this crate
    /// (no public constructor). For non-consuming access use [`Thm::ctx`] /
    /// [`Thm::prop`] / [`Thm::as_ref`]; for in-place rewriting use [`Thm::rw_in`].
    pub fn into_parts(self) -> (C, P) {
        (self.ctx, self.prop)
    }

    /// Unary inference ([`Infer1`]): consume this theorem to mint a `G`-theorem.
    /// `G` is the *output* context and must opt in by implementing the rule.
    pub fn infer<G, R, Q>(self, rule: R) -> Result<Thm<G, Q>, G::Err>
    where
        G: Infer1<C, R, P, Q>,
    {
        let (ctx, prop) = G::infer_from(self.ctx, rule, self.prop)?;
        Ok(Thm { ctx, prop })
    }

    /// In-place rewrite ([`RwIn`]): context `C` mutates this theorem's witness
    /// and returns auxiliary data `D`.
    pub fn rw_in<R, D>(&mut self, rule: R) -> Result<D, C::Err>
    where
        C: RwIn<R, P, D>,
    {
        self.ctx.rw_in(rule, &mut self.prop)
    }

    /// Binary inference ([`Infer2`]): combine this theorem with `other` into a
    /// `U`-theorem. `U` opts in (and, for `∧`, [`Union`]s the two contexts).
    pub fn apply<C2, U, R, P2, Q>(self, rule: R, other: Thm<C2, P2>) -> Result<Thm<U, Q>, U::Err>
    where
        U: Infer2<C, C2, R, P, P2, Q>,
    {
        let (ctx, prop) = U::infer_from((self.ctx, other.ctx), rule, (self.prop, other.prop))?;
        Ok(Thm { ctx, prop })
    }
}

/// `∧`-elimination: the constructive conjunction destructures, mirroring
/// [`Thm::or_elim`] for `∨`. Sound because the prop is an actual `(P, Q)` value.
impl<C, P, Q> Thm<C, (P, Q)> {
    /// Left `∧`-elim: from `C ⊢ P ∧ Q` extract `C ⊢ P` (drops the `Q` witness).
    pub fn fst(self) -> Thm<C, P> {
        Thm {
            ctx: self.ctx,
            prop: self.prop.0,
        }
    }

    /// Right `∧`-elim: from `C ⊢ P ∧ Q` extract `C ⊢ Q` (drops the `P` witness).
    pub fn snd(self) -> Thm<C, Q> {
        Thm {
            ctx: self.ctx,
            prop: self.prop.1,
        }
    }

    /// Both conjuncts. Needs `C: Clone` to duplicate the context — a linear
    /// (non-`Clone`) context can only take one side, via [`Thm::fst`]/[`Thm::snd`].
    pub fn and_elim(self) -> (Thm<C, P>, Thm<C, Q>)
    where
        C: Clone,
    {
        let (p, q) = self.prop;
        (
            Thm {
                ctx: self.ctx.clone(),
                prop: p,
            },
            Thm {
                ctx: self.ctx,
                prop: q,
            },
        )
    }
}

/// `⊤`-introduction: every context proves `⊤` (the unit prop `()`). A reserved
/// structural rule — so a context cannot also define its own `Intro<Self, ()>`
/// (it would conflict with this blanket impl under coherence).
impl<C> Intro<C, ()> for C {
    type Err = Infallible;

    fn intro(self, _rule: C) -> Result<(Self, ()), Self::Err> {
        Ok((self, ()))
    }
}

/// The identity rule: leave a theorem unchanged ([`Infer1`] within one context).
pub struct Id;

impl<C, P> Infer1<C, Id, P, P> for C {
    type Err = Infallible;

    fn infer_from(ctx: C, _rule: Id, prem: P) -> Result<(Self, P), Self::Err> {
        Ok((ctx, prem))
    }
}

impl<C, P> RwIn<Id, P, ()> for C {
    type Err = Infallible;

    fn rw_in(&mut self, _rule: Id, _prem: &mut P) -> Result<(), Self::Err> {
        Ok(())
    }
}

/// Left injection — `∨`-introduction: `C ⊢ P` ⟹ `C ⊢ P ∨ Q` for any `Q`.
pub struct Inl;

impl<C, P, Q> Infer1<C, Inl, P, Either<P, Q>> for C {
    type Err = Infallible;

    fn infer_from(ctx: C, _rule: Inl, prem: P) -> Result<(Self, Either<P, Q>), Self::Err> {
        Ok((ctx, Either::Left(prem)))
    }
}

/// Right injection — `∨`-introduction: `C ⊢ Q` ⟹ `C ⊢ P ∨ Q` for any `P`.
pub struct Inr;

impl<C, P, Q> Infer1<C, Inr, Q, Either<P, Q>> for C {
    type Err = Infallible;

    fn infer_from(ctx: C, _rule: Inr, prem: Q) -> Result<(Self, Either<P, Q>), Self::Err> {
        Ok((ctx, Either::Right(prem)))
    }
}

impl<C, P, Q> Thm<C, Either<P, Q>> {
    /// `∨`-elimination: decide a constructive disjunction by matching its
    /// witness. Sound because the `Either` tag was fixed at introduction.
    pub fn or_elim(self) -> Either<Thm<C, P>, Thm<C, Q>> {
        match self.prop {
            Either::Left(p) => Either::Left(Thm {
                ctx: self.ctx,
                prop: p,
            }),
            Either::Right(q) => Either::Right(Thm {
                ctx: self.ctx,
                prop: q,
            }),
        }
    }
}

/// First projection rule combinator: `∧`-eliminate a tuple premise, then apply
/// the inner rule `R` to its first conjunct.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Fst<R>(pub R);

impl<C1, C2, R, P1, P2, Q> Infer1<C1, Fst<R>, (P1, P2), Q> for C2
where
    C2: Infer1<C1, R, P1, Q>,
{
    type Err = C2::Err;

    fn infer_from(ctx: C1, Fst(rule): Fst<R>, (prem, _): (P1, P2)) -> Result<(C2, Q), Self::Err> {
        C2::infer_from(ctx, rule, prem)
    }
}

/// Second projection rule combinator: `∧`-eliminate a tuple premise, then apply
/// the inner rule `R` to its second conjunct.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Snd<R>(pub R);

impl<C1, C2, R, P1, P2, Q> Infer1<C1, Snd<R>, (P1, P2), Q> for C2
where
    C2: Infer1<C1, R, P2, Q>,
{
    type Err = C2::Err;

    fn infer_from(ctx: C1, Snd(rule): Snd<R>, (_, prem): (P1, P2)) -> Result<(C2, Q), Self::Err> {
        C2::infer_from(ctx, rule, prem)
    }
}

/// Combine two trust-contexts into `Self`.
///
/// Used to form the context of a conjunction across contexts ([`Prod`]).
/// **Infallible**: implementing `Union<C1, C2>` asserts that `C1` and `C2` are
/// *unconditionally* mergeable into `Self` (and that `Self` vouches for both
/// premises). If a merge can fail at runtime, model it with a fallible
/// [`Infer2`] rule instead.
pub trait Union<C1, C2>: Sized {
    fn union(lhs: C1, rhs: C2) -> Self;
}

/// Product rule — `∧`-introduction across contexts: [`Union`] the two contexts
/// into `U`, pair the premises, then run a single ordinary [`Infer1`] rule `R`
/// on the conjunction `(P1, P2)` in the unified context.
///
/// The pure conjunction is `Prod(`[`Id`]`)`: `Thm<C1, P1>` and `Thm<C2, P2>`
/// combine into `Thm<U, (P1, P2)>`. To transform each side *before* combining,
/// pre-process with [`Thm::infer`] and conjoin with `Prod(Id)`
/// (`a.infer(r1)?.apply(Prod(Id), b.infer(r2)?)`); to transform the joint
/// result, use `Prod(rule)` (e.g. [`Fst`] / [`Snd`] to project a conjunct).
pub struct Prod<R>(pub R);

impl<C1, C2, R, P1, P2, Q, U> Infer2<C1, C2, Prod<R>, P1, P2, Q> for U
where
    U: Union<C1, C2> + Infer1<U, R, (P1, P2), Q>,
{
    type Err = <U as Infer1<U, R, (P1, P2), Q>>::Err;

    fn infer_from(
        (lctx, rctx): (C1, C2),
        Prod(rule): Prod<R>,
        prems: (P1, P2),
    ) -> Result<(U, Q), Self::Err> {
        let ctx = U::union(lctx, rctx);
        <U as Infer1<U, R, (P1, P2), Q>>::infer_from(ctx, rule, prems)
    }
}

// === Contexts distribute with `Either` ===
//
// A sum *context* `Either<C, G>` is "a theorem that holds in C, or in G". Like
// the prop-level `∨`, these are sound because the context is real data: the
// eliminator just matches which branch was injected.

impl<C, P> Thm<C, P> {
    /// Context `∨`-introduction (left): inject `C` into a sum context.
    pub fn ctx_inl<G>(self) -> Thm<Either<C, G>, P> {
        Thm {
            ctx: Either::Left(self.ctx),
            prop: self.prop,
        }
    }

    /// Context `∨`-introduction (right): inject `C` into a sum context.
    pub fn ctx_inr<G>(self) -> Thm<Either<G, C>, P> {
        Thm {
            ctx: Either::Right(self.ctx),
            prop: self.prop,
        }
    }
}

impl<C, G, P> Thm<Either<C, G>, P> {
    /// Context `∨`-elimination: recover which branch of the sum context held.
    pub fn ctx_or_elim(self) -> Either<Thm<C, P>, Thm<G, P>> {
        match self.ctx {
            Either::Left(c) => Either::Left(Thm {
                ctx: c,
                prop: self.prop,
            }),
            Either::Right(g) => Either::Right(Thm {
                ctx: g,
                prop: self.prop,
            }),
        }
    }
}
