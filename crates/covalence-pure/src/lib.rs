//! # `covalence-pure` — the base logic (the TCB floor)
//!
//! A small, value-directed kernel core. A [`Thm<C, P>`] certifies a specific
//! statement [`Stmt<C, P>`] — a context **value** `c: C` paired with a
//! proposition **value** `p: P`. Read `C ⊢ P`.
//!
//! - **`C` is the TCB.** The context value names (and carries) what is trusted:
//!   a pile of assumptions, a HOL context, WASM-evaluation facts. Growing the
//!   trusted base = a richer `C` (`Hol`, `WasmEval`, `WasmTrusted`, …); the
//!   logical content lives in `P`.
//! - **`P` is the statement.** An equation, a claim about a WASM program, a
//!   `bool`. Connectives are host types over the *values*: `(P, Q)` is `P ∧ Q`,
//!   [`Either<P, Q>`] is `P ∨ Q`, `()` is `⊤`, and the `bool` value `false` is
//!   `⊥`.
//!
//! ## The invariant (load-bearing)
//!
//! Every type is **assumed inhabited** (HOL-style), so the *existence* of a
//! `Thm<C, P>` at the type level is **not information** — you could always
//! exhibit some `p: P`. What a theorem certifies is that *this specific* `(c, p)`
//! is derivable. `Thm<C, bool>` is not "C proves bool"; it certifies a specific
//! bool, possibly `false` (→ C is inconsistent). The types are *sorts*; the
//! **values** are the content. So the kernel is **value-directed**: no API reads
//! meaning from type-level inhabitation (no `Option<Thm>` standing for
//! "provable"); eliminators dispatch on values, and ex-falso takes the caller's
//! specific target value.
//!
//! ## Soundness
//!
//! 1. **`Thm` is an unforgeable wrapper around `Stmt`** (private field, no public
//!    constructor): every line of this crate is TCB. `Stmt` is public and freely
//!    constructible — it carries *no* claim of truth (the untrusted analogue of a
//!    theorem).
//! 2. **Minting is gated by [`Thm::deduce`]**, which runs a [`Rule`] and blesses
//!    its output. A rule's `Self` is the *output context*, so the orphan rule
//!    reserves each context's rules to its own crate — a context controls every
//!    theorem minted in it. Premises ride inside the rule `R` as real `Thm`s
//!    (unforgeable ⇒ genuine); a `Rule` invoked directly yields a raw pair, never
//!    a `Thm`. The reserved constructive structural rules (`trivial` / `zip` /
//!    `fst` / `or_inl` / `or_elim` / `false_elim` / `ctx_*`) are trusted methods.
//!
//! ## Future directions
//!
//! - **Proof recording** — since `deduce` is the single choke point and a rule
//!   already bundles its premises, a recording container is just "a `Thm` that
//!   retains its `R`"; nested rules form the proof tree. (Not built yet.)
//! - **In-place rewriting** — mutate a prop value in place (returning auxiliary
//!   data) for efficient large-term edits. (Not built yet.)

use std::{convert::Infallible, ops::Deref};

use covalence_types::Either;

/// A statement `C ⊢ P` as plain data: a context value and a proposition value.
///
/// Public and freely constructible — it carries **no** claim of truth (the
/// untrusted analogue of a [`Thm`]). Rules compute on `Stmt`s; only [`Thm`]
/// blesses one as derived.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Stmt<C, P> {
    pub ctx: C,
    pub prop: P,
}

/// A theorem: a [`Stmt`] certified derived through the kernel.
///
/// The wrapped statement is **private with no public constructor** — this is
/// load-bearing (see the crate docs). A `Thm` is producible only by the trusted
/// methods here and by [`Thm::deduce`] (which runs a [`Rule`]).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Thm<C, P>(Stmt<C, P>);

/// Read-only access to the underlying statement. There is no `DerefMut`: a
/// `&mut Stmt` would expose `&mut prop` and let a live theorem be overwritten.
impl<C, P> Deref for Thm<C, P> {
    type Target = Stmt<C, P>;
    fn deref(&self) -> &Stmt<C, P> {
        &self.0
    }
}

/// Weaken a theorem to its statement (forget the proof).
impl<C, P> From<Thm<C, P>> for Stmt<C, P> {
    fn from(thm: Thm<C, P>) -> Stmt<C, P> {
        thm.0
    }
}

/// A `covalence-pure` inference rule. `Self` is the **output context** — the
/// orphan rule reserves the impl to `Self`'s crate, so a context controls every
/// theorem minted in it.
///
/// Premises ride inside `R` as real [`Thm`]s (unforgeable, hence genuine); the
/// rule opens them (via [`Deref`] to [`Stmt`] / [`Thm::into_stmt`]) and produces
/// a fresh `(context, prop)`. Untrusted on its own: invoked directly it yields a
/// raw pair — only [`Thm::deduce`] blesses it into a `Thm`.
pub trait Rule<R, P, E>: Sized {
    fn derive(rule: R) -> Result<(Self, P), E>;
}

impl<C, P> Thm<C, P> {
    /// The sole `Stmt → Thm` gate: run `rule` in output context `C` and bless the
    /// result. `Intro`/`Infer1`/`Infer2` are all this, with `R` carrying 0/1/2
    /// premise theorems.
    pub fn deduce<R, E>(rule: R) -> Result<Thm<C, P>, E>
    where
        C: Rule<R, P, E>,
    {
        C::derive(rule).map(|(ctx, prop)| Thm(Stmt { ctx, prop }))
    }

    /// Reborrow as a theorem of references.
    pub fn as_ref(&self) -> Thm<&C, &P> {
        Thm(Stmt {
            ctx: &self.0.ctx,
            prop: &self.0.prop,
        })
    }

    /// Weaken to the underlying statement (forget the proof). Sound: the result
    /// is a mere claim, not recombinable into a `Thm` without the kernel.
    pub fn into_stmt(self) -> Stmt<C, P> {
        self.0
    }

    /// Destructure into the owned context and prop values.
    pub fn into_parts(self) -> (C, P) {
        (self.0.ctx, self.0.prop)
    }

    /// `∧`-introduction across contexts: [`Union`] the contexts, pair the props.
    pub fn zip<C2, P2, U>(self, other: Thm<C2, P2>) -> Thm<U, (P, P2)>
    where
        U: Union<C, C2>,
    {
        Thm(Stmt {
            ctx: U::union(self.0.ctx, other.0.ctx),
            prop: (self.0.prop, other.0.prop),
        })
    }

    /// `∨`-introduction (left): `C ⊢ P` ⟹ `C ⊢ P ∨ Q`.
    pub fn or_inl<Q>(self) -> Thm<C, Either<P, Q>> {
        Thm(Stmt {
            ctx: self.0.ctx,
            prop: Either::Left(self.0.prop),
        })
    }

    /// `∨`-introduction (right): `C ⊢ P` ⟹ `C ⊢ Q ∨ P`.
    pub fn or_inr<Q>(self) -> Thm<C, Either<Q, P>> {
        Thm(Stmt {
            ctx: self.0.ctx,
            prop: Either::Right(self.0.prop),
        })
    }

    /// Context `∨`-introduction (left): inject `C` into a sum context.
    pub fn ctx_inl<G>(self) -> Thm<Either<C, G>, P> {
        Thm(Stmt {
            ctx: Either::Left(self.0.ctx),
            prop: self.0.prop,
        })
    }

    /// Context `∨`-introduction (right): inject `C` into a sum context.
    pub fn ctx_inr<G>(self) -> Thm<Either<G, C>, P> {
        Thm(Stmt {
            ctx: Either::Right(self.0.ctx),
            prop: self.0.prop,
        })
    }
}

/// `⊤`-introduction: every context certifies the unit prop `()`.
impl<C> Thm<C, ()> {
    pub fn trivial(ctx: C) -> Thm<C, ()> {
        Thm(Stmt { ctx, prop: () })
    }
}

/// The `bool` base case: a statement whose value *is* its truth.
impl<C> Thm<C, bool> {
    /// `⊢ T`: every context certifies the boolean `true`.
    pub fn truth(ctx: C) -> Thm<C, bool> {
        Thm(Stmt { ctx, prop: true })
    }

    /// `false`-elimination (value-directed ex falso). If the value is `false`,
    /// `C` certifies a falsehood — it is inconsistent — so any caller-supplied
    /// `target` is a theorem. If the value is `true`, there is no contradiction;
    /// the theorem is handed back unchanged.
    pub fn false_elim<P>(self, target: P) -> Result<Thm<C, P>, Self> {
        if self.0.prop {
            Err(self)
        } else {
            Ok(Thm(Stmt {
                ctx: self.0.ctx,
                prop: target,
            }))
        }
    }
}

/// `∧`-elimination.
impl<C, P, Q> Thm<C, (P, Q)> {
    /// Left: from `C ⊢ P ∧ Q` extract `C ⊢ P` (drops the `Q` witness).
    pub fn fst(self) -> Thm<C, P> {
        Thm(Stmt {
            ctx: self.0.ctx,
            prop: self.0.prop.0,
        })
    }

    /// Right: from `C ⊢ P ∧ Q` extract `C ⊢ Q` (drops the `P` witness).
    pub fn snd(self) -> Thm<C, Q> {
        Thm(Stmt {
            ctx: self.0.ctx,
            prop: self.0.prop.1,
        })
    }

    /// Both conjuncts. Needs `C: Clone` to duplicate the context.
    pub fn and_elim(self) -> (Thm<C, P>, Thm<C, Q>)
    where
        C: Clone,
    {
        let Stmt { ctx, prop: (p, q) } = self.0;
        (
            Thm(Stmt {
                ctx: ctx.clone(),
                prop: p,
            }),
            Thm(Stmt { ctx, prop: q }),
        )
    }
}

/// `∨`-elimination: decide a constructive disjunction by matching its witness.
impl<C, P, Q> Thm<C, Either<P, Q>> {
    pub fn or_elim(self) -> Either<Thm<C, P>, Thm<C, Q>> {
        let Stmt { ctx, prop } = self.0;
        match prop {
            Either::Left(p) => Either::Left(Thm(Stmt { ctx, prop: p })),
            Either::Right(q) => Either::Right(Thm(Stmt { ctx, prop: q })),
        }
    }
}

/// Context `∨`-elimination: recover which branch of a sum context held.
impl<C, G, P> Thm<Either<C, G>, P> {
    pub fn ctx_or_elim(self) -> Either<Thm<C, P>, Thm<G, P>> {
        let Stmt { ctx, prop } = self.0;
        match ctx {
            Either::Left(c) => Either::Left(Thm(Stmt { ctx: c, prop })),
            Either::Right(g) => Either::Right(Thm(Stmt { ctx: g, prop })),
        }
    }
}

/// Combine two trust-contexts into `Self` (the context of a [`Thm::zip`]).
///
/// Infallible: implementing `Union<C1, C2>` asserts `C1` and `C2` are
/// unconditionally mergeable into `Self`. If a merge can fail, model it with a
/// fallible [`Rule`] instead.
pub trait Union<C1, C2>: Sized {
    fn union(lhs: C1, rhs: C2) -> Self;
}

/// The identity rule: re-derive a theorem unchanged — the canonical minimal
/// [`Rule`], showing how a rule carries its premise. `Thm::deduce(Id(t))` ≡ `t`.
pub struct Id<C, P>(pub Thm<C, P>);

impl<C, P> Rule<Id<C, P>, P, Infallible> for C {
    fn derive(Id(thm): Id<C, P>) -> Result<(C, P), Infallible> {
        Ok(thm.into_parts())
    }
}
