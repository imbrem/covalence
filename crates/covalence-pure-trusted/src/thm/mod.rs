//! Kernel core: [`Stmt`], [`MThm`], and the reserved constructive structural
//! rules. The trusted traits live in submodules — [`Rule`] (`rule`), [`Union`]
//! (`union`) — the statement surface in `stmt` ([`IsStmt`], [`GetCtx`] /
//! [`GetProp`] / [`IntoParts`]), and pointer support in `deref` ([`TrustedDeref`]
//! / [`TrustedTake`]).

use std::marker::PhantomData;

use covalence_types::Either;

mod deref;
mod erased;
mod rule;
mod seq;
mod stmt;
mod union;

pub use deref::{TrustedDeref, TrustedTake};
pub use erased::CtxMismatch;
pub use rule::{Id, Rule};
pub use stmt::{GetCtx, GetProp, IntoParts, IsStmt};
pub use union::{TryUnion, Union};

/// The canonical statement `K ⊢ P` as plain data: a context value and a
/// proposition value.
///
/// Public and freely constructible — it carries **no** claim of truth (the
/// untrusted analogue of a [`MThm`]), and is the canonical [`IsStmt`] /
/// [`GetCtx`] / [`GetProp`] / [`IntoParts`] implementor that every other
/// representation reduces to.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Stmt<K, P> {
    pub ctx: K,
    pub prop: P,
}

/// A **metatheorem**: a *derived* statement `S` certified in kernel `K`, whose
/// logical `(context, prop)` are the type tags `K` and `P`.
///
/// Named `MThm` (not `Thm`) deliberately — this is the *meta*-level certificate
/// over a trust domain `K`, distinct from an object logic's own `Thm` (HOL's,
/// say). The intended downstream pattern is a per-crate alias fixing `K` to that
/// crate's context, with an optional extension point:
/// ```ignore
/// pub type Thm<P, K = ()> = MThm<MyCrateCtx<K>, P>;
/// ```
///
/// `S` defaults to the canonical [`Stmt<K, P>`]; later it ranges over richer
/// representations (a borrow, an `Arc`, an `Arc<dyn TypedTerm>`, …). `K` and `P`
/// are phantom tags — the real data lives in `S`.
///
/// The fields are **private with no public constructor** — load-bearing (see the
/// crate docs). An `MThm` is producible only by the trusted methods here and by
/// [`crate::Derive::derive`], and only when `K: IsStmt<S, P>` (so the context
/// admits the representation).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MThm<K, P, S = Stmt<K, P>>(S, PhantomData<fn() -> (K, P)>);

impl<K, P, S> MThm<K, P, S> {
    /// The single internal constructor: bless a statement `S` into a theorem,
    /// **gated by `K: IsStmt<S, P>`** — only a context that admits the
    /// representation can form it. (Private; external code cannot build a `MThm`.)
    fn new(stmt: S) -> MThm<K, P, S>
    where
        K: IsStmt<S, P>,
    {
        MThm(stmt, PhantomData)
    }
}

/// Weaken a (canonical) theorem to its statement (forget the proof).
impl<K, P> From<MThm<K, P>> for Stmt<K, P> {
    fn from(thm: MThm<K, P>) -> Stmt<K, P> {
        thm.0
    }
}

impl<K, P> MThm<K, P> {
    /// Reborrow as a theorem of references.
    pub fn as_ref(&self) -> MThm<&K, &P> {
        MThm::new(Stmt {
            ctx: &self.0.ctx,
            prop: &self.0.prop,
        })
    }

    /// Weaken to the underlying statement (forget the proof). Sound: the result
    /// is a mere claim, not recombinable into a `MThm` without the kernel.
    pub fn into_stmt(self) -> Stmt<K, P> {
        self.0
    }

    /// Destructure into the owned context and prop values.
    pub fn into_parts(self) -> (K, P) {
        (self.0.ctx, self.0.prop)
    }

    /// `∨`-introduction (left): `K ⊢ P` ⟹ `K ⊢ P ∨ Q`.
    pub fn or_inl<Q>(self) -> MThm<K, Either<P, Q>> {
        MThm::new(Stmt {
            ctx: self.0.ctx,
            prop: Either::Left(self.0.prop),
        })
    }

    /// `∨`-introduction (right): `K ⊢ P` ⟹ `K ⊢ Q ∨ P`.
    pub fn or_inr<Q>(self) -> MThm<K, Either<Q, P>> {
        MThm::new(Stmt {
            ctx: self.0.ctx,
            prop: Either::Right(self.0.prop),
        })
    }

    /// Context `∨`-introduction (left): inject `K` into a sum context.
    pub fn ctx_inl<K2>(self) -> MThm<Either<K, K2>, P> {
        MThm::new(Stmt {
            ctx: Either::Left(self.0.ctx),
            prop: self.0.prop,
        })
    }

    /// Context `∨`-introduction (right): inject `K` into a sum context.
    pub fn ctx_inr<K2>(self) -> MThm<Either<K2, K>, P> {
        MThm::new(Stmt {
            ctx: Either::Right(self.0.ctx),
            prop: self.0.prop,
        })
    }
}

/// `⊤`-introduction: every context certifies the unit prop `()`.
impl<K> MThm<K, ()> {
    pub fn trivial(ctx: K) -> MThm<K, ()> {
        MThm::new(Stmt { ctx, prop: () })
    }
}

/// The `bool` base case: a statement whose value *is* its truth.
impl<K> MThm<K, bool> {
    /// `⊢ T`: every context certifies the boolean `true`.
    pub fn truth(ctx: K) -> MThm<K, bool> {
        MThm::new(Stmt { ctx, prop: true })
    }

    /// `false`-elimination (value-directed ex falso). If the value is `false`,
    /// `K` certifies a falsehood — it is inconsistent — so any caller-supplied
    /// `target` is a theorem. If the value is `true`, there is no contradiction;
    /// the theorem is handed back unchanged.
    pub fn false_elim<P>(self, target: P) -> Result<MThm<K, P>, Self> {
        if self.0.prop {
            Err(self)
        } else {
            Ok(MThm::new(Stmt {
                ctx: self.0.ctx,
                prop: target,
            }))
        }
    }
}

/// `∧`-elimination.
impl<K, P, Q> MThm<K, (P, Q)> {
    /// Left: from `K ⊢ P ∧ Q` extract `K ⊢ P` (drops the `Q` witness).
    pub fn fst(self) -> MThm<K, P> {
        MThm::new(Stmt {
            ctx: self.0.ctx,
            prop: self.0.prop.0,
        })
    }

    /// Right: from `K ⊢ P ∧ Q` extract `K ⊢ Q` (drops the `P` witness).
    pub fn snd(self) -> MThm<K, Q> {
        MThm::new(Stmt {
            ctx: self.0.ctx,
            prop: self.0.prop.1,
        })
    }

    /// Both conjuncts. Needs `K: Clone` to duplicate the context.
    pub fn and_elim(self) -> (MThm<K, P>, MThm<K, Q>)
    where
        K: Clone,
    {
        let Stmt { ctx, prop: (p, q) } = self.0;
        (
            MThm::new(Stmt {
                ctx: ctx.clone(),
                prop: p,
            }),
            MThm::new(Stmt { ctx, prop: q }),
        )
    }
}

/// `∨`-elimination: decide a constructive disjunction by matching its witness.
impl<K, P, Q> MThm<K, Either<P, Q>> {
    pub fn or_elim(self) -> Either<MThm<K, P>, MThm<K, Q>> {
        let Stmt { ctx, prop } = self.0;
        match prop {
            Either::Left(p) => Either::Left(MThm::new(Stmt { ctx, prop: p })),
            Either::Right(q) => Either::Right(MThm::new(Stmt { ctx, prop: q })),
        }
    }
}

/// Context `∨`-elimination: recover which branch of a sum context held.
impl<K, K2, P> MThm<Either<K, K2>, P> {
    pub fn ctx_or_elim(self) -> Either<MThm<K, P>, MThm<K2, P>> {
        let Stmt { ctx, prop } = self.0;
        match ctx {
            Either::Left(c) => Either::Left(MThm::new(Stmt { ctx: c, prop })),
            Either::Right(g) => Either::Right(MThm::new(Stmt { ctx: g, prop })),
        }
    }
}
