use std::{convert::Infallible, fmt::Debug};

use covalence_types::Either;

/// A `covalence-pure` introduction rule
pub trait Intro<R, P>: Sized {
    type Err;

    fn intro(self, rule: R) -> Result<(Self, P), Self::Err>;
}

/// A `covalence-pure` unary inference rule
pub trait Infer1<C, R, P, Q>: Sized {
    type Err;

    fn infer_from(ctx: C, rule: R, prem: P) -> Result<(Self, Q), Self::Err>;
}

/// A `covalence-pure` binary inference rule
pub trait Infer2<C1, C2, R, P1, P2, Q>: Sized {
    type Err;

    fn infer_from(ctx: (C1, C2), rule: R, prem: (P1, P2)) -> Result<(Self, Q), Self::Err>;
}

/// A `covalence-pure` rewriting rule
pub trait RwIn<R, P, D>: Sized {
    type Err;

    fn rw_in(&mut self, rule: R, prem: &mut P) -> Result<D, Self::Err>;
}

/// A `covalence-pure` theorem
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Thm<C, P> {
    ctx: C,
    prop: P,
}

impl<C, P> Thm<C, P> {
    pub fn new<R>(ctx: C, rule: R) -> Thm<C, P>
    where
        C: Intro<R, P>,
        C::Err: Debug,
    {
        Self::intro(ctx, rule).expect("Thm::new: intro failed")
    }

    pub fn intro<R>(ctx: C, rule: R) -> Result<Thm<C, P>, C::Err>
    where
        C: Intro<R, P>,
    {
        let (ctx, prop) = ctx.intro(rule)?;
        Ok(Thm { ctx, prop })
    }

    pub fn as_ref(&self) -> Thm<&C, &P> {
        Thm {
            ctx: &self.ctx,
            prop: &self.prop,
        }
    }

    pub fn as_mut(&mut self) -> Thm<&mut C, &mut P> {
        Thm {
            ctx: &mut self.ctx,
            prop: &mut self.prop,
        }
    }

    pub fn infer<G, R, Q>(self, rule: R) -> Result<Thm<G, Q>, G::Err>
    where
        G: Infer1<C, R, P, Q>,
    {
        let (ctx, prop) = G::infer_from(self.ctx, rule, self.prop)?;
        Ok(Thm { ctx, prop })
    }

    pub fn rw_in<R, D>(&mut self, rule: R) -> Result<D, C::Err>
    where
        C: RwIn<R, P, D>,
    {
        self.ctx.rw_in(rule, &mut self.prop)
    }

    pub fn apply<C2, U, R, P2, Q>(self, rule: R, other: Thm<C2, P2>) -> Result<Thm<U, Q>, U::Err>
    where
        U: Infer2<C, C2, R, P, P2, Q>,
    {
        let (ctx, prop) = U::infer_from((self.ctx, other.ctx), rule, (self.prop, other.prop))?;
        Ok(Thm { ctx, prop })
    }
}

/// The trivially true proposition
impl<C> Intro<C, ()> for C {
    type Err = Infallible;

    fn intro(self, _rule: C) -> Result<(Self, ()), Self::Err> {
        Ok((self, ()))
    }
}

/// The identity rule
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

/// Left injection
pub struct Inl;

impl<C, P, Q> Infer1<C, Inl, P, Either<P, Q>> for C {
    type Err = Infallible;

    fn infer_from(ctx: C, _rule: Inl, prem: P) -> Result<(Self, Either<P, Q>), Self::Err> {
        Ok((ctx, Either::Left(prem)))
    }
}

/// Right injection
pub struct Inr;

impl<C, P, Q> Infer1<C, Inr, Q, Either<P, Q>> for C {
    type Err = Infallible;

    fn infer_from(ctx: C, _rule: Inr, prem: Q) -> Result<(Self, Either<P, Q>), Self::Err> {
        Ok((ctx, Either::Right(prem)))
    }
}

impl<C, P, Q> Thm<C, Either<P, Q>> {
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

/// First projection
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

/// Second projection
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

/// `covalence-pure` context union
pub trait Union<C1, C2>: Sized {
    fn union(lhs: C1, rhs: C2) -> Self;
}

/// Product of rules
pub struct Prod<R1, R2>(pub R1, pub R2);

impl<C1, C2, R1, R2, P1, P2, Q1, Q2, U> Infer2<C1, C2, Prod<R1, R2>, P1, P2, (Q1, Q2)> for U
where
    C1: Infer1<C1, R1, P1, Q1>,
    C2: Infer1<C2, R2, P2, Q2, Err = C1::Err>,
    U: Union<C1, C2>,
{
    type Err = C1::Err;

    fn infer_from(
        (lctx, rctx): (C1, C2),
        Prod(lrule, rrule): Prod<R1, R2>,
        (lprem, rprem): (P1, P2),
    ) -> Result<(U, (Q1, Q2)), C1::Err> {
        let (lctx, lprop) = C1::infer_from(lctx, lrule, lprem)?;
        let (rctx, rprop) = C2::infer_from(rctx, rrule, rprem)?;
        let ctx = U::union(lctx, rctx);
        Ok((ctx, (lprop, rprop)))
    }
}

// === Contexts distribute with `Either` ===

impl<C, P> Thm<C, P> {
    pub fn ctx_inl<G>(self) -> Thm<Either<C, G>, P> {
        Thm {
            ctx: Either::Left(self.ctx),
            prop: self.prop,
        }
    }

    pub fn ctx_inr<G>(self) -> Thm<Either<G, C>, P> {
        Thm {
            ctx: Either::Right(self.ctx),
            prop: self.prop,
        }
    }
}

impl<C, G, P> Thm<Either<C, G>, P> {
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
