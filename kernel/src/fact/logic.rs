use either::Either;

use super::*;

pub trait ImpliesIn<C, F, D> {
    fn implies_in(self, ctx: &C) -> F;
}

pub trait Implies<F, D> {
    fn implies(self) -> F;
}

impl<C, F, G, D> Implies<Seq<C, G>, D> for Seq<C, F>
where
    F: ImpliesIn<C, G, D>,
{
    fn implies(self) -> Seq<C, G> {
        Seq {
            form: self.form.implies_in(&self.ctx),
            ctx: self.ctx,
        }
    }
}

pub trait IffIn<C, F, D> {
    fn iff_in(self, ctx: &C) -> F;
}

pub trait Iff<F, D> {
    fn iff(self) -> F;
}

impl<C, F, G, D> Iff<Seq<C, G>, D> for Seq<C, F>
where
    F: IffIn<C, G, D>,
{
    fn iff(self) -> Seq<C, G> {
        Seq {
            form: self.form.iff_in(&self.ctx),
            ctx: self.ctx,
        }
    }
}

pub trait TryIffIn<C, F, D>: Sized {
    fn try_iff_in(self, ctx: &C) -> Result<F, Self>;
}

pub trait TryIff<F, D>: Sized {
    fn try_iff(self) -> Result<F, Self>;
}

impl<C, F, G, D> TryIff<Seq<C, G>, D> for Seq<C, F>
where
    F: TryIffIn<C, G, D>,
{
    fn try_iff(self) -> Result<Seq<C, G>, Self> {
        match self.form.try_iff_in(&self.ctx) {
            Ok(form) => Ok(Seq {
                form,
                ctx: self.ctx,
            }),
            Err(form) => Err(Seq {
                form,
                ctx: self.ctx,
            }),
        }
    }
}

/// `()` is interpreted as the true proposition `⊤`
impl<R: ?Sized> CheckFact<()> for R {
    fn check(&self, _fact: &()) -> bool {
        true
    }
}

/// `bool` is interpreted as a proposition
impl<R: ?Sized> CheckFact<bool> for R {
    fn check(&self, fact: &bool) -> bool {
        *fact
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, A, B> CheckFact<(A, B)> for R
where
    R: CheckFact<A> + CheckFact<B>,
{
    fn check(&self, fact: &(A, B)) -> bool {
        self.check(&fact.0) && self.check(&fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, A, B> CheckFact<Either<A, B>> for R
where
    R: CheckFact<A> + CheckFact<B>,
{
    fn check(&self, fact: &Either<A, B>) -> bool {
        match fact {
            Either::Left(a) => self.check(a),
            Either::Right(b) => self.check(b),
        }
    }
}

/// `()` is interpreted as the true proposition `⊤`
impl<R: ?Sized> SetFactUnchecked<()> for R {
    fn set_unchecked(&mut self, _fact: &()) -> Result<(), StoreFailure> {
        Ok(())
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, A, B> SetFactUnchecked<(A, B)> for R
where
    R: SetFactUnchecked<A> + SetFactUnchecked<B>,
{
    fn set_unchecked(&mut self, fact: &(A, B)) -> Result<(), StoreFailure> {
        self.set_unchecked(&fact.0)?;
        self.set_unchecked(&fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, A, B> SetFactUnchecked<Either<A, B>> for R
where
    R: SetFactUnchecked<A> + SetFactUnchecked<B>,
{
    fn set_unchecked(&mut self, fact: &Either<A, B>) -> Result<(), StoreFailure> {
        match fact {
            Either::Left(a) => self.set_unchecked(a),
            Either::Right(b) => self.set_unchecked(b),
        }
    }
}

/// `()` is interpreted as the true proposition `⊤`
impl<R: ?Sized, C> CheckFormula<C, ()> for R {
    fn check_in(&self, _ctx: C, _db: &()) -> bool {
        true
    }
}

/// `bool` is interpreted as a proposition
impl<R: ?Sized, C> CheckFormula<C, bool> for R {
    fn check_in(&self, _ctx: C, fact: &bool) -> bool {
        *fact
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, C, A, B> CheckFormula<C, (A, B)> for R
where
    R: CheckFormula<C, A> + CheckFormula<C, B>,
    C: Copy,
{
    fn check_in(&self, ctx: C, fact: &(A, B)) -> bool {
        self.check_in(ctx, &fact.0) && self.check_in(ctx, &fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, C, A, B> CheckFormula<C, Either<A, B>> for R
where
    R: CheckFormula<C, A> + CheckFormula<C, B>,
    C: Copy,
{
    fn check_in(&self, ctx: C, fact: &Either<A, B>) -> bool {
        match fact {
            Either::Left(a) => self.check_in(ctx, a),
            Either::Right(b) => self.check_in(ctx, b),
        }
    }
}

/// `()` is interpreted as the true proposition `⊤`
impl<R: ?Sized, C> SetFactUncheckedIn<C, ()> for R {
    fn set_unchecked_in(&mut self, _ctx: C, _fact: &()) -> Result<(), StoreFailure> {
        Ok(())
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, C, A, B> SetFactUncheckedIn<C, (A, B)> for R
where
    R: SetFactUncheckedIn<C, A> + SetFactUncheckedIn<C, B>,
    C: Copy,
{
    fn set_unchecked_in(&mut self, ctx: C, fact: &(A, B)) -> Result<(), StoreFailure> {
        self.set_unchecked_in(ctx, &fact.0)?;
        self.set_unchecked_in(ctx, &fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, C, A, B> SetFactUncheckedIn<C, Either<A, B>> for R
where
    R: SetFactUncheckedIn<C, A> + SetFactUncheckedIn<C, B>,
    C: Copy,
{
    fn set_unchecked_in(&mut self, ctx: C, fact: &Either<A, B>) -> Result<(), StoreFailure> {
        match fact {
            Either::Left(a) => self.set_unchecked_in(ctx, a),
            Either::Right(b) => self.set_unchecked_in(ctx, b),
        }
    }
}
