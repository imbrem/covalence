use either::Either;

use super::*;

pub trait ImpliesIn<C, F, D> {
    fn implies_in(self, ctx: &C) -> F;
}

pub trait IffIn<C, F, D> {
    fn iff_in(self, ctx: &C) -> F;
}

pub trait TryIffIn<C, F, D>: Sized {
    fn try_iff_in(self, ctx: &C) -> Result<F, Self>;
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
