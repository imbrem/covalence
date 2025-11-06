use either::Either;

use super::*;

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
    fn set_unchecked(&mut self, _fact: &()) -> bool {
        true
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, A, B> SetFactUnchecked<(A, B)> for R
where
    R: SetFactUnchecked<A> + SetFactUnchecked<B>,
{
    fn set_unchecked(&mut self, fact: &(A, B)) -> bool {
        self.set_unchecked(&fact.0) && self.set_unchecked(&fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, A, B> SetFactUnchecked<Either<A, B>> for R
where
    R: SetFactUnchecked<A> + SetFactUnchecked<B>,
{
    fn set_unchecked(&mut self, fact: &Either<A, B>) -> bool {
        match fact {
            Either::Left(a) => self.set_unchecked(a),
            Either::Right(b) => self.set_unchecked(b),
        }
    }
}

/// `()` is interpreted as the true proposition `⊤`
impl<R: ?Sized, C> CheckFactIn<C, ()> for R {
    fn check_in(&self, _ctx: C, _db: &()) -> bool {
        true
    }
}

/// `bool` is interpreted as a proposition
impl<R: ?Sized, C> CheckFactIn<C, bool> for R {
    fn check_in(&self, _ctx: C, fact: &bool) -> bool {
        *fact
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, C, A, B> CheckFactIn<C, (A, B)> for R
where
    R: CheckFactIn<C, A> + CheckFactIn<C, B>,
    C: Copy,
{
    fn check_in(&self, ctx: C, fact: &(A, B)) -> bool {
        self.check_in(ctx, &fact.0) && self.check_in(ctx, &fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, C, A, B> CheckFactIn<C, Either<A, B>> for R
where
    R: CheckFactIn<C, A> + CheckFactIn<C, B>,
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
    fn set_unchecked_in(&mut self, _ctx: C, _fact: &()) -> bool {
        true
    }
}

/// `(A, B)` is interpreted as the conjunction `A ∧ B`
impl<R: ?Sized, C, A, B> SetFactUncheckedIn<C, (A, B)> for R
where
    R: SetFactUncheckedIn<C, A> + SetFactUncheckedIn<C, B>,
    C: Copy,
{
    fn set_unchecked_in(&mut self, ctx: C, fact: &(A, B)) -> bool {
        self.set_unchecked_in(ctx, &fact.0) && self.set_unchecked_in(ctx, &fact.1)
    }
}

/// `Either<A, B>` is interpreted as the disjunction `A ∨ B`
impl<R: ?Sized, C, A, B> SetFactUncheckedIn<C, Either<A, B>> for R
where
    R: SetFactUncheckedIn<C, A> + SetFactUncheckedIn<C, B>,
    C: Copy,
{
    fn set_unchecked_in(&mut self, ctx: C, fact: &Either<A, B>) -> bool {
        match fact {
            Either::Left(a) => self.set_unchecked_in(ctx, a),
            Either::Right(b) => self.set_unchecked_in(ctx, b),
        }
    }
}
