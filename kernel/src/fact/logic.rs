use super::*;

impl<R> Fact<R> for () {
    fn check(&self, _db: &R) -> bool {
        true
    }
}

impl<R> Fact<R> for bool {
    fn check(&self, _db: &R) -> bool {
        *self
    }
}

impl<R, A, B> Fact<R> for (A, B)
where
    A: Fact<R>,
    B: Fact<R>,
{
    fn check(&self, db: &R) -> bool {
        self.0.check(db) && self.1.check(db)
    }
}

impl<R, F> Fact<R> for Option<F>
where
    F: Fact<R>,
{
    fn check(&self, db: &R) -> bool {
        self.as_ref().is_none_or(|f| f.check(db))
    }
}

impl<C, R> FactIn<C, R> for () {
    fn check_in(&self, _ctx: &C, _db: &R) -> bool {
        true
    }
}

impl<C, R> FactIn<C, R> for bool {
    fn check_in(&self, _ctx: &C, _db: &R) -> bool {
        *self
    }
}

impl<C, R, A, B> FactIn<C, R> for (A, B)
where
    A: FactIn<C, R>,
    B: FactIn<C, R>,
{
    fn check_in(&self, ctx: &C, db: &R) -> bool {
        self.0.check_in(ctx, db) && self.1.check_in(ctx, db)
    }
}

impl<C, R, F> FactIn<C, R> for Option<F>
where
    F: FactIn<C, R>,
{
    fn check_in(&self, ctx: &C, db: &R) -> bool {
        self.as_ref().is_none_or(|f| f.check_in(ctx, db))
    }
}

impl<C, Q, R> FactUnder<C, Q, R> for ()
where
    Q: FactIn<C, R>,
{
    fn check_under(&self, ctx: &C, binder: &Q, db: &R) -> bool {
        binder.check_in(ctx, db)
    }
}

impl<C, Q, R, F> FactUnder<C, Q, R> for Option<F>
where
    Q: FactIn<C, R>,
    F: FactUnder<C, Q, R>,
{
    fn check_under(&self, ctx: &C, binder: &Q, db: &R) -> bool {
        match self {
            None => binder.check_in(ctx, db),
            Some(f) => f.check_under(ctx, binder, db),
        }
    }
}
