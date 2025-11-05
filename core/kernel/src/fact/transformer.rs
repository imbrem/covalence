use crate::fact::transformer::fact_transformer_sealed::ValidFactTransformer;

use super::*;

/// Transform a fact
pub trait TransformFact<P, I, D, S, E>: ValidFactTransformer {
    type Out;

    fn precondition(self, input: I, ker: D, strategy: S) -> Result<Self::Out, E>;

    fn map_err<EO>(self, f: impl FnOnce(E) -> EO) -> MapErr<Self, impl FnOnce(E) -> EO, E>
    where
        Self: Sized,
    {
        MapErr {
            transformer: self,
            error: f,
            _input: std::marker::PhantomData,
        }
    }
}

impl<P, I, D, S, E> TransformFact<P, I, D, S, E> for () {
    type Out = I;

    fn precondition(self, input: I, _ker: D, _strategy: S) -> Result<I, E> {
        Ok(input)
    }
}

impl<P, I, D, E, L, S, R> TransformFact<P, I, D, S, E> for Either<L, R>
where
    L: TransformFact<P, I, D, S, E>,
    R: TransformFact<P, I, D, S, E, Out = L::Out>,
{
    type Out = L::Out;

    fn precondition(self, input: I, ker: D, strategy: S) -> Result<L::Out, E> {
        match self {
            Either::Left(this) => this.precondition(input, ker, strategy),
            Either::Right(this) => this.precondition(input, ker, strategy),
        }
    }
}

impl<P, I, D, E, S, B, C> TransformFact<P, I, D, S, E> for ControlFlow<B, C>
where
    B: TransformFact<P, I, D, S, E>,
    C: TransformFact<P, I, D, S, E>,
{
    type Out = ControlFlow<B::Out, C::Out>;

    fn precondition(self, input: I, ker: D, strategy: S) -> Result<Self::Out, E> {
        match self {
            ControlFlow::Continue(b) => b
                .precondition(input, ker, strategy)
                .map(ControlFlow::Continue),
            ControlFlow::Break(c) => c.precondition(input, ker, strategy).map(ControlFlow::Break),
        }
    }
}

impl<P, I, D, E, S, T> TransformFact<P, I, D, S, E> for Result<T, E>
where
    T: TransformFact<P, I, D, S, E>,
{
    type Out = T::Out;

    fn precondition(self, input: I, ker: D, strategy: S) -> Result<Self::Out, E> {
        match self {
            Ok(t) => t.precondition(input, ker, strategy),
            Err(e) => Err(e),
        }
    }
}

impl<'a, 'b, P, I, D, E, S, L, R> TransformFact<P, I, &'a D, &'b S, E> for (L, R)
where
    L: TransformFact<P, I, &'a D, &'b S, E>,
    R: TransformFact<P, L::Out, &'a D, &'b S, E>,
{
    type Out = R::Out;

    fn precondition(self, input: I, ker: &'a D, strategy: &'b S) -> Result<R::Out, E> {
        let mid = self.0.precondition(input, ker, strategy)?;
        self.1.precondition(mid, ker, strategy)
    }
}

impl<'a, 'b, P, I, M, O, D, E, S, L, R> TransformFact<P, I, &'a D, &'b mut S, E> for (L, R)
where
    L: for<'c> TransformFact<P, I, &'a D, &'c mut S, E, Out = M>,
    R: for<'c> TransformFact<P, M, &'a D, &'c mut S, E, Out = O>,
{
    type Out = O;

    fn precondition(self, input: I, ker: &'a D, strategy: &'b mut S) -> Result<O, E> {
        let mid = self.0.precondition(input, ker, strategy)?;
        self.1.precondition(mid, ker, strategy)
    }
}

impl<'a, P, I, M, O, D, E, S, L, R> TransformFact<P, I, &'a mut D, &'a mut S, E> for (L, R)
where
    L: for<'b> TransformFact<P, I, &'b mut D, &'b mut S, E, Out = M>,
    R: for<'b> TransformFact<P, M, &'b mut D, &'b mut S, E, Out = O>,
{
    type Out = O;

    fn precondition(self, input: I, ker: &'a mut D, strategy: &'a mut S) -> Result<O, E> {
        let mid = self.0.precondition(input, ker, strategy)?;
        self.1.precondition(mid, ker, strategy)
    }
}

/// A fact transformer which always fails
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Fail<E>(pub E);

impl<P, I, D, S, E> TransformFact<P, I, D, S, E> for Fail<E>
where
    E: Clone,
{
    type Out = I;

    fn precondition(self, _input: I, _ker: D, _strategy: S) -> Result<I, E> {
        Err(self.0)
    }
}

/// A fact transformer which maps errors
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct MapErr<T, F, E> {
    pub transformer: T,
    pub error: F,
    pub _input: std::marker::PhantomData<E>,
}

impl<P, I, D, S, EI, T, F, EO> TransformFact<P, I, D, S, EO> for MapErr<T, F, EI>
where
    T: TransformFact<P, I, D, S, EI>,
    F: FnOnce(EI) -> EO,
{
    type Out = T::Out;

    fn precondition(self, input: I, ker: D, strategy: S) -> Result<T::Out, EO> {
        self.transformer
            .precondition(input, ker, strategy)
            .map_err(self.error)
    }
}

/// Use the strategy to decide the next move
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Inspect<F, I, D, S> {
    pub choose: F,
    pub input: std::marker::PhantomData<I>,
    pub data: std::marker::PhantomData<D>,
    pub strategy: std::marker::PhantomData<S>,
}

pub fn inspect<F, I, D, S, T>(choose: F) -> Inspect<F, I, D, S>
where
    F: FnOnce(&I, &mut D, &mut S) -> T,
{
    Inspect {
        choose,
        input: std::marker::PhantomData,
        data: std::marker::PhantomData,
        strategy: std::marker::PhantomData,
    }
}

impl<P, I, D, S, E, F, T> TransformFact<P, I, D, S, E> for Inspect<F, I, D, S>
where
    F: FnOnce(&I, &mut D, &mut S) -> T,
    T: TransformFact<P, I, D, S, E>,
{
    type Out = T::Out;

    fn precondition(self, input: I, mut ker: D, mut strategy: S) -> Result<T::Out, E> {
        (self.choose)(&input, &mut ker, &mut strategy).precondition(input, ker, strategy)
    }
}

/// Iterate the given transformer
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Iterate<F, I, D, S> {
    pub body: F,
    pub input: std::marker::PhantomData<I>,
    pub data: std::marker::PhantomData<D>,
    pub strategy: std::marker::PhantomData<S>,
}

impl<'a, P, I, D, S, E, F, T, B> TransformFact<P, I, &'a mut D, &'a mut S, E>
    for Iterate<F, I, D, S>
where
    F: FnMut(&I, &mut D, &mut S) -> T,
    T: for<'b> TransformFact<P, I, &'b mut D, &'b mut S, E, Out = ControlFlow<B, I>>,
{
    type Out = B;

    fn precondition(
        mut self,
        mut input: I,
        ker: &'a mut D,
        strategy: &'a mut S,
    ) -> Result<Self::Out, E> {
        loop {
            match (self.body)(&input, ker, strategy).precondition(input, ker, strategy)? {
                ControlFlow::Continue(i) => {
                    input = i;
                }
                ControlFlow::Break(b) => break Ok(b),
            }
        }
    }
}

pub fn iterate<F, I, D, S, T, B, P>(body: F) -> Iterate<F, I, D, S>
where
    F: FnMut(&I, &mut D, &mut S) -> T,
    T: for<'b> TransformFact<P, I, &'b mut D, &'b mut S, B, Out = ControlFlow<B, I>>,
{
    Iterate {
        body,
        input: std::marker::PhantomData,
        data: std::marker::PhantomData,
        strategy: std::marker::PhantomData,
    }
}

mod fact_transformer_sealed {
    use super::*;

    pub trait ValidFactTransformer {}

    impl ValidFactTransformer for () {}

    impl<L, R> ValidFactTransformer for (L, R)
    where
        L: ValidFactTransformer,
        R: ValidFactTransformer,
    {
    }

    impl<L, R> ValidFactTransformer for Either<L, R>
    where
        L: ValidFactTransformer,
        R: ValidFactTransformer,
    {
    }

    impl<B, C> ValidFactTransformer for ControlFlow<B, C>
    where
        B: ValidFactTransformer,
        C: ValidFactTransformer,
    {
    }

    impl<T, E> ValidFactTransformer for Result<T, E> where T: ValidFactTransformer {}

    impl<T, F, E> ValidFactTransformer for MapErr<T, F, E> where T: ValidFactTransformer {}

    impl<E> ValidFactTransformer for Fail<E> {}

    impl<F, I, D, S, T> ValidFactTransformer for Inspect<F, I, D, S>
    where
        F: FnOnce(&I, &mut D, &mut S) -> T,
        T: ValidFactTransformer,
    {
    }

    impl<F, I, D, S, T> ValidFactTransformer for Iterate<F, I, D, S>
    where
        F: FnMut(&I, &mut D, &mut S) -> T,
        T: ValidFactTransformer,
    {
    }
}
