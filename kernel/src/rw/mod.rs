use crate::{
    Theorem,
    error::KernelError,
    fact::RwIn,
    store::{Ctx, LocalTerm},
};

mod transform_sealed {
    use crate::{error::KernelError, id::KernelId};

    pub trait MapIntoEqSealed<I, E, S, D> {}

    pub trait MapToEqSealed<I, E, S, D> {}

    pub trait TransformState<C, D> {
        fn check(&mut self, ctx: &C, id: KernelId, relocatable: bool) -> Result<(), KernelError>;
    }
}

use transform_sealed::{MapIntoEqSealed, MapToEqSealed, TransformState};

pub trait MapIntoEq<I, E, S, D>: MapIntoEqSealed<I, E, S, D> {
    type IntoEq;

    fn into_eq(self, lhs: I, state: &mut S) -> Result<Self::IntoEq, E>;
}

pub trait MapToEq<I, E, S, D>: MapToEqSealed<I, E, S, D> {
    type ToEq;

    fn to_eq(self, lhs: &I, state: &mut S) -> Result<Self::ToEq, E>;
}

impl<I, E, S, D> MapIntoEqSealed<I, E, S, D> for () {}

impl<I, E, S, D> MapIntoEq<I, E, S, D> for () {
    type IntoEq = I;

    fn into_eq(self, lhs: I, _state: &mut S) -> Result<I, E> {
        Ok(lhs)
    }
}

impl<I, E, S, D> MapToEqSealed<I, E, S, D> for () {}

impl<I, E, S, D> MapToEq<I, E, S, D> for ()
where
    I: Clone,
{
    type ToEq = I;

    fn to_eq(self, lhs: &I, _state: &mut S) -> Result<I, E> {
        Ok(lhs.clone())
    }
}

impl<'a, C, I, L, R, S, D> MapToEqSealed<I, KernelError, S, D> for &'a Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    I: LocalTerm<C, D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
}

impl<C, I, L, R, S, D> MapToEqSealed<I, KernelError, S, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    I: LocalTerm<C, D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
}

impl<'a, C, I, L, R, S, D> MapToEq<I, KernelError, S, D> for &'a Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    I: LocalTerm<C, D> + PartialEq<L>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
    S: TransformState<C, D>,
{
    type ToEq = &'a R;

    fn to_eq(self, lhs: &I, state: &mut S) -> Result<&'a R, KernelError> {
        state.check(
            &self.stmt.ctx,
            self.id,
            self.0.relocatable() && self.1.relocatable(),
        )?;
        if *lhs != self.0 {
            return Err(KernelError::EqMismatch);
        }
        Ok(&self.1)
    }
}

impl<'a, C, I, L, R, S, D> MapToEq<I, KernelError, S, D> for Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    I: LocalTerm<C, D> + PartialEq<L>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
    S: TransformState<C, D>,
{
    type ToEq = R;

    fn to_eq(self, lhs: &I, state: &mut S) -> Result<R, KernelError> {
        (&self).to_eq(lhs, state)?;
        Ok(self.into_inner().stmt.1)
    }
}

// #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub struct BorrowIn<M>(pub M);

// impl<M, I, E, S, D> MapIntoEqSealed<I, E, S, D> for BorrowIn<M> where M: MapToEq<I, E, S, D> {}

// impl<M, I, E, S, D> MapIntoEq<I, E, S, D> for BorrowIn<M>
// where
//     M: MapToEq<I, E, S, D>,
// {
//     type IntoEq = M::ToEq;

//     fn into_eq(self, lhs: I, state: &mut S) -> Result<Self::IntoEq, E> {
//         self.0.to_eq(&lhs, state)
//     }
// }

// impl<T, U, I, E, S, D> MapIntoEqSealed<I, E, S, D> for (T, U)
// where
//     T: MapIntoEq<I, E, S, D>,
//     U: MapIntoEq<T::IntoEq, E, S, D>,
// {
// }

// impl<T, U, I, E, S, D> MapIntoEq<I, E, S, D> for (T, U)
// where
//     T: MapIntoEq<I, E, S, D>,
//     U: MapIntoEq<T::IntoEq, E, S, D>,
// {
//     type IntoEq = U::IntoEq;

//     fn into_eq(self, lhs: I, state: &mut S) -> Result<Self::IntoEq, E> {
//         let mid = self.0.into_eq(lhs, state)?;
//         self.1.into_eq(mid, state)
//     }
// }
