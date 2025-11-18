use crate::{
    fact::{Rw, RwIn},
    store::{Ctx, LocalTerm},
};

use super::*;

/// An equality mismatch error
#[derive(Debug, Copy, Clone, Error, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct EqMismatch;

impl Display for EqMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "equality mismatch")
    }
}

impl<L, R> Rw<L, R> {
    /// Swap the left- and right-hand sides of this equation
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::fact::Rw;
    /// # let x = 1; let y = 2;
    /// assert_eq!(Rw(x, y).symm(), Rw(y, x));
    /// ```
    pub fn symm(self) -> Rw<R, L> {
        Rw(self.1, self.0)
    }

    /// Transitivity of equality
    ///
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::fact::Rw;
    /// # let x = 1; let y = 2; let z = 3;
    /// assert_eq!(Rw(x, y).trans(Rw(y, z)), Ok(Rw(x, z)));
    /// assert_ne!(y, z);
    /// Rw(x, y).trans(Rw(z, x)).unwrap_err();
    /// ```
    pub fn trans<L2, R2>(self, other: Rw<L2, R2>) -> Result<Rw<L, R2>, EqMismatch>
    where
        R: PartialEq<L2>,
    {
        if self.1 != other.0 {
            return Err(EqMismatch);
        }
        Ok(Rw(self.0, other.1))
    }

    /// Borrow this equation
    pub fn as_ref(&self) -> Rw<&L, &R> {
        Rw(&self.0, &self.1)
    }
}

impl<C, L, R> RwIn<C, L, R> {
    /// Swap the left- and right-hand sides of this equation
    pub fn symm(self) -> RwIn<C, R, L> {
        RwIn {
            ctx: self.ctx,
            form: self.form.symm(),
        }
    }

    /// Transitivity of equality
    pub fn trans<C2, L2, R2>(self, other: RwIn<C2, L2, R2>) -> Result<RwIn<C, L, R2>, EqMismatch>
    where
        C: PartialEq<C2>,
        R: PartialEq<L2>,
    {
        if self.ctx != other.ctx {
            return Err(EqMismatch);
        }
        Ok(RwIn {
            ctx: self.ctx,
            form: self.form.trans(other.form)?,
        })
    }

    /// Borrow this equation-in-context
    pub fn eqn_as_ref(&self) -> RwIn<C, &L, &R>
    where
        C: Copy,
    {
        RwIn {
            ctx: self.ctx,
            form: self.form.as_ref(),
        }
    }
}

impl<C, T, D> Theorem<RwIn<C, T>, D>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    /// Construct an equation from two equal terms
    pub fn of_refl(id: KernelId, ctx: C, tm: T) -> Result<Theorem<RwIn<C, T>, D>, KernelError>
    where
        T: Clone,
    {
        Ok(Theorem::new_unchecked(
            id,
            RwIn {
                ctx,
                form: Rw(tm.clone(), tm),
            },
        ))
    }
}

impl<C, T, D> Theorem<RwIn<C, &T, T>, D>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    /// A term is equal to its clone
    pub fn eq_clone(id: KernelId, ctx: C, tm: &T) -> Result<Theorem<RwIn<C, &T, T>, D>, KernelError>
    where
        T: Clone,
    {
        Ok(Theorem::new_unchecked(
            id,
            RwIn {
                ctx,
                form: Rw(tm, tm.clone()),
            },
        ))
    }
}

impl<C, L, R, D> Theorem<RwIn<C, L, R>, D>
where
    C: Ctx<D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
{
    /// Construct an equation from two equal terms
    pub fn of_eq(
        id: KernelId,
        ctx: C,
        lhs: L,
        rhs: R,
    ) -> Result<Theorem<RwIn<C, L, R>, D>, KernelError>
    where
        L: PartialEq<R>,
    {
        if lhs != rhs {
            return Err(KernelError::EqMismatch);
        }
        Ok(Theorem::new_unchecked(
            id,
            RwIn {
                ctx,
                form: Rw(lhs, rhs),
            },
        ))
    }

    /// Construct an equation using `Into`
    pub fn eq_into(id: KernelId, ctx: C, lhs: L) -> Theorem<RwIn<C, L, R>, D>
    where
        L: Clone + Into<R>,
    {
        Theorem::new_unchecked(
            id,
            RwIn {
                ctx,
                form: Rw(lhs.clone(), lhs.into()),
            },
        )
    }

    /// Construct an equation using `TryInto`
    pub fn eq_try_into(id: KernelId, ctx: C, lhs: L) -> Result<Theorem<RwIn<C, L, R>, D>, L::Error>
    where
        L: Clone + TryInto<R>,
    {
        Ok(Theorem::new_unchecked(
            id,
            RwIn {
                ctx,
                form: Rw(lhs.clone(), lhs.try_into()?),
            },
        ))
    }

    /// Swap the left- and right-hand sides of this equation
    pub fn symm(self) -> Theorem<RwIn<C, R, L>, D> {
        Theorem::new_unchecked(self.session, self.fact.symm())
    }

    /// Transitivity of equality
    pub fn trans<C2, L2, R2>(
        self,
        other: Theorem<RwIn<C2, L2, R2>, D>,
    ) -> Result<Theorem<RwIn<C, L, R2>, D>, KernelError>
    where
        C: PartialEq<C2>,
        R: PartialEq<L2>,
        C2: Ctx<D>,
        L2: LocalTerm<C, D>,
        R2: LocalTerm<C, D>,
    {
        self.compat(&other)?;
        Ok(Theorem::new_unchecked(
            self.session,
            self.fact.trans(other.fact)?,
        ))
    }

    /// Borrow this equation-in-context
    pub fn eq_as_ref(&self) -> Theorem<RwIn<C, &L, &R>, D>
    where
        C: Copy,
    {
        Theorem::new_unchecked(self.session, self.fact.eqn_as_ref())
    }
}
