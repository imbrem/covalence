use crate::fact::{Eqn, EqnIn};

use super::*;

/// An equality mismatch error
#[derive(Debug, Copy, Clone, Error, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct EqMismatch;

impl Display for EqMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "equality mismatch")
    }
}

pub trait InterEq<L, R> {
    fn inter_eq(&self, lhs: &L, rhs: &R) -> bool;
}

impl<L, R> InterEq<L, R> for ()
where
    L: PartialEq<R>,
    R: PartialEq<L>,
{
    fn inter_eq(&self, lhs: &L, rhs: &R) -> bool {
        lhs == rhs
    }
}

impl<L, R> Eqn<L, R> {
    /// Swap the left- and right-hand sides of this equation
    /// 
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::fact::Eqn;
    /// # let x = 1; let y = 2;
    /// assert_eq!(Eqn(x, y).symm(), Eqn(y, x));
    /// ```
    pub fn symm(self) -> Eqn<R, L> {
        Eqn(self.1, self.0)
    }

    /// Transitivity of equality
    /// 
    /// # Examples
    /// ```rust
    /// # use covalence_kernel::fact::Eqn;
    /// # let x = 1; let y = 2; let z = 3;
    /// assert_eq!(Eqn(x, y).trans(Eqn(y, z)), Ok(Eqn(x, z)));
    /// assert_ne!(y, z);
    /// Eqn(x, y).trans(Eqn(z, x)).unwrap_err();
    /// ```
    pub fn trans<L2, R2>(self, other: Eqn<L2, R2>) -> Result<Eqn<L, R2>, EqMismatch>
    where
        (): InterEq<R, L2>,
    {
        if ().inter_eq(&self.1, &other.0) {
            Ok(Eqn(self.0, other.1))
        } else {
            Err(EqMismatch)
        }
    }

    /// Borrow this equation
    pub fn as_ref<'a>(&'a self) -> Eqn<&'a L, &'a R> {
        Eqn(&self.0, &self.1)
    }

    //TODO: localization

    //TODO: congruence

    //TODO: stepping
}

impl<C, L, R> EqnIn<C, L, R> {
    /// Swap the left- and right-hand sides of this equation
    pub fn symm(self) -> EqnIn<C, R, L> {
        EqnIn {
            ctx: self.ctx,
            stmt: self.stmt.symm(),
        }
    }

    /// Transitivity of equality
    pub fn trans<L2, R2>(self, other: EqnIn<C, L2, R2>) -> Result<EqnIn<C, L, R2>, EqMismatch>
    where
        (): InterEq<R, L2>,
        (): InterEq<C, C>,
    {
        if !().inter_eq(&self.ctx, &other.ctx) {
            return Err(EqMismatch);
        }
        Ok(EqnIn {
            ctx: self.ctx,
            stmt: self.stmt.trans(other.stmt)?,
        })
    }

    /// Borrow this equation-in-context
    pub fn as_ref<'a>(&'a self) -> EqnIn<C, &'a L, &'a R>
    where
        C: Copy,
    {
        EqnIn {
            ctx: self.ctx,
            stmt: self.stmt.as_ref(),
        }
    }
}

impl<C, L, R> Theorem<EqnIn<C, L, R>> {
    /// Swap the left- and right-hand sides of this equation
    pub fn symm(self) -> Theorem<EqnIn<C, R, L>> {
        Theorem {
            stmt: self.stmt.symm(),
            id: self.id,
        }
    }

    /// Transitivity of equality
    pub fn trans<L2, R2>(
        self,
        other: Theorem<EqnIn<C, L2, R2>>,
    ) -> Result<Theorem<EqnIn<C, L, R2>>, EqMismatch>
    where
        (): InterEq<R, L2>,
        (): InterEq<C, C>,
    {
        if self.id != other.id {
            return Err(EqMismatch);
        }
        Ok(Theorem {
            stmt: self.stmt.trans(other.stmt)?,
            id: self.id,
        })
    }

    /// Borrow this equation-in-context
    pub fn eq_as_ref<'a>(&'a self) -> Theorem<EqnIn<C, &'a L, &'a R>>
    where
        C: Copy,
    {
        Theorem {
            stmt: self.stmt.as_ref(),
            id: self.id,
        }
    }
}
