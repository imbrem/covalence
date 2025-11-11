use std::marker::PhantomData;

use crate::{
    Theorem,
    data::term::{Abs, HasTy, Pi, Sigma},
    fact::{
        HasTyIn, HasTyP, Is, IsTy, IsWf, IsWfIn, Seq, Ty, Wf,
        quant::{Forall, Quantified},
    },
    store::{Ctx, LocalTerm},
};

impl<C, T> Seq<C, Quantified<Forall<T>, IsWf<T>>> {
    pub fn abs_wf(self) -> Seq<C, IsWf<Abs<T>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Wf, Abs::new(self.stmt.binder.0, self.stmt.body.1)),
        }
    }
}

impl<C, T, D> Theorem<Seq<C, Quantified<Forall<T>, IsWf<T>>>, D>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    pub fn abs_wf(self) -> Theorem<Seq<C, IsWf<Abs<T>>>, D> {
        Theorem {
            stmt: self.stmt.abs_wf(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<C, T> Seq<C, Quantified<Forall<T>, IsTy<T>>> {
    pub fn pi_ty(self) -> Seq<C, IsTy<Pi<T>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Ty, Pi::new(self.stmt.binder.0, self.stmt.body.1)),
        }
    }

    pub fn sigma_ty(self) -> Seq<C, IsTy<Sigma<T>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Ty, Sigma::new(self.stmt.binder.0, self.stmt.body.1)),
        }
    }
}

impl<C, T, D> Theorem<Seq<C, Quantified<Forall<T>, IsTy<T>>>, D>
where
    C: Ctx<D>,
    T: LocalTerm<C, D>,
{
    pub fn pi_ty(self) -> Theorem<Seq<C, IsTy<Pi<T>>>, D> {
        Theorem {
            stmt: self.stmt.pi_ty(),
            id: self.id,
            store: PhantomData,
        }
    }

    pub fn sigma_ty(self) -> Theorem<Seq<C, IsTy<Sigma<T>>>, D> {
        Theorem {
            stmt: self.stmt.sigma_ty(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<C, L, R, RTy> Seq<C, Quantified<Forall<L>, HasTyP<R, RTy>>> {
    pub fn abs_has_ty(self) -> HasTyIn<C, Abs<L, R>, Pi<L, RTy>>
    where
        L: Clone,
    {
        HasTyIn::new(
            self.ctx,
            Abs::new(self.stmt.binder.0.clone(), self.stmt.body.1.1),
            Pi::new(self.stmt.binder.0, self.stmt.body.1.2),
        )
    }

    pub fn abs_has_ty_wf(self) -> IsWfIn<C, Abs<L, HasTy<R, RTy>>> {
        Seq {
            ctx: self.ctx,
            stmt: Is(Wf, Abs::new(self.stmt.binder.0, self.stmt.body.1)),
        }
    }
}

// impl<C, L, R, RTy, D> Theorem<Seq<C, Quantified<Forall<L>, HasTyP<R, RTy>>>, D>
// where
//     C: Ctx<D>,
//     L: LocalTerm<C, D>,
//     R: LocalTerm<C, D>,
//     RTy: LocalTerm<C, D>,
// {
//     pub fn abs_has_ty(self) -> Theorem<HasTyIn<C, Abs<L, R>, Pi<L, RTy>>, D>
//     where
//         L: Clone,
//     {
//         Theorem {
//             stmt: self.stmt.abs_has_ty(),
//             id: self.id,
//             store: PhantomData,
//         }
//     }

//     pub fn abs_has_ty_wf(self) -> Theorem<IsWfIn<C, Abs<L, HasTy<R, RTy>>>, D> {
//         Theorem {
//             stmt: self.stmt.abs_has_ty_wf(),
//             id: self.id,
//             store: PhantomData,
//         }
//     }
// }
