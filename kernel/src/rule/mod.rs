use std::marker::PhantomData;

use crate::{
    Theorem,
    data::term::{Abs, HasTy, Pi, Sigma},
    fact::{HasTyIn, IsWfIn, Seq},
    formula::{
        HasTyP, Is, IsTy, IsWf, Ty, Wf,
        quant::{Forall, Quantified},
    },
    store::{Ctx, LocalTerm},
};

impl<C, T> Seq<C, Quantified<Forall<T>, IsWf<T>>> {
    pub fn abs_wf(self) -> Seq<C, IsWf<Abs<T>>> {
        Seq {
            ctx: self.ctx,
            form: Is(Wf, Abs::new(self.form.binder.0, self.form.body.1)),
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
            fact: self.fact.abs_wf(),
            id: self.id,
            store: PhantomData,
        }
    }
}

impl<C, T> Seq<C, Quantified<Forall<T>, IsTy<T>>> {
    pub fn pi_ty(self) -> Seq<C, IsTy<Pi<T>>> {
        Seq {
            ctx: self.ctx,
            form: Is(Ty, Pi::new(self.form.binder.0, self.form.body.1)),
        }
    }

    pub fn sigma_ty(self) -> Seq<C, IsTy<Sigma<T>>> {
        Seq {
            ctx: self.ctx,
            form: Is(Ty, Sigma::new(self.form.binder.0, self.form.body.1)),
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
            fact: self.fact.pi_ty(),
            id: self.id,
            store: PhantomData,
        }
    }

    pub fn sigma_ty(self) -> Theorem<Seq<C, IsTy<Sigma<T>>>, D> {
        Theorem {
            fact: self.fact.sigma_ty(),
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
            Abs::new(self.form.binder.0.clone(), self.form.body.1.1),
            Pi::new(self.form.binder.0, self.form.body.1.2),
        )
    }

    pub fn abs_has_ty_wf(self) -> IsWfIn<C, Abs<L, HasTy<R, RTy>>> {
        Seq {
            ctx: self.ctx,
            form: Is(Wf, Abs::new(self.form.binder.0, self.form.body.1)),
        }
    }
}

impl<C, L, R, RTy, D> Theorem<Seq<C, Quantified<Forall<L>, HasTyP<R, RTy>>>, D>
where
    C: Ctx<D>,
    L: LocalTerm<C, D>,
    R: LocalTerm<C, D>,
    RTy: LocalTerm<C, D>,
{
    pub fn abs_has_ty(self) -> Theorem<HasTyIn<C, Abs<L, R>, Pi<L, RTy>>, D>
    where
        L: Clone,
    {
        Theorem {
            fact: self.fact.abs_has_ty(),
            id: self.id,
            store: PhantomData,
        }
    }

    pub fn abs_has_ty_wf(self) -> Theorem<IsWfIn<C, Abs<L, HasTy<R, RTy>>>, D> {
        Theorem {
            fact: self.fact.abs_has_ty_wf(),
            id: self.id,
            store: PhantomData,
        }
    }
}
