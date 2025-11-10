use std::marker::PhantomData;

use crate::{
    Kernel, Theorem,
    ctx::VarTy,
    data::term::Fv,
    error::KernelError,
    fact::{
        HasTyIn, IsTyIn, Seq,
        quant::{CloseChildren, Forall, Quantified},
        stable::StableFact,
    },
    store::{Ctx, CtxId, LocalStoreUnchecked, ReadCtx, ReadCtxGraph},
};

impl<C, S, D> Theorem<Seq<C, S>, D> {
    pub fn wk0<T>(
        self,
        binder: Theorem<IsTyIn<C, T>, D>,
    ) -> Result<Theorem<Seq<C, Quantified<Forall<T>, S>>, D>, KernelError>
    where
        S: StableFact,
        C: PartialEq + Ctx<D>,
    {
        if self.id != binder.id {
            return Err(KernelError::IdMismatch);
        }
        self.stmt.wk0(binder.stmt).map(|stmt| Theorem {
            stmt,
            id: self.id,
            store: PhantomData,
        })
    }

    pub fn close_var_self<T>(
        self,
        var: Theorem<HasTyIn<C, Fv<C>, T>, D>,
    ) -> Result<Theorem<Seq<C, Quantified<Forall<T>, S::ClosedChildren>>, D>, KernelError>
    where
        S: CloseChildren<C>,
        C: PartialEq + Ctx<D>,
    {
        if self.id != var.id {
            return Err(KernelError::IdMismatch);
        }
        self.stmt.close_var_self(var.stmt).map(|stmt| Theorem {
            stmt,
            id: self.id,
            store: PhantomData,
        })
    }
}

impl<C, S> Seq<C, S> {
    pub fn wk0<T>(
        self,
        binder: IsTyIn<C, T>,
    ) -> Result<Seq<C, Quantified<Forall<T>, S>>, KernelError>
    where
        S: StableFact,
        C: PartialEq,
    {
        if self.ctx != binder.ctx {
            return Err(KernelError::CtxMismatch);
        }
        Ok(Seq {
            ctx: self.ctx,
            stmt: Quantified {
                binder: Forall(binder.stmt.1),
                body: self.stmt,
            },
        })
    }

    pub fn close_var_self<T>(
        self,
        var: HasTyIn<C, Fv<C>, T>,
    ) -> Result<Seq<C, Quantified<Forall<T>, S::ClosedChildren>>, KernelError>
    where
        S: CloseChildren<C>,
        C: PartialEq,
    {
        if self.ctx != var.ctx {
            return Err(KernelError::CtxMismatch);
        }
        Ok(Seq {
            ctx: self.ctx,
            stmt: Quantified {
                binder: Forall(var.stmt.ty),
                body: self.stmt.close_children(var.stmt.tm),
            },
        })
    }

    pub fn close_var_single<T, D>(
        self,
        var_ty: VarTy<C, T>,
        db: &D,
    ) -> Result<Seq<C, Quantified<Forall<T>, S::ClosedChildren>>, KernelError>
    where
        S: CloseChildren<C>,
        C: Copy + PartialEq,
        D: ReadCtxGraph<C> + ReadCtx<C>,
    {
        if !db.parents_are_subctx(var_ty.var.ctx, self.ctx) {
            return Err(KernelError::CtxMismatch);
        }
        if !db.num_assumptions(var_ty.var.ctx) != 1 {
            return Err(KernelError::SingleVarCtxExpected);
        }
        Ok(Seq {
            ctx: self.ctx,
            stmt: Quantified {
                binder: Forall(var_ty.ty),
                body: self.stmt.close_children(var_ty.var),
            },
        })
    }
}

impl<D> Kernel<D>
where
    D: LocalStoreUnchecked,
{
    pub fn close_var_single<S, T>(
        &self,
        seq: Theorem<Seq<CtxId<D>, S>, D>,
        var: Theorem<VarTy<CtxId<D>, T>, D>,
    ) -> Result<Theorem<Seq<CtxId<D>, Quantified<Forall<T>, S::ClosedChildren>>, D>, KernelError>
    where
        S: CloseChildren<CtxId<D>>,
    {
        if seq.id != self.id() || var.id != self.id() {
            return Err(KernelError::IdMismatch);
        }
        let ix = var.stmt.var.ix;
        let stmt = seq.stmt.close_var_single(var.stmt, &self.db)?;
        debug_assert_eq!(
            ix, 0,
            "the only valid variable index in a single variable context is 0"
        );
        Ok(Theorem {
            stmt,
            id: self.id(),
            store: PhantomData,
        })
    }
}
