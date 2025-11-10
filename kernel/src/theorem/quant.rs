use std::marker::PhantomData;

use crate::{
    Kernel, Theorem,
    ctx::VarTy,
    data::term::Fv,
    error::KernelError,
    fact::{
        HasTyIn, IsTyIn, Seq,
        quant::{CloseChildren, Forall, Quantified},
        stable::StableFactIn,
    },
    store::{Ctx, CtxId, LocalStoreUnchecked, ReadCtx, ReadCtxGraph},
};

impl<C, S, D> Theorem<Seq<C, S>, D> {
    pub fn wk0<T>(
        self,
        binder: Theorem<IsTyIn<C, T>, D>,
    ) -> Result<Theorem<Seq<C, Quantified<Forall<T>, S>>, D>, KernelError>
    where
        C: PartialEq + Ctx<D>,
        S: StableFactIn<C, D>,
    {
        self.compat(&binder)?;
        self.stmt.wk0(binder.stmt).map(|stmt| Theorem {
            stmt,
            id: self.id,
            store: PhantomData,
        })
    }

    pub fn close_var_self<T>(
        self,
        var: Theorem<HasTyIn<C, Fv<C>, T>, D>,
    ) -> Result<Theorem<Seq<C, Quantified<Forall<T>, S::Close1Children>>, D>, KernelError>
    where
        C: PartialEq + Ctx<D>,
        S: StableFactIn<C, D> + CloseChildren<C, D>,
    {
        self.compat(&var)?;
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

    pub fn close_var_self<T, D>(
        self,
        var: HasTyIn<C, Fv<C>, T>,
    ) -> Result<Seq<C, Quantified<Forall<T>, S::Close1Children>>, KernelError>
    where
        S: CloseChildren<C, D>,
        C: PartialEq,
    {
        if self.ctx != var.ctx {
            return Err(KernelError::CtxMismatch);
        }
        Ok(Seq {
            ctx: self.ctx,
            stmt: Quantified {
                binder: Forall(var.stmt.ty),
                body: self.stmt.close1_children(var.stmt.tm),
            },
        })
    }

    pub fn close_var_single<T, D>(
        self,
        var_ty: VarTy<C, T>,
        db: &D,
    ) -> Result<Seq<C, Quantified<Forall<T>, S::Close1Children>>, KernelError>
    where
        S: CloseChildren<C, D>,
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
                body: self.stmt.close1_children(var_ty.var),
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
    ) -> Result<Theorem<Seq<CtxId<D>, Quantified<Forall<T>, S::Close1Children>>, D>, KernelError>
    where
        S: StableFactIn<CtxId<D>, D> + CloseChildren<CtxId<D>, D>,
    {
        self.thm_belongs(&seq)?;
        self.thm_belongs(&var)?;
        let ix = var.stmt.var.ix;
        let stmt = seq.stmt.close_var_single(var.stmt, &self.db)?;
        debug_assert_eq!(
            ix, 0,
            "the only valid variable index in a single variable context is 0"
        );
        Ok(self.new_thm(stmt))
    }
}
