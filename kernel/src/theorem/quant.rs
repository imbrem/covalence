use crate::{
    Kernel, Theorem,
    ctx::VarTy,
    data::term::Fv,
    error::KernelError,
    fact::{
        HasTyIn, IsTyIn, Seq,
        quant::{CloseChildren, Quantified},
        stable::StableFact,
    },
    store::{CtxId, LocalStoreUnchecked, TmId},
};

impl<C, S> Theorem<Seq<C, S>> {
    pub fn wk0<T>(
        self,
        binder: Theorem<IsTyIn<C, T>>,
    ) -> Result<Theorem<Seq<C, Quantified<T, S>>>, KernelError>
    where
        S: StableFact,
        C: PartialEq,
    {
        if self.id != binder.id {
            return Err(KernelError::IdMismatch);
        }
        self.stmt
            .wk0(binder.stmt)
            .map(|stmt| Theorem { stmt, id: self.id })
    }

    pub fn close_var_self<T>(
        self,
        var: Theorem<HasTyIn<C, Fv<C>, T>>,
    ) -> Result<Theorem<Seq<C, Quantified<T, S::ClosedChildren>>>, KernelError>
    where
        S: CloseChildren<C>,
        C: PartialEq,
    {
        if self.id != var.id {
            return Err(KernelError::IdMismatch);
        }
        self.stmt
            .close_var_self(var.stmt)
            .map(|stmt| Theorem { stmt, id: self.id })
    }
}

impl<C, S> Seq<C, S> {
    pub fn wk0<T>(self, binder: IsTyIn<C, T>) -> Result<Seq<C, Quantified<T, S>>, KernelError>
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
                binder: binder.stmt.1,
                body: self.stmt,
            },
        })
    }

    pub fn close_var_self<T>(
        self,
        var: HasTyIn<C, Fv<C>, T>,
    ) -> Result<Seq<C, Quantified<T, S::ClosedChildren>>, KernelError>
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
                binder: var.stmt.ty,
                body: self.stmt.close_children(var.stmt.tm),
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
        seq: Theorem<Seq<CtxId<D>, S>>,
        var: Theorem<VarTy<CtxId<D>, T>>,
    ) -> Result<Theorem<Seq<CtxId<D>, Quantified<T, S::ClosedChildren>>>, KernelError>
    where
        S: CloseChildren<CtxId<D>>,
    {
        if seq.id != self.id() || var.id != self.id() {
            return Err(KernelError::IdMismatch);
        }
        let seq = seq.stmt;
        let var = var.stmt;
        if !self.parents_are_subctx(var.var.ctx, seq.ctx) {
            return Err(KernelError::CtxMismatch);
        }
        if self.num_assumptions(var.var.ctx) != 1 {
            return Err(KernelError::SingleVarCtxExpected);
        }
        debug_assert_eq!(
            var.var.ix, 0,
            "the only valid variable in a single-var ctx has index 0"
        );
        Ok(Theorem {
            stmt: Seq {
                ctx: seq.ctx,
                stmt: Quantified {
                    binder: var.ty,
                    body: seq.stmt.close_children(var.var),
                },
            },
            id: self.id(),
        })
    }
}
