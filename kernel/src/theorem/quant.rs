use crate::{
    Theorem,
    data::term::Fv,
    error::KernelError,
    fact::{
        HasTyIn, IsTyIn, Seq,
        quant::{CloseChildren, Quantified},
        stable::StableFact,
    },
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
