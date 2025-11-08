use crate::{error::KernelError, fact::IsTyIn, *};

impl<D> Kernel<D>
where
    D: TermIndex + AddVarUnchecked<CtxId<D>, TmId<D>>,
{
    pub fn add_var(
        &mut self,
        ty: Theorem<IsTyIn<CtxId<D>, TmId<D>>>,
    ) -> Result<FvId<D>, KernelError> {
        self.theorem_belongs(&ty)?;
        let var = self.db.add_var_unchecked(ty.stmt.ctx, ty.stmt.0)?;
        Ok(var)
    }
}

impl<D> Kernel<D>
where
    D: TermIndex + AddParentUnchecked<CtxId<D>> + ReadCtxGraph<CtxId<D>>,
{
    pub fn add_parent(&mut self, ctx: CtxId<D>, parent: CtxId<D>) -> Result<(), KernelError> {
        if self.db.is_ancestor(ctx, parent) {
            return Err(KernelError::WouldCycle);
        }
        self.db.add_parent_unchecked(ctx, parent)?;
        Ok(())
    }
}
