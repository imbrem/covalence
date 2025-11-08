use crate::{fact::IsTyIn, theorem::IdMismatch, *};

impl<D> Kernel<D>
where
    D: TermIndex + AddVarUnchecked<CtxId<D>, TmId<D>>,
{
    pub fn add_var(
        &mut self,
        ty: Theorem<IsTyIn<CtxId<D>, TmId<D>>>,
    ) -> Result<FvId<D>, IdMismatch> {
        self.theorem_belongs(&ty)?;
        //TODO: check for a sealed context, etc...
        Ok(self.db.add_var_unchecked(ty.stmt.ctx, ty.stmt.0))
    }
}
