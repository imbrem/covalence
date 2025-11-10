use crate::{
    error::KernelError,
    fact::{
        CheckFact, HasTy, HasTyIn, IsTyIn,
        logic::Iff,
        stable::{FactSealed, StableFact},
    },
    *,
};

/// The fact that a variable has a given type within a context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct VarTy<C, T> {
    pub var: Fv<C>,
    pub ty: T,
}

impl<D, C, T> Iff<HasTyIn<C, Fv<C>, T>, D> for VarTy<C, T>
where
    C: Copy + Ctx<D>,
    T: LocalTerm<C, D>,
{
    fn iff(self) -> HasTyIn<C, Fv<C>, T> {
        HasTyIn {
            ctx: self.var.ctx,
            stmt: HasTy {
                tm: self.var,
                ty: self.ty,
            },
        }
    }
}

impl<D, C, T, I> Iff<HasTyIn<C, Node<C, T, I>, T>, D> for VarTy<C, T>
where
    C: Copy + Ctx<D>,
    T: LocalTerm<C, D>,
    I: LocalTerm<C, D>,
{
    fn iff(self) -> HasTyIn<C, Node<C, T, I>, T> {
        HasTyIn {
            ctx: self.var.ctx,
            stmt: HasTy {
                tm: Node::Fv(self.var),
                ty: self.ty,
            },
        }
    }
}

impl<D, C: Ctx<D>, T: Term<D>> FactSealed<D> for VarTy<C, T> {}

impl<D, C: Ctx<D>, T: Term<D>> StableFact<D> for VarTy<C, T> {}

impl<D> CheckFact<VarTy<CtxId<D>, TmId<D>>> for D
where
    D: TermIndex + ReadCtx<CtxId<D>, VarId = TmId<D>>,
{
    fn check(&self, fact: &VarTy<CtxId<D>, TmId<D>>) -> bool {
        fact.var.ix < self.num_vars(fact.var.ctx) && self.var_ty(fact.var) == fact.ty
    }
}

impl<D> Kernel<D>
where
    D: TermIndex + AddVarUnchecked<CtxId<D>, TmId<D>>,
{
    pub fn add_var(
        &mut self,
        ty: Theorem<IsTyIn<CtxId<D>, TmId<D>>, D>,
    ) -> Result<Theorem<VarTy<CtxId<D>, TmId<D>>, D>, KernelError> {
        self.thm_belongs(&ty)?;
        let var = self.db.add_var_unchecked(ty.stmt.ctx, ty.stmt.1)?;
        Ok(self.new_thm(VarTy { var, ty: ty.1 }))
    }
}

impl<D> Kernel<D>
where
    D: TermIndex + ReadCtx<CtxId<D>, VarId = TmId<D>>,
{
    pub fn get_var(
        &self,
        var: Fv<CtxId<D>>,
    ) -> Result<Theorem<VarTy<CtxId<D>, TmId<D>>, D>, KernelError> {
        if self.db.num_vars(var.ctx) <= var.ix {
            return Err(KernelError::VarNotFound);
        }
        let ty = self.db.var_ty(var);
        Ok(self.new_thm(VarTy { var, ty }))
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
