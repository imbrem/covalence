use crate::{
    error::KernelError,
    fact::{
        CheckFact, HasTy, HasTyIn, IsTyIn,
        implies::{FromIff, FromIffSealed},
        stable::{StableFact, StableFactSealed},
    },
    *,
};

/// The fact that a variable has a given type within a context
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct VarTy<C, T> {
    pub var: Fv<C>,
    pub ty: T,
}

impl<C, T> FromIffSealed<VarTy<C, T>> for HasTyIn<C, Fv<C>, T> where C: Copy {}

impl<C, T> FromIff<VarTy<C, T>> for HasTyIn<C, Fv<C>, T>
where
    C: Copy,
{
    fn from_iff(value: VarTy<C, T>) -> Self {
        HasTyIn {
            ctx: value.var.ctx,
            stmt: HasTy {
                tm: value.var,
                ty: value.ty,
            },
        }
    }
}

impl<C, T> FromIffSealed<VarTy<C, T>> for HasTyIn<C, Node<C, T>, T> where C: Copy {}

impl<C, T> FromIff<VarTy<C, T>> for HasTyIn<C, Node<C, T>, T>
where
    C: Copy,
{
    fn from_iff(value: VarTy<C, T>) -> Self {
        HasTyIn {
            ctx: value.var.ctx,
            stmt: HasTy {
                tm: Node::Fv(value.var),
                ty: value.ty,
            },
        }
    }
}

impl<C, T> StableFactSealed for VarTy<C, T> {}

impl<C, T> StableFact for VarTy<C, T> {}

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
        ty: Theorem<IsTyIn<CtxId<D>, TmId<D>>>,
    ) -> Result<Theorem<VarTy<CtxId<D>, TmId<D>>>, KernelError> {
        self.theorem_belongs(&ty)?;
        let var = self.db.add_var_unchecked(ty.stmt.ctx, ty.stmt.0)?;
        Ok(self.new_thm(VarTy { var, ty: ty.0 }))
    }
}

impl<D> Kernel<D>
where
    D: TermIndex + ReadCtx<CtxId<D>, VarId = TmId<D>>,
{
    pub fn get_var(
        &self,
        var: Fv<CtxId<D>>,
    ) -> Result<Theorem<VarTy<CtxId<D>, TmId<D>>>, KernelError> {
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
