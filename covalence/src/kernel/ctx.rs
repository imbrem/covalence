use covalence_kernel::store::*;

pub trait KernelCtxExt: TermStore {
    fn with_parent(&mut self, ctx: CtxId<Self::Store>) -> CtxId<Self::Store>;
}

impl<D> KernelCtxExt for covalence_kernel::Kernel<D>
where
    D: TermIndex + LocalStoreUnchecked<Store = D>,
{
    fn with_parent(&mut self, ctx: CtxId<D>) -> CtxId<D> {
        let result = self.new_ctx();
        self.add_parent(result, ctx)
            .expect("it is always valid to add a parent to a new context");
        result
    }
}
