use covalence_kernel::store::*;

pub trait KernelCtxExt: TermIndex {
    fn with_parent(&mut self, ctx: CtxId<Self>) -> CtxId<Self>;
}

impl<D> KernelCtxExt for covalence_kernel::Kernel<D>
where
    D: LocalStoreUnchecked,
{
    fn with_parent(&mut self, ctx: CtxId<Self>) -> CtxId<Self> {
        let result = self.new_ctx();
        self.add_parent(result, ctx)
            .expect("it is always valid to add a parent to a new context");
        result
    }
}
