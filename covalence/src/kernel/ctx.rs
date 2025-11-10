use covalence_kernel::{Kernel, store::*};

pub trait KernelCtxExt: TermStore {
    fn with_parent(&mut self, ctx: CtxId<Self::Store>) -> CtxId<Self::Store>;
}

impl<D> KernelCtxExt for Kernel<D>
where
    D: LocalStoreUnchecked,
{
    fn with_parent(&mut self, ctx: CtxId<D>) -> CtxId<D> {
        let result = self.new_ctx();
        self.add_parent(result, ctx)
            .expect("it is always valid to add a parent to a new context");
        result
    }
}
