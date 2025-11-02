pub use covalence_kernel::*;

use data::term::*;

/// An extension trait providing a more convenient interface for the `covalence` kernel
pub trait DeriveExt<C, T>: Derive<C, T> + ReadTermDb<C, T> + WriteTerm<C, T>
where
    C: Copy + PartialEq,
    T: Copy + PartialEq,
{
    /// Construct the universe of propositions in a given context
    fn prop(&mut self, ctx: C) -> Val<C, T> {
        Val {
            ctx,
            tm: self.add(ctx, NodeT::U(ULvl::PROP)),
        }
    }

    /// Construct the true proposition in a given context
    fn tt(&mut self, ctx: C) -> Val<C, T> {
        Val {
            ctx,
            tm: self.add(ctx, NodeT::Unit),
        }
    }

    /// Construct the false proposition in a given context
    fn ff(&mut self, ctx: C) -> Val<C, T> {
        Val {
            ctx,
            tm: self.add(ctx, NodeT::Empty),
        }
    }
}

impl<C, T, K> DeriveExt<C, T> for K
where
    C: Copy + PartialEq,
    T: Copy + PartialEq,
    K: Derive<C, T> + ReadTermDb<C, T> + WriteTerm<C, T>,
{
}
