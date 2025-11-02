use covalence_kernel::api::strategy::Strategy;
pub use covalence_kernel::*;

use data::term::*;

/// An extension trait providing a more convenient interface for the `covalence` kernel
pub trait DeriveExt<C, T>: Derive<C, T> + ReadTermDb<C, T> + WriteTerm<C, T>
where
    C: Copy + PartialEq,
    T: Copy + PartialEq,
{
    /// Insert a new context with the given parameter
    ///
    /// TODO: reference Lean
    fn with_param<S>(
        &mut self,
        parent: C,
        param: Val<C, T>,
        strategy: &mut S,
    ) -> Result<Fv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        todo!()
        // //TODO: indicate to strategy we're calling with_param?
        // let ctx = self.with_parent(parent);
        // let ty = self.import(
        //     ctx,
        //     Val {
        //         ctx: parent,
        //         tm: param,
        //     },
        // );
        // let var = self.add_var(ctx, ty, strategy)?;
        // Ok(var)
    }

    //TODO: derive these to be fully well-typed, every time?

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

    /// Construct the universe of sets in a given context
    fn sets(&mut self, ctx: C) -> Val<C, T> {
        Val {
            ctx,
            tm: self.add(ctx, NodeT::U(ULvl::SET)),
        }
    }

    /// Construct the type of natural numbers in a given context
    fn nats(&mut self, ctx: C) -> Val<C, T> {
        Val {
            ctx,
            tm: self.add(ctx, NodeT::Nats),
        }
    }

    /// Construct a small natural number in a given context
    fn n64(&mut self, ctx: C, n: u64) -> Val<C, T> {
        Val {
            ctx,
            tm: self.add(ctx, NodeT::N64(n)),
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
