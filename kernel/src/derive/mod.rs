pub mod trusted;

pub use trusted::*;

use crate::term::Gv;

pub trait DeriveExt<C: Copy + PartialEq, T: Copy + PartialEq>:
    Derive<C, T> + TermStore<C, T> + ReadFacts<C, T>
{
    /// Insert a new context with the given parameter
    fn with_param<S>(&mut self, parent: C, param: T, strategy: &mut S) -> Result<Gv<C>, S::Fail>
    where
        S: Strategy<C, T, Self>,
    {
        //TODO: indicate to strategy we're calling with_param?
        let ctx = self.with_parent(parent);
        let ty = self.import(ctx, parent, param);
        let assume = self.assume(ctx, ty, parent, strategy)?;
        debug_assert!(
            assume.0 == ty,
            "assume returns the fact that ty is inhabited in ctx"
        );
        debug_assert!(self.is_inhab(ctx, ty), "ty is inhabited in ctx");
        let var = self
            .add_var(ctx, param, &mut ())
            .expect("we can always safely add a variable of inhabited type");
        Ok(var)
    }
}

impl<C: Copy + PartialEq, T: Copy + PartialEq, K: Derive<C, T> + TermStore<C, T> + ReadFacts<C, T>>
    DeriveExt<C, T> for K
{
}
