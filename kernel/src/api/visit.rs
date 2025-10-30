use std::ops::ControlFlow;

use crate::data::term::*;

pub trait Visitor<C, T> {
    type Output;
    type Error;

    /// Inspect a term
    fn inspect(&mut self, val: Val<C, T>) -> ControlFlow<Result<Self::Output, Self::Error>>;

    /// Flatten a nested result for a given term
    fn flatten(
        &mut self,
        val: Val<C, T>,
        result: NodeT<C, Self::Output>,
    ) -> Result<Self::Output, Self::Error>;

    /// Push a binder, inspecting a term under this binder
    fn inspect_under(
        &mut self,
        _binder: Option<Val<C, T>>,
        val: Val<C, T>,
    ) -> ControlFlow<Result<Self::Output, Self::Error>> {
        self.inspect(val)
    }

    /// Push a negated binder, inspecting a term under this binder
    fn inspect_under_not(
        &mut self,
        _pred: Val<C, T>,
        val: Val<C, T>,
    ) -> ControlFlow<Result<Self::Output, Self::Error>> {
        self.inspect_under(None, val)
    }

    /// Inspect a term under a binder of type ℕ
    fn inspect_under_nat(
        &mut self,
        val: Val<C, T>,
    ) -> ControlFlow<Result<Self::Output, Self::Error>> {
        self.inspect_under(None, val)
    }

    /// Finish inspecting a term, popping any binders
    ///
    /// Note that in general `pop` is _not_ called on `Continue`, only on `Break`!
    fn pop(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}
