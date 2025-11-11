use crate::{
    formula::{IntoPred1, Is, Pred0, Rw},
    store::{Ctx, LocalTerm},
};

/// Stable formulas are sealed
pub(crate) mod stable_formula_sealed {
    pub trait FormulaSealed<C, D> {}
}

use either::Either;
pub(crate) use stable_formula_sealed::FormulaSealed;

/// A formula is stable if it remains true as its context weakens
pub trait StableFormula<C, D>: FormulaSealed<C, D> {}

impl<D, C: Ctx<D>> StableFormula<C, D> for () {}

impl<D, C: Ctx<D>> StableFormula<C, D> for bool {}

impl<D, C: Ctx<D>, A: StableFormula<C, D>, B: StableFormula<C, D>> StableFormula<C, D> for (A, B) {}

impl<D, C: Ctx<D>, A: StableFormula<C, D>, B: StableFormula<C, D>> StableFormula<C, D>
    for Either<A, B>
{
}

impl<D, C: Ctx<D>> StableFormula<C, D> for Pred0 {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> StableFormula<C, D> for Is<P, T> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFormula<C, D> for Rw<L, R> {}

impl<D, C: Ctx<D>> FormulaSealed<C, D> for () {}

impl<D, C: Ctx<D>> FormulaSealed<C, D> for bool {}

impl<D, C: Ctx<D>, A: FormulaSealed<C, D>, B: FormulaSealed<C, D>> FormulaSealed<C, D> for (A, B) {}

impl<D, C: Ctx<D>, A: FormulaSealed<C, D>, B: FormulaSealed<C, D>> FormulaSealed<C, D>
    for Either<A, B>
{
}

impl<D, C: Ctx<D>> FormulaSealed<C, D> for Pred0 {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> FormulaSealed<C, D> for Rw<L, R> {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> FormulaSealed<C, D> for Is<P, T> {}
