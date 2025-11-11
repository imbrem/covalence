use crate::{
    fact::{Holds, IntoPred1, Is, Pred0, Rw, Seq},
    store::{Ctx, LocalTerm},
};

/// Stable facts are sealed
pub(crate) mod stable_facts_sealed {
    pub trait FactSealed<D> {}

    pub trait FormulaSealed<C, D> {}
}

use either::Either;
pub(crate) use stable_facts_sealed::{FormulaSealed, FactSealed};

/// A stable fact is one which will stay true as the kernel evolves
pub trait StableFact<D>: FactSealed<D> {}

/// A formula is stable if it remains true as its context weakens
pub trait StableFormula<C, D>: FormulaSealed<C, D> {}

impl<D> StableFact<D> for () {}

impl<D, C: Ctx<D>> StableFormula<C, D> for () {}

impl<D> StableFact<D> for bool {}

impl<D, C: Ctx<D>> StableFormula<C, D> for bool {}

impl<D, A: StableFact<D>, B: StableFact<D>> StableFact<D> for (A, B) {}

impl<D, C: Ctx<D>, A: StableFormula<C, D>, B: StableFormula<C, D>> StableFormula<C, D> for (A, B) {}

impl<D, A: StableFact<D>, B: StableFact<D>> StableFact<D> for Either<A, B> {}

impl<D, C: Ctx<D>, A: StableFormula<C, D>, B: StableFormula<C, D>> StableFormula<C, D>
    for Either<A, B>
{
}

impl<D, C: Ctx<D>, F: StableFormula<C, D>> StableFact<D> for Seq<C, F> {}

impl<D, C: Ctx<D>> StableFormula<C, D> for Pred0 {}

impl<D, C: Ctx<D>, T: LocalTerm<C, D>> StableFormula<C, D> for Holds<T> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> StableFormula<C, D> for Rw<L, R> {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> StableFormula<C, D> for Is<P, T> {}

impl<D> FactSealed<D> for () {}

impl<D, C: Ctx<D>> FormulaSealed<C, D> for () {}

impl<D> FactSealed<D> for bool {}

impl<D, C: Ctx<D>> FormulaSealed<C, D> for bool {}

impl<D, A: FactSealed<D>, B: FactSealed<D>> FactSealed<D> for (A, B) {}

impl<D, C: Ctx<D>, A: FormulaSealed<C, D>, B: FormulaSealed<C, D>> FormulaSealed<C, D> for (A, B) {}

impl<D, A: FactSealed<D>, B: FactSealed<D>> FactSealed<D> for Either<A, B> {}

impl<D, C: Ctx<D>, A: FormulaSealed<C, D>, B: FormulaSealed<C, D>> FormulaSealed<C, D>
    for Either<A, B>
{
}

impl<D, C: Ctx<D>, F: FormulaSealed<C, D>> FactSealed<D> for Seq<C, F> {}

impl<D, C: Ctx<D>> FormulaSealed<C, D> for Pred0 {}

impl<D, C: Ctx<D>, T: LocalTerm<C, D>> FormulaSealed<C, D> for Holds<T> {}

impl<D, C: Ctx<D>, L: LocalTerm<C, D>, R: LocalTerm<C, D>> FormulaSealed<C, D> for Rw<L, R> {}

impl<D, P: IntoPred1, C: Ctx<D>, T: LocalTerm<C, D>> FormulaSealed<C, D> for Is<P, T> {}
