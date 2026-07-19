//! Interpretation and functor action for the structural polynomial fragment.
//!
//! This module deliberately covers only `0`, `1`, parameters, the variable,
//! finite sums, and finite products. [`FunctorExpr::Compose`] remains useful
//! source syntax, but composition and nested-fixpoint realization require a
//! stronger interpretation and are rejected at this boundary.

use crate::polynomial::FunctorExpr;

/// A backend-neutral recipe for constructing `F(f)` from a structural
/// polynomial declaration.
///
/// Constants are retained so an interpreter can resolve their objects and
/// identity arrows. Only [`Variable`](Self::Variable) applies the input arrow.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StructuralMapPlan<P> {
    /// Map on the empty functor.
    Empty,
    /// Identity on the unit object.
    Unit,
    /// Identity on a declared constant parameter.
    Constant(P),
    /// Apply the input arrow.
    Variable,
    /// Map each summand and combine by coproduct.
    Sum(Vec<Self>),
    /// Map each factor and combine by product.
    Product(Vec<Self>),
}

/// Algebra used to interpret an automatically derived [`StructuralMapPlan`].
///
/// An implementation may return host functions, typed logic arrows, an IR, or
/// proof-script syntax. This is construction only; functor-law evidence remains
/// the separate [`StructuralFunctorLaws`] capability.
pub trait StructuralMapAlgebra<P> {
    /// The interpreter's result at each node.
    type Mapped;
    /// Interpretation failure.
    type Error;

    fn empty(&mut self) -> Result<Self::Mapped, Self::Error>;
    fn unit(&mut self) -> Result<Self::Mapped, Self::Error>;
    fn constant(&mut self, parameter: &P) -> Result<Self::Mapped, Self::Error>;
    fn variable(&mut self) -> Result<Self::Mapped, Self::Error>;
    fn sum(&mut self, terms: Vec<Self::Mapped>) -> Result<Self::Mapped, Self::Error>;
    fn product(&mut self, terms: Vec<Self::Mapped>) -> Result<Self::Mapped, Self::Error>;
}

impl<P> StructuralMapPlan<P> {
    /// Interpret this plan using a backend-selected map algebra.
    pub fn interpret<A: StructuralMapAlgebra<P>>(
        &self,
        algebra: &mut A,
    ) -> Result<A::Mapped, A::Error> {
        match self {
            Self::Empty => algebra.empty(),
            Self::Unit => algebra.unit(),
            Self::Constant(parameter) => algebra.constant(parameter),
            Self::Variable => algebra.variable(),
            Self::Sum(terms) => {
                let mapped = terms
                    .iter()
                    .map(|term| term.interpret(algebra))
                    .collect::<Result<Vec<_>, _>>()?;
                algebra.sum(mapped)
            }
            Self::Product(terms) => {
                let mapped = terms
                    .iter()
                    .map(|term| term.interpret(algebra))
                    .collect::<Result<Vec<_>, _>>()?;
                algebra.product(mapped)
            }
        }
    }
}

/// A checked expression in the structural polynomial fragment.
///
/// The private field prevents a backend from accidentally advertising support
/// for [`FunctorExpr::Compose`]. This is a capability check, not a semantic
/// positivity proof.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructuralPolynomial<P>(FunctorExpr<P>);

/// Why a [`FunctorExpr`] is outside the structural polynomial fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructuralPolynomialError {
    /// Explicit composition needs a stronger, separately advertised backend.
    CompositionUnsupported,
}

impl std::fmt::Display for StructuralPolynomialError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CompositionUnsupported => {
                f.write_str("explicit functor composition is not structural polynomial syntax")
            }
        }
    }
}

impl std::error::Error for StructuralPolynomialError {}

impl<P> StructuralPolynomial<P> {
    /// Borrow the checked structural expression.
    pub fn expression(&self) -> &FunctorExpr<P> {
        &self.0
    }

    /// Recover the underlying plain-data expression.
    pub fn into_expression(self) -> FunctorExpr<P> {
        self.0
    }

    /// Derive the canonical map-construction recipe from the declaration.
    pub fn derive_map_plan(&self) -> StructuralMapPlan<P>
    where
        P: Clone,
    {
        fn derive<P: Clone>(expression: &FunctorExpr<P>) -> StructuralMapPlan<P> {
            match expression {
                FunctorExpr::Zero => StructuralMapPlan::Empty,
                FunctorExpr::One => StructuralMapPlan::Unit,
                FunctorExpr::Param(parameter) => StructuralMapPlan::Constant(parameter.clone()),
                FunctorExpr::Var => StructuralMapPlan::Variable,
                FunctorExpr::Sum(terms) => {
                    StructuralMapPlan::Sum(terms.iter().map(derive).collect())
                }
                FunctorExpr::Product(terms) => {
                    StructuralMapPlan::Product(terms.iter().map(derive).collect())
                }
                FunctorExpr::Compose { .. } => {
                    unreachable!("StructuralPolynomial excludes composition")
                }
            }
        }

        derive(&self.0)
    }
}

/// Normalize explicit composition, check the structural fragment, and derive a
/// map plan. This is the opt-in composition pipeline; callers which require
/// source-preserving composition should use a stronger capability instead.
pub fn derive_composed_map_plan<P: Clone>(
    expression: FunctorExpr<P>,
) -> Result<StructuralMapPlan<P>, StructuralPolynomialError> {
    let expanded = expression.expand_composition();
    Ok(StructuralPolynomial::try_from(expanded)?.derive_map_plan())
}

impl<P> TryFrom<FunctorExpr<P>> for StructuralPolynomial<P> {
    type Error = StructuralPolynomialError;

    fn try_from(expression: FunctorExpr<P>) -> Result<Self, Self::Error> {
        fn check<P>(expression: &FunctorExpr<P>) -> Result<(), StructuralPolynomialError> {
            match expression {
                FunctorExpr::Zero | FunctorExpr::One | FunctorExpr::Param(_) | FunctorExpr::Var => {
                    Ok(())
                }
                FunctorExpr::Sum(terms) | FunctorExpr::Product(terms) => {
                    terms.iter().try_for_each(check)
                }
                FunctorExpr::Compose { .. } => {
                    Err(StructuralPolynomialError::CompositionUnsupported)
                }
            }
        }

        check(&expression)?;
        Ok(Self(expression))
    }
}

/// Backend capability for interpreting and mapping structural polynomials.
///
/// `Object` and `Arrow` are intentionally abstract. In HOL they may be type and
/// term handles; in a reference model they may be ordinary sets and functions.
/// Parameter tokens are interpreted by the backend, so this trait does not
/// prescribe a universe or add anything to the trusted kernel.
pub trait StructuralFunctorAction<P> {
    /// Objects in the backend's ambient category.
    type Object;
    /// Arrows between objects. Implementations must reject ill-typed arrows.
    type Arrow;
    /// Interpretation or typing failure.
    type Error;

    /// Interpret `F(X)` at `variable = X`.
    fn interpret(
        &self,
        functor: &StructuralPolynomial<P>,
        variable: &Self::Object,
    ) -> Result<Self::Object, Self::Error>;

    /// Lift `arrow : X → Y` to `F(arrow) : F(X) → F(Y)`.
    fn map(
        &self,
        functor: &StructuralPolynomial<P>,
        source: &Self::Object,
        target: &Self::Object,
        arrow: &Self::Arrow,
    ) -> Result<Self::Arrow, Self::Error>;
}

/// Explicit proof/evidence seams for the functor laws.
///
/// Implementing [`StructuralFunctorAction`] supplies operations only.
/// Implementing this trait additionally supplies backend-native evidence that
/// those operations preserve identity, composition, and equal arrows. The
/// evidence remains opaque: this API neither constructs nor admits facts.
pub trait StructuralFunctorLaws<P>: StructuralFunctorAction<P> {
    /// Backend-native evidence (for example an unforgeable theorem handle).
    type Evidence;

    /// Evidence for `F(id_X) = id_(F(X))`.
    fn map_identity(
        &self,
        functor: &StructuralPolynomial<P>,
        object: &Self::Object,
    ) -> Result<Self::Evidence, Self::Error>;

    /// Evidence for `F(g ∘ f) = F(g) ∘ F(f)`.
    fn map_composition(
        &self,
        functor: &StructuralPolynomial<P>,
        source: &Self::Object,
        middle: &Self::Object,
        target: &Self::Object,
        first: &Self::Arrow,
        second: &Self::Arrow,
    ) -> Result<Self::Evidence, Self::Error>;

    /// Transport equality of arrows: evidence for `f = g` yields evidence for
    /// `F(f) = F(g)`.
    fn map_congruence(
        &self,
        functor: &StructuralPolynomial<P>,
        source: &Self::Object,
        target: &Self::Object,
        left: &Self::Arrow,
        right: &Self::Arrow,
        equal: &Self::Evidence,
    ) -> Result<Self::Evidence, Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Symbolic;

    impl StructuralFunctorAction<&'static str> for Symbolic {
        type Object = String;
        type Arrow = String;
        type Error = std::convert::Infallible;

        fn interpret(
            &self,
            functor: &StructuralPolynomial<&'static str>,
            variable: &Self::Object,
        ) -> Result<Self::Object, Self::Error> {
            fn go(expression: &FunctorExpr<&str>, variable: &str) -> String {
                match expression {
                    FunctorExpr::Zero => "0".into(),
                    FunctorExpr::One => "1".into(),
                    FunctorExpr::Param(parameter) => format!("P[{parameter}]"),
                    FunctorExpr::Var => variable.into(),
                    FunctorExpr::Sum(terms) => format!(
                        "({})",
                        terms
                            .iter()
                            .map(|term| go(term, variable))
                            .collect::<Vec<_>>()
                            .join(" + ")
                    ),
                    FunctorExpr::Product(terms) => format!(
                        "({})",
                        terms
                            .iter()
                            .map(|term| go(term, variable))
                            .collect::<Vec<_>>()
                            .join(" × ")
                    ),
                    FunctorExpr::Compose { .. } => {
                        unreachable!("StructuralPolynomial excludes composition")
                    }
                }
            }
            Ok(go(functor.expression(), variable))
        }

        fn map(
            &self,
            functor: &StructuralPolynomial<&'static str>,
            source: &Self::Object,
            target: &Self::Object,
            arrow: &Self::Arrow,
        ) -> Result<Self::Arrow, Self::Error> {
            Ok(format!(
                "map[{}]({arrow} : {source} -> {target})",
                self.interpret(functor, &"X".into())?
            ))
        }
    }

    impl StructuralFunctorLaws<&'static str> for Symbolic {
        type Evidence = String;

        fn map_identity(
            &self,
            functor: &StructuralPolynomial<&'static str>,
            object: &Self::Object,
        ) -> Result<Self::Evidence, Self::Error> {
            Ok(format!("map-id[{}]", self.interpret(functor, object)?))
        }

        fn map_composition(
            &self,
            functor: &StructuralPolynomial<&'static str>,
            source: &Self::Object,
            middle: &Self::Object,
            target: &Self::Object,
            first: &Self::Arrow,
            second: &Self::Arrow,
        ) -> Result<Self::Evidence, Self::Error> {
            Ok(format!(
                "map-compose[{}]({first}, {second}; {source}, {middle}, {target})",
                self.interpret(functor, source)?
            ))
        }

        fn map_congruence(
            &self,
            functor: &StructuralPolynomial<&'static str>,
            source: &Self::Object,
            target: &Self::Object,
            left: &Self::Arrow,
            right: &Self::Arrow,
            equal: &Self::Evidence,
        ) -> Result<Self::Evidence, Self::Error> {
            Ok(format!(
                "map-cong[{}]({left}, {right}; {source}, {target}; {equal})",
                self.interpret(functor, source)?
            ))
        }
    }

    fn example() -> StructuralPolynomial<&'static str> {
        FunctorExpr::Sum(vec![
            FunctorExpr::One,
            FunctorExpr::Product(vec![FunctorExpr::Param("label"), FunctorExpr::Var]),
            FunctorExpr::Zero,
        ])
        .try_into()
        .unwrap()
    }

    #[test]
    fn structural_interpretation_and_map_cover_the_core_grammar() {
        let backend = Symbolic;
        let functor = example();
        assert_eq!(
            backend.interpret(&functor, &"A".into()).unwrap(),
            "(1 + (P[label] × A) + 0)"
        );
        assert!(
            backend
                .map(&functor, &"A".into(), &"B".into(), &"f".into())
                .unwrap()
                .contains("f : A -> B")
        );
    }

    #[test]
    fn law_capability_is_separate_and_explicit() {
        let backend = Symbolic;
        let functor = example();
        assert_eq!(
            backend.map_identity(&functor, &"A".into()).unwrap(),
            "map-id[(1 + (P[label] × A) + 0)]"
        );
        assert!(
            backend
                .map_composition(
                    &functor,
                    &"A".into(),
                    &"B".into(),
                    &"C".into(),
                    &"f".into(),
                    &"g".into()
                )
                .unwrap()
                .starts_with("map-compose")
        );
        assert!(
            backend
                .map_congruence(
                    &functor,
                    &"A".into(),
                    &"B".into(),
                    &"f".into(),
                    &"g".into(),
                    &"f=g".into()
                )
                .unwrap()
                .starts_with("map-cong")
        );
    }

    #[test]
    fn explicit_composition_requires_a_stronger_capability() {
        let composed = FunctorExpr::compose(FunctorExpr::Var, FunctorExpr::Param("nested"));
        assert_eq!(
            StructuralPolynomial::try_from(composed),
            Err(StructuralPolynomialError::CompositionUnsupported)
        );
    }

    #[derive(Default)]
    struct PlanPrinter;

    impl StructuralMapAlgebra<&'static str> for PlanPrinter {
        type Mapped = String;
        type Error = std::convert::Infallible;

        fn empty(&mut self) -> Result<String, Self::Error> {
            Ok("absurd".into())
        }
        fn unit(&mut self) -> Result<String, Self::Error> {
            Ok("id(1)".into())
        }
        fn constant(&mut self, parameter: &&'static str) -> Result<String, Self::Error> {
            Ok(format!("id({parameter})"))
        }
        fn variable(&mut self) -> Result<String, Self::Error> {
            Ok("f".into())
        }
        fn sum(&mut self, terms: Vec<String>) -> Result<String, Self::Error> {
            Ok(format!("sum({})", terms.join(",")))
        }
        fn product(&mut self, terms: Vec<String>) -> Result<String, Self::Error> {
            Ok(format!("product({})", terms.join(",")))
        }
    }

    #[test]
    fn map_plan_is_derived_and_interpretable() {
        let plan = example().derive_map_plan();
        assert_eq!(
            plan.interpret(&mut PlanPrinter).unwrap(),
            "sum(id(1),product(id(label),f),absurd)"
        );
    }

    #[test]
    fn composition_can_be_normalized_before_plan_derivation() {
        let maybe = FunctorExpr::Sum(vec![FunctorExpr::One, FunctorExpr::Var]);
        let pair = FunctorExpr::Product(vec![FunctorExpr::Param("tag"), FunctorExpr::Var]);
        let plan = derive_composed_map_plan(FunctorExpr::compose(maybe, pair)).unwrap();
        assert_eq!(
            plan.interpret(&mut PlanPrinter).unwrap(),
            "sum(id(1),product(id(tag),f))"
        );
    }
}
