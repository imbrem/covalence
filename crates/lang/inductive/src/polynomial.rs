//! Plain-data descriptions of records, variants, enums, and polynomial
//! functors.
//!
//! [`PolynomialSpec`] is the ergonomic named sum-of-products form. A field is
//! either a parameter supplied by the surrounding theory or the functor
//! variable. Thus a declaration denotes
//!
//! ```text
//! F(X) = Σ variant. Π field. (parameter | X)
//! ```
//!
//! Records, variants, and enums are the non-recursive aggregate views of the
//! same data. [`FunctorExpr`] is the smaller structural layer beneath that
//! syntax: it makes zero, one, sums, products, and functor composition
//! explicit. Fixpoint APIs continue to consume the named normal form, so
//! callers which care about constructor and field names do not pay for a more
//! general syntax.

use smol_str::SmolStr;

use crate::error::SpecError;
use crate::validated::Validated;

/// A structural polynomial-functor expression.
///
/// `Compose(outer, inner)` denotes substitution of `inner` for every
/// occurrence of [`Var`](Self::Var) in `outer`. Parameters remain constants.
/// Keeping this layer separate from [`PolynomialSpec`] makes the boundary
/// explicit: expressions describe functor algebra, while specifications retain
/// source-level constructor and field names.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FunctorExpr<P> {
    /// The empty functor.
    Zero,
    /// The unit functor.
    One,
    /// A constant parameter supplied by the surrounding theory.
    Param(P),
    /// The functor variable.
    Var,
    /// A finite coproduct.
    Sum(Vec<Self>),
    /// A finite product.
    Product(Vec<Self>),
    /// Functor composition: `outer ∘ inner`.
    Compose {
        /// The functor whose variable is substituted.
        outer: Box<Self>,
        /// The expression substituted for the outer variable.
        inner: Box<Self>,
    },
}

impl<P> FunctorExpr<P> {
    /// Construct an explicit functor composition.
    pub fn compose(outer: Self, inner: Self) -> Self {
        Self::Compose {
            outer: Box::new(outer),
            inner: Box::new(inner),
        }
    }

    /// Whether the expression depends on its functor variable.
    pub fn is_recursive(&self) -> bool {
        match self {
            Self::Zero | Self::One | Self::Param(_) => false,
            Self::Var => true,
            Self::Sum(terms) | Self::Product(terms) => terms.iter().any(Self::is_recursive),
            Self::Compose { outer, inner } => outer.is_recursive() && inner.is_recursive(),
        }
    }

    /// Map constant parameters without changing the functor structure.
    pub fn map_param<Q>(self, mut f: impl FnMut(P) -> Q) -> FunctorExpr<Q> {
        self.map_param_with(&mut f)
    }

    fn map_param_with<Q>(self, f: &mut impl FnMut(P) -> Q) -> FunctorExpr<Q> {
        match self {
            Self::Zero => FunctorExpr::Zero,
            Self::One => FunctorExpr::One,
            Self::Param(parameter) => FunctorExpr::Param(f(parameter)),
            Self::Var => FunctorExpr::Var,
            Self::Sum(terms) => FunctorExpr::Sum(
                terms
                    .into_iter()
                    .map(|term| term.map_param_with(f))
                    .collect(),
            ),
            Self::Product(terms) => FunctorExpr::Product(
                terms
                    .into_iter()
                    .map(|term| term.map_param_with(f))
                    .collect(),
            ),
            Self::Compose { outer, inner } => FunctorExpr::Compose {
                outer: Box::new(outer.map_param_with(f)),
                inner: Box::new(inner.map_param_with(f)),
            },
        }
    }

    /// Evaluate explicit composition by substituting `inner` for the outer
    /// variable. This preserves zero/one/sum/product structure and removes
    /// every [`Compose`](Self::Compose) node.
    pub fn expand_composition(self) -> Self
    where
        P: Clone,
    {
        match self {
            Self::Zero | Self::One | Self::Param(_) | Self::Var => self,
            Self::Sum(terms) => {
                Self::Sum(terms.into_iter().map(Self::expand_composition).collect())
            }
            Self::Product(terms) => {
                Self::Product(terms.into_iter().map(Self::expand_composition).collect())
            }
            Self::Compose { outer, inner } => {
                let inner = inner.expand_composition();
                outer.expand_composition().substitute(&inner)
            }
        }
    }

    fn substitute(self, replacement: &Self) -> Self
    where
        P: Clone,
    {
        match self {
            Self::Zero | Self::One | Self::Param(_) => self,
            Self::Var => replacement.clone(),
            Self::Sum(terms) => Self::Sum(
                terms
                    .into_iter()
                    .map(|term| term.substitute(replacement))
                    .collect(),
            ),
            Self::Product(terms) => Self::Product(
                terms
                    .into_iter()
                    .map(|term| term.substitute(replacement))
                    .collect(),
            ),
            Self::Compose { .. } => unreachable!("composition expanded before substitution"),
        }
    }
}

/// A position in a polynomial functor.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Position<P> {
    /// A non-recursive parameter or external sort.
    Param(P),
    /// The polynomial variable.
    Var,
}

impl<P> Position<P> {
    /// Whether this position contains the functor variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var)
    }

    /// Map a parameter while preserving the functor variable.
    pub fn map_param<Q>(self, f: impl FnOnce(P) -> Q) -> Position<Q> {
        match self {
            Self::Param(p) => Position::Param(f(p)),
            Self::Var => Position::Var,
        }
    }
}

/// One named field in a product.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FieldSpec<P> {
    /// Stable source-level field name.
    pub name: SmolStr,
    /// The field's parameter or recursive position.
    pub position: Position<P>,
}

impl<P> FieldSpec<P> {
    /// Construct a field.
    pub fn new(name: impl Into<SmolStr>, position: Position<P>) -> Self {
        Self {
            name: name.into(),
            position,
        }
    }

    /// Map the parameter token.
    pub fn map_param<Q>(self, f: impl FnOnce(P) -> Q) -> FieldSpec<Q> {
        FieldSpec {
            name: self.name,
            position: self.position.map_param(f),
        }
    }
}

/// A named product (record).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RecordSpec<P> {
    /// Record name.
    pub name: SmolStr,
    /// Fields in declaration order.
    pub fields: Vec<FieldSpec<P>>,
}

impl<P> RecordSpec<P> {
    /// Construct a record. Empty records are unit products and are valid.
    pub fn new(name: impl Into<SmolStr>, fields: Vec<FieldSpec<P>>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }

    /// Validate names and reject recursive fields in an aggregate record.
    pub fn validate(&self) -> Result<(), SpecError> {
        validate_product(&self.name, &self.fields, false)
    }

    /// Map the parameter token.
    pub fn map_param<Q>(self, mut f: impl FnMut(P) -> Q) -> RecordSpec<Q> {
        RecordSpec {
            name: self.name,
            fields: self
                .fields
                .into_iter()
                .map(|field| field.map_param(&mut f))
                .collect(),
        }
    }
}

/// Incremental builder for a checked record declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordBuilder<P> {
    name: SmolStr,
    fields: Vec<FieldSpec<P>>,
}

impl<P> RecordBuilder<P> {
    /// Begin a record declaration.
    pub fn new(name: impl Into<SmolStr>) -> Self {
        Self {
            name: name.into(),
            fields: Vec::new(),
        }
    }

    /// Append a non-recursive field.
    pub fn field(mut self, name: impl Into<SmolStr>, parameter: P) -> Self {
        self.fields
            .push(FieldSpec::new(name, Position::Param(parameter)));
        self
    }

    /// Validate and finish the declaration.
    pub fn build(self) -> Result<Validated<RecordSpec<P>>, SpecError> {
        Validated::try_from(RecordSpec::new(self.name, self.fields))
    }
}

/// One constructor of a variant, carrying a named product of fields.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VariantCase<P> {
    /// Constructor/tag name.
    pub name: SmolStr,
    /// Payload fields in declaration order.
    pub fields: Vec<FieldSpec<P>>,
}

impl<P> VariantCase<P> {
    /// Construct a variant case. No fields denotes a nullary constructor.
    pub fn new(name: impl Into<SmolStr>, fields: Vec<FieldSpec<P>>) -> Self {
        Self {
            name: name.into(),
            fields,
        }
    }

    /// A nullary case.
    pub fn nullary(name: impl Into<SmolStr>) -> Self {
        Self::new(name, Vec::new())
    }

    /// Map the parameter token.
    pub fn map_param<Q>(self, mut f: impl FnMut(P) -> Q) -> VariantCase<Q> {
        VariantCase {
            name: self.name,
            fields: self
                .fields
                .into_iter()
                .map(|field| field.map_param(&mut f))
                .collect(),
        }
    }
}

/// A named sum of named products.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PolynomialSpec<P> {
    /// Type/functor name.
    pub name: SmolStr,
    /// Summands in declaration order.
    pub variants: Vec<VariantCase<P>>,
}

impl<P> PolynomialSpec<P> {
    /// Construct a polynomial functor.
    pub fn new(name: impl Into<SmolStr>, variants: Vec<VariantCase<P>>) -> Self {
        Self {
            name: name.into(),
            variants,
        }
    }

    /// Construct a one-constructor product.
    pub fn record(record: RecordSpec<P>) -> Self {
        Self::new(
            record.name.clone(),
            vec![VariantCase::new(record.name, record.fields)],
        )
    }

    /// Construct an enumeration (a sum of units).
    pub fn enumeration(
        name: impl Into<SmolStr>,
        cases: impl IntoIterator<Item = impl Into<SmolStr>>,
    ) -> Self {
        Self::new(name, cases.into_iter().map(VariantCase::nullary).collect())
    }

    /// Validate a polynomial. The empty sum is allowed (the zero functor).
    pub fn validate(&self) -> Result<(), SpecError> {
        if self.name.is_empty() {
            return Err(SpecError::EmptyTypeName);
        }
        for (index, variant) in self.variants.iter().enumerate() {
            if variant.name.is_empty() {
                return Err(SpecError::EmptyName { ctor: index });
            }
            if self.variants[..index]
                .iter()
                .any(|prior| prior.name == variant.name)
            {
                return Err(SpecError::DuplicateCtor(variant.name.clone()));
            }
            validate_product(&variant.name, &variant.fields, true)?;
        }
        Ok(())
    }

    /// Whether the polynomial contains its variable.
    pub fn is_recursive(&self) -> bool {
        self.variants
            .iter()
            .flat_map(|variant| &variant.fields)
            .any(|field| field.position.is_var())
    }

    /// Map the parameter token.
    pub fn map_param<Q>(self, mut f: impl FnMut(P) -> Q) -> PolynomialSpec<Q> {
        PolynomialSpec {
            name: self.name,
            variants: self
                .variants
                .into_iter()
                .map(|variant| variant.map_param(&mut f))
                .collect(),
        }
    }

    /// Erase source-level names into the structural functor expression.
    ///
    /// Empty sums and products become [`FunctorExpr::Zero`] and
    /// [`FunctorExpr::One`] respectively.
    pub fn into_expression(self) -> FunctorExpr<P> {
        if self.variants.is_empty() {
            return FunctorExpr::Zero;
        }
        FunctorExpr::Sum(
            self.variants
                .into_iter()
                .map(|variant| {
                    if variant.fields.is_empty() {
                        FunctorExpr::One
                    } else {
                        FunctorExpr::Product(
                            variant
                                .fields
                                .into_iter()
                                .map(|field| match field.position {
                                    Position::Param(parameter) => FunctorExpr::Param(parameter),
                                    Position::Var => FunctorExpr::Var,
                                })
                                .collect(),
                        )
                    }
                })
                .collect(),
        )
    }
}

/// Incremental builder for a checked named sum-of-products.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolynomialBuilder<P> {
    name: SmolStr,
    variants: Vec<VariantCase<P>>,
}

impl<P> PolynomialBuilder<P> {
    /// Begin a polynomial declaration.
    pub fn new(name: impl Into<SmolStr>) -> Self {
        Self {
            name: name.into(),
            variants: Vec::new(),
        }
    }

    /// Append a complete constructor/product.
    pub fn variant(mut self, case: VariantCase<P>) -> Self {
        self.variants.push(case);
        self
    }

    /// Validate and finish the declaration.
    pub fn build(self) -> Result<Validated<PolynomialSpec<P>>, SpecError> {
        Validated::try_from(PolynomialSpec::new(self.name, self.variants))
    }
}

/// A non-recursive tagged union.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VariantSpec<P>(pub PolynomialSpec<P>);

impl<P> VariantSpec<P> {
    /// Construct and validate later with [`Self::validate`].
    pub fn new(name: impl Into<SmolStr>, variants: Vec<VariantCase<P>>) -> Self {
        Self(PolynomialSpec::new(name, variants))
    }

    /// Validate the sum-of-products and reject recursive positions.
    pub fn validate(&self) -> Result<(), SpecError> {
        self.0.validate()?;
        if self.0.is_recursive() {
            return Err(SpecError::UnexpectedVariable(self.0.name.clone()));
        }
        Ok(())
    }
}

/// A non-empty enumeration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EnumSpec {
    /// Enum name.
    pub name: SmolStr,
    /// Case names in declaration order.
    pub cases: Vec<SmolStr>,
}

impl EnumSpec {
    /// Construct an enum.
    pub fn new(
        name: impl Into<SmolStr>,
        cases: impl IntoIterator<Item = impl Into<SmolStr>>,
    ) -> Self {
        Self {
            name: name.into(),
            cases: cases.into_iter().map(Into::into).collect(),
        }
    }

    /// Validate non-empty, unique names.
    pub fn validate(&self) -> Result<(), SpecError> {
        if self.cases.is_empty() {
            return Err(SpecError::EmptySpec(self.name.clone()));
        }
        PolynomialSpec::<()>::enumeration(self.name.clone(), self.cases.clone()).validate()
    }

    /// View the enum as a polynomial functor independent of its parameter.
    pub fn into_polynomial<P>(self) -> PolynomialSpec<P> {
        PolynomialSpec::enumeration(self.name, self.cases)
    }
}

fn validate_product<P>(
    name: &SmolStr,
    fields: &[FieldSpec<P>],
    allow_var: bool,
) -> Result<(), SpecError> {
    if name.is_empty() {
        return Err(SpecError::EmptyTypeName);
    }
    for (index, field) in fields.iter().enumerate() {
        if field.name.is_empty() {
            return Err(SpecError::EmptyFieldName {
                aggregate: name.clone(),
                field: index,
            });
        }
        if fields[..index].iter().any(|prior| prior.name == field.name) {
            return Err(SpecError::DuplicateField {
                aggregate: name.clone(),
                field: field.name.clone(),
            });
        }
        if !allow_var && field.position.is_var() {
            return Err(SpecError::UnexpectedVariable(name.clone()));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aggregates_are_polynomial_functors() {
        let pair = RecordSpec::new(
            "pair",
            vec![
                FieldSpec::new("left", Position::Param("a")),
                FieldSpec::new("right", Position::Param("b")),
            ],
        );
        pair.validate().unwrap();
        let polynomial = PolynomialSpec::record(pair);
        assert_eq!(polynomial.variants.len(), 1);
        assert!(!polynomial.is_recursive());

        let colour = EnumSpec::new("colour", ["red", "green", "blue"]);
        colour.validate().unwrap();
        assert_eq!(colour.into_polynomial::<&str>().variants.len(), 3);
    }

    #[test]
    fn validates_names_and_aggregate_non_recursion() {
        let duplicate = VariantSpec::<()>::new(
            "result",
            vec![VariantCase::nullary("ok"), VariantCase::nullary("ok")],
        );
        assert!(matches!(
            duplicate.validate(),
            Err(SpecError::DuplicateCtor(_))
        ));

        let recursive_record =
            RecordSpec::<()>::new("bad", vec![FieldSpec::new("next", Position::Var)]);
        assert!(matches!(
            recursive_record.validate(),
            Err(SpecError::UnexpectedVariable(_))
        ));
    }

    #[test]
    fn builders_return_only_checked_specs() {
        let pair = RecordBuilder::new("pair")
            .field("left", "a")
            .field("right", "b")
            .build()
            .unwrap();
        assert_eq!(pair.fields.len(), 2);

        let bad = PolynomialBuilder::<()>::new("bad")
            .variant(VariantCase::nullary(""))
            .build();
        assert!(matches!(bad, Err(SpecError::EmptyName { .. })));
    }

    #[test]
    fn named_normal_form_erases_to_structural_expression() {
        let list = PolynomialSpec::new(
            "list",
            vec![
                VariantCase::nullary("nil"),
                VariantCase::new(
                    "cons",
                    vec![
                        FieldSpec::new("head", Position::Param("a")),
                        FieldSpec::new("tail", Position::Var),
                    ],
                ),
            ],
        );

        assert_eq!(
            list.into_expression(),
            FunctorExpr::Sum(vec![
                FunctorExpr::One,
                FunctorExpr::Product(vec![FunctorExpr::Param("a"), FunctorExpr::Var,]),
            ])
        );
    }

    #[test]
    fn composition_expands_by_substituting_only_the_variable() {
        let maybe = FunctorExpr::Sum(vec![FunctorExpr::One, FunctorExpr::Var]);
        let pair = FunctorExpr::Product(vec![FunctorExpr::Param("label"), FunctorExpr::Var]);
        let composed = FunctorExpr::compose(maybe, pair.clone());

        assert!(composed.is_recursive());
        assert_eq!(
            composed.expand_composition(),
            FunctorExpr::Sum(vec![FunctorExpr::One, pair])
        );

        let constant = FunctorExpr::compose(FunctorExpr::Param("constant"), FunctorExpr::Var);
        assert!(!constant.is_recursive());
        assert_eq!(
            constant.expand_composition(),
            FunctorExpr::Param("constant")
        );
    }
}
