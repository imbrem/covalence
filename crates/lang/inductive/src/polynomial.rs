//! Plain-data descriptions of records, variants, enums, and polynomial
//! functors.
//!
//! [`PolynomialSpec`] is a named sum of named products.  A field is either a
//! parameter supplied by the surrounding theory or the functor variable.
//! Thus a declaration denotes
//!
//! ```text
//! F(X) = Σ variant. Π field. (parameter | X)
//! ```
//!
//! Records, variants, and enums are the non-recursive aggregate views of the
//! same data.  Fixpoint APIs consume the full polynomial form.

use smol_str::SmolStr;

use crate::error::SpecError;
use crate::validated::Validated;

// TODO(cov:inductive.functor-expressions, major): Extend direct Param/Var positions with zero, one, sum, product, and composition expressions while retaining named sum-of-products as the ergonomic normal form.

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
}
