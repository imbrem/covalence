//! Scoped expressions for regular datatype families with nested fixpoints.
//!
//! [`FunctorExpr`](crate::FunctorExpr) describes ordinary polynomial
//! endofunctors and their composition. This module adds the distinct operation
//! needed for nested datatypes such as `List(X) = μY. 1 + X × Y`.

/// A regular datatype family with capture-safe nested fixpoints.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DatatypeFamilyExpr<P> {
    /// The empty type.
    Zero,
    /// The unit type.
    One,
    /// A constant parameter.
    Param(P),
    /// The free argument of the datatype family.
    FamilyVar,
    /// A de Bruijn reference to a surrounding [`Least`](Self::Least).
    ///
    /// Index zero names the nearest enclosing least fixpoint.
    Bound(usize),
    /// A finite coproduct.
    Sum(Vec<Self>),
    /// A finite product.
    Product(Vec<Self>),
    /// A nested least fixpoint. Its body binds [`Bound(0)`](Self::Bound).
    Least(Box<Self>),
    /// A nested greatest fixpoint. Its body binds [`Bound(0)`](Self::Bound).
    Greatest(Box<Self>),
}

/// Why a datatype-family expression is not well scoped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DatatypeFamilyError {
    /// A de Bruijn index has no enclosing fixpoint binder.
    UnboundFixpointVariable { index: usize, depth: usize },
}

impl std::fmt::Display for DatatypeFamilyError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundFixpointVariable { index, depth } => write!(
                formatter,
                "fixpoint variable {index} is unbound at binder depth {depth}"
            ),
        }
    }
}

impl std::error::Error for DatatypeFamilyError {}

impl<P> DatatypeFamilyExpr<P> {
    /// Form a nested least fixpoint.
    pub fn least(body: Self) -> Self {
        Self::Least(Box::new(body))
    }

    /// Form a nested greatest fixpoint.
    pub fn greatest(body: Self) -> Self {
        Self::Greatest(Box::new(body))
    }

    /// Check every bound-variable reference against its lexical binder depth.
    pub fn validate(&self) -> Result<(), DatatypeFamilyError> {
        self.validate_at(0)
    }

    fn validate_at(&self, depth: usize) -> Result<(), DatatypeFamilyError> {
        match self {
            Self::Zero | Self::One | Self::Param(_) | Self::FamilyVar => Ok(()),
            Self::Bound(index) if *index < depth => Ok(()),
            Self::Bound(index) => Err(DatatypeFamilyError::UnboundFixpointVariable {
                index: *index,
                depth,
            }),
            Self::Sum(terms) | Self::Product(terms) => {
                terms.iter().try_for_each(|term| term.validate_at(depth))
            }
            Self::Least(body) | Self::Greatest(body) => body.validate_at(depth + 1),
        }
    }

    /// Whether the family depends on its free argument.
    pub fn is_recursive(&self) -> bool {
        match self {
            Self::FamilyVar => true,
            Self::Zero | Self::One | Self::Param(_) | Self::Bound(_) => false,
            Self::Sum(terms) | Self::Product(terms) => terms.iter().any(Self::is_recursive),
            Self::Least(body) | Self::Greatest(body) => body.is_recursive(),
        }
    }

    /// Map constant parameters without changing either variable namespace.
    pub fn map_param<Q>(self, mut map: impl FnMut(P) -> Q) -> DatatypeFamilyExpr<Q> {
        self.map_param_with(&mut map)
    }

    fn map_param_with<Q>(self, map: &mut impl FnMut(P) -> Q) -> DatatypeFamilyExpr<Q> {
        match self {
            Self::Zero => DatatypeFamilyExpr::Zero,
            Self::One => DatatypeFamilyExpr::One,
            Self::Param(parameter) => DatatypeFamilyExpr::Param(map(parameter)),
            Self::FamilyVar => DatatypeFamilyExpr::FamilyVar,
            Self::Bound(index) => DatatypeFamilyExpr::Bound(index),
            Self::Sum(terms) => DatatypeFamilyExpr::Sum(
                terms
                    .into_iter()
                    .map(|term| term.map_param_with(map))
                    .collect(),
            ),
            Self::Product(terms) => DatatypeFamilyExpr::Product(
                terms
                    .into_iter()
                    .map(|term| term.map_param_with(map))
                    .collect(),
            ),
            Self::Least(body) => DatatypeFamilyExpr::Least(Box::new(body.map_param_with(map))),
            Self::Greatest(body) => {
                DatatypeFamilyExpr::Greatest(Box::new(body.map_param_with(map)))
            }
        }
    }

    /// Substitute an expression for the free family argument.
    ///
    /// Bound fixpoint variables are a separate namespace, so substitution
    /// cannot capture variables in `replacement`.
    pub fn substitute_family(self, replacement: &Self) -> Result<Self, DatatypeFamilyError>
    where
        P: Clone,
    {
        self.validate()?;
        replacement.validate()?;
        let result = self.substitute_family_unchecked(replacement);
        result.validate()?;
        Ok(result)
    }

    fn substitute_family_unchecked(self, replacement: &Self) -> Self
    where
        P: Clone,
    {
        match self {
            Self::FamilyVar => replacement.clone(),
            Self::Zero | Self::One | Self::Param(_) | Self::Bound(_) => self,
            Self::Sum(terms) => Self::Sum(
                terms
                    .into_iter()
                    .map(|term| term.substitute_family_unchecked(replacement))
                    .collect(),
            ),
            Self::Product(terms) => Self::Product(
                terms
                    .into_iter()
                    .map(|term| term.substitute_family_unchecked(replacement))
                    .collect(),
            ),
            Self::Least(body) => {
                Self::Least(Box::new(body.substitute_family_unchecked(replacement)))
            }
            Self::Greatest(body) => {
                Self::Greatest(Box::new(body.substitute_family_unchecked(replacement)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_list_family_is_well_scoped_and_recursive_in_its_argument() {
        let list = DatatypeFamilyExpr::least(DatatypeFamilyExpr::Sum(vec![
            DatatypeFamilyExpr::One,
            DatatypeFamilyExpr::Product(vec![
                DatatypeFamilyExpr::<&str>::FamilyVar,
                DatatypeFamilyExpr::Bound(0),
            ]),
        ]));
        assert_eq!(list.validate(), Ok(()));
        assert!(list.is_recursive());
    }

    #[test]
    fn validation_rejects_unbound_fixpoint_variables() {
        assert_eq!(
            DatatypeFamilyExpr::<()>::Bound(0).validate(),
            Err(DatatypeFamilyError::UnboundFixpointVariable { index: 0, depth: 0 })
        );
        assert_eq!(
            DatatypeFamilyExpr::<()>::least(DatatypeFamilyExpr::Bound(1)).validate(),
            Err(DatatypeFamilyError::UnboundFixpointVariable { index: 1, depth: 1 })
        );
    }

    #[test]
    fn family_substitution_does_not_capture_nested_fixpoint_variables() {
        let list = DatatypeFamilyExpr::least(DatatypeFamilyExpr::Product(vec![
            DatatypeFamilyExpr::FamilyVar,
            DatatypeFamilyExpr::Bound(0),
        ]));
        let replaced = list
            .substitute_family(&DatatypeFamilyExpr::Param("element"))
            .unwrap();
        assert_eq!(
            replaced,
            DatatypeFamilyExpr::least(DatatypeFamilyExpr::Product(vec![
                DatatypeFamilyExpr::Param("element"),
                DatatypeFamilyExpr::Bound(0),
            ]))
        );
        assert_eq!(replaced.validate(), Ok(()));
    }
}
