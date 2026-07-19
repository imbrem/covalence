//! Automatically derived interpretation and functor action for datatype families.
//!
//! The traversal in this module is the common implementation pipeline:
//! backends supply only the ambient category's initial/terminal objects,
//! sums, products, parameters, and fixpoint operations.  In particular a
//! nested fixpoint is never treated as an opaque parameter.

use crate::{DatatypeFamilyError, DatatypeFamilyExpr};

/// A well-scoped datatype family.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValidatedDatatypeFamily<P>(DatatypeFamilyExpr<P>);

impl<P> ValidatedDatatypeFamily<P> {
    /// Borrow the checked expression.
    pub fn expression(&self) -> &DatatypeFamilyExpr<P> {
        &self.0
    }

    /// Recover the checked plain-data expression.
    pub fn into_expression(self) -> DatatypeFamilyExpr<P> {
        self.0
    }
}

impl<P> TryFrom<DatatypeFamilyExpr<P>> for ValidatedDatatypeFamily<P> {
    type Error = DatatypeFamilyError;

    fn try_from(expression: DatatypeFamilyExpr<P>) -> Result<Self, Self::Error> {
        expression.validate()?;
        Ok(Self(expression))
    }
}

/// The kind of a nested fixpoint request.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FamilyFixpointKind {
    /// A least fixpoint, `μ`.
    Least,
    /// A greatest fixpoint, `ν`.
    Greatest,
}

/// A transparent object expression produced by [`SymbolicFamilyBackend`].
///
/// This backend is useful for API planning, serialization tests, and checking
/// that consumers do not accidentally rely on a concrete logic. It makes no
/// proof claim.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SymbolicFamilyObject<P> {
    Zero,
    One,
    Parameter(P),
    Sum(Vec<Self>),
    Product(Vec<Self>),
    Fixpoint {
        kind: FamilyFixpointKind,
        body: DatatypeFamilyExpr<P>,
        family: Box<Self>,
        outer_bounds: Vec<Self>,
    },
}

/// A transparent derived map produced by [`SymbolicFamilyBackend`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SymbolicFamilyArrow<P> {
    Identity(SymbolicFamilyObject<P>),
    Supplied {
        source: SymbolicFamilyObject<P>,
        target: SymbolicFamilyObject<P>,
        name: String,
    },
    Sum(Vec<Self>),
    Product(Vec<Self>),
    Fixpoint {
        kind: FamilyFixpointKind,
        body: DatatypeFamilyExpr<P>,
        family_arrow: Box<Self>,
    },
}

/// Proof-free reference backend for scoped family interpretation.
#[derive(Clone, Copy, Debug, Default)]
pub struct SymbolicFamilyBackend;

impl<P: Clone> DatatypeFamilyBackend<P> for SymbolicFamilyBackend {
    type Object = SymbolicFamilyObject<P>;
    type Arrow = SymbolicFamilyArrow<P>;
    type Error = std::convert::Infallible;

    fn zero(&self) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::Zero)
    }
    fn one(&self) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::One)
    }
    fn parameter(&self, parameter: &P) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::Parameter(parameter.clone()))
    }
    fn sum(&self, terms: &[Self::Object]) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::Sum(terms.to_vec()))
    }
    fn product(&self, terms: &[Self::Object]) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::Product(terms.to_vec()))
    }
    fn identity(&self, object: &Self::Object) -> Result<Self::Arrow, Self::Error> {
        Ok(SymbolicFamilyArrow::Identity(object.clone()))
    }
    fn sum_map(
        &self,
        _sources: &[Self::Object],
        _targets: &[Self::Object],
        arrows: &[Self::Arrow],
    ) -> Result<Self::Arrow, Self::Error> {
        Ok(SymbolicFamilyArrow::Sum(arrows.to_vec()))
    }
    fn product_map(
        &self,
        _sources: &[Self::Object],
        _targets: &[Self::Object],
        arrows: &[Self::Arrow],
    ) -> Result<Self::Arrow, Self::Error> {
        Ok(SymbolicFamilyArrow::Product(arrows.to_vec()))
    }
    fn least_object(
        &self,
        body: &DatatypeFamilyExpr<P>,
        family: &Self::Object,
        outer_bounds: &[Self::Object],
    ) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::Fixpoint {
            kind: FamilyFixpointKind::Least,
            body: body.clone(),
            family: Box::new(family.clone()),
            outer_bounds: outer_bounds.to_vec(),
        })
    }
    fn greatest_object(
        &self,
        body: &DatatypeFamilyExpr<P>,
        family: &Self::Object,
        outer_bounds: &[Self::Object],
    ) -> Result<Self::Object, Self::Error> {
        Ok(SymbolicFamilyObject::Fixpoint {
            kind: FamilyFixpointKind::Greatest,
            body: body.clone(),
            family: Box::new(family.clone()),
            outer_bounds: outer_bounds.to_vec(),
        })
    }
    fn least_map(
        &self,
        body: &DatatypeFamilyExpr<P>,
        _source_family: &Self::Object,
        _target_family: &Self::Object,
        family_arrow: &Self::Arrow,
        _source_bounds: &[Self::Object],
        _target_bounds: &[Self::Object],
    ) -> Result<Self::Arrow, Self::Error> {
        Ok(SymbolicFamilyArrow::Fixpoint {
            kind: FamilyFixpointKind::Least,
            body: body.clone(),
            family_arrow: Box::new(family_arrow.clone()),
        })
    }
    fn greatest_map(
        &self,
        body: &DatatypeFamilyExpr<P>,
        _source_family: &Self::Object,
        _target_family: &Self::Object,
        family_arrow: &Self::Arrow,
        _source_bounds: &[Self::Object],
        _target_bounds: &[Self::Object],
    ) -> Result<Self::Arrow, Self::Error> {
        Ok(SymbolicFamilyArrow::Fixpoint {
            kind: FamilyFixpointKind::Greatest,
            body: body.clone(),
            family_arrow: Box::new(family_arrow.clone()),
        })
    }
}

/// Name an arrow between two symbolic objects.
pub fn symbolic_arrow<P>(
    source: SymbolicFamilyObject<P>,
    target: SymbolicFamilyObject<P>,
    name: impl Into<String>,
) -> SymbolicFamilyArrow<P> {
    SymbolicFamilyArrow::Supplied {
        source,
        target,
        name: name.into(),
    }
}

/// Backend capabilities from which family interpretation and `map` are derived.
///
/// `least_object`/`greatest_object` construct the carrier for the supplied
/// open body. `least_map`/`greatest_map` lift a map of the body's free family
/// parameter to the corresponding fixpoint carriers. The body remains scoped:
/// `Bound(0)` denotes the carrier being constructed and higher indices denote
/// `outer_bounds`.
pub trait DatatypeFamilyBackend<P> {
    /// Objects in the backend's ambient category.
    type Object: Clone;
    /// Arrows between objects.
    type Arrow: Clone;
    /// Interpretation failure.
    type Error;

    fn zero(&self) -> Result<Self::Object, Self::Error>;
    fn one(&self) -> Result<Self::Object, Self::Error>;
    fn parameter(&self, parameter: &P) -> Result<Self::Object, Self::Error>;
    fn sum(&self, terms: &[Self::Object]) -> Result<Self::Object, Self::Error>;
    fn product(&self, terms: &[Self::Object]) -> Result<Self::Object, Self::Error>;

    fn identity(&self, object: &Self::Object) -> Result<Self::Arrow, Self::Error>;
    fn sum_map(
        &self,
        sources: &[Self::Object],
        targets: &[Self::Object],
        arrows: &[Self::Arrow],
    ) -> Result<Self::Arrow, Self::Error>;
    fn product_map(
        &self,
        sources: &[Self::Object],
        targets: &[Self::Object],
        arrows: &[Self::Arrow],
    ) -> Result<Self::Arrow, Self::Error>;

    fn least_object(
        &self,
        body: &DatatypeFamilyExpr<P>,
        family: &Self::Object,
        outer_bounds: &[Self::Object],
    ) -> Result<Self::Object, Self::Error>;
    fn greatest_object(
        &self,
        body: &DatatypeFamilyExpr<P>,
        family: &Self::Object,
        outer_bounds: &[Self::Object],
    ) -> Result<Self::Object, Self::Error>;
    #[allow(clippy::too_many_arguments)]
    fn least_map(
        &self,
        body: &DatatypeFamilyExpr<P>,
        source_family: &Self::Object,
        target_family: &Self::Object,
        family_arrow: &Self::Arrow,
        source_bounds: &[Self::Object],
        target_bounds: &[Self::Object],
    ) -> Result<Self::Arrow, Self::Error>;
    #[allow(clippy::too_many_arguments)]
    fn greatest_map(
        &self,
        body: &DatatypeFamilyExpr<P>,
        source_family: &Self::Object,
        target_family: &Self::Object,
        family_arrow: &Self::Arrow,
        source_bounds: &[Self::Object],
        target_bounds: &[Self::Object],
    ) -> Result<Self::Arrow, Self::Error>;
}

/// Interpret `F(X)`, recursively invoking nested fixpoint capabilities.
pub fn interpret_family<P, B: DatatypeFamilyBackend<P>>(
    backend: &B,
    family: &ValidatedDatatypeFamily<P>,
    variable: &B::Object,
) -> Result<B::Object, B::Error> {
    interpret_at(backend, family.expression(), variable, &[])
}

fn interpret_at<P, B: DatatypeFamilyBackend<P>>(
    backend: &B,
    expression: &DatatypeFamilyExpr<P>,
    variable: &B::Object,
    bounds: &[B::Object],
) -> Result<B::Object, B::Error> {
    match expression {
        DatatypeFamilyExpr::Zero => backend.zero(),
        DatatypeFamilyExpr::One => backend.one(),
        DatatypeFamilyExpr::Param(parameter) => backend.parameter(parameter),
        DatatypeFamilyExpr::FamilyVar => Ok(variable.clone()),
        DatatypeFamilyExpr::Bound(index) => Ok(bounds[*index].clone()),
        DatatypeFamilyExpr::Sum(terms) => {
            let objects = terms
                .iter()
                .map(|term| interpret_at(backend, term, variable, bounds))
                .collect::<Result<Vec<_>, _>>()?;
            backend.sum(&objects)
        }
        DatatypeFamilyExpr::Product(terms) => {
            let objects = terms
                .iter()
                .map(|term| interpret_at(backend, term, variable, bounds))
                .collect::<Result<Vec<_>, _>>()?;
            backend.product(&objects)
        }
        DatatypeFamilyExpr::Least(body) => backend.least_object(body, variable, bounds),
        DatatypeFamilyExpr::Greatest(body) => backend.greatest_object(body, variable, bounds),
    }
}

/// Automatically lift `arrow : X → Y` to `F(arrow) : F(X) → F(Y)`.
pub fn map_family<P, B: DatatypeFamilyBackend<P>>(
    backend: &B,
    family: &ValidatedDatatypeFamily<P>,
    source: &B::Object,
    target: &B::Object,
    arrow: &B::Arrow,
) -> Result<B::Arrow, B::Error> {
    map_at(
        backend,
        family.expression(),
        source,
        target,
        arrow,
        &[],
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
fn map_at<P, B: DatatypeFamilyBackend<P>>(
    backend: &B,
    expression: &DatatypeFamilyExpr<P>,
    source: &B::Object,
    target: &B::Object,
    arrow: &B::Arrow,
    source_bounds: &[B::Object],
    target_bounds: &[B::Object],
) -> Result<B::Arrow, B::Error> {
    match expression {
        DatatypeFamilyExpr::FamilyVar => Ok(arrow.clone()),
        DatatypeFamilyExpr::Zero => backend.identity(&backend.zero()?),
        DatatypeFamilyExpr::One => backend.identity(&backend.one()?),
        DatatypeFamilyExpr::Param(parameter) => backend.identity(&backend.parameter(parameter)?),
        DatatypeFamilyExpr::Bound(index) => {
            // Bound carriers do not vary during the outer family map. Nested
            // fixpoint lifting is delegated as one coherent operation below.
            backend.identity(&source_bounds[*index])
        }
        DatatypeFamilyExpr::Sum(terms) | DatatypeFamilyExpr::Product(terms) => {
            let sources = terms
                .iter()
                .map(|term| interpret_at(backend, term, source, source_bounds))
                .collect::<Result<Vec<_>, _>>()?;
            let targets = terms
                .iter()
                .map(|term| interpret_at(backend, term, target, target_bounds))
                .collect::<Result<Vec<_>, _>>()?;
            let arrows = terms
                .iter()
                .map(|term| {
                    map_at(
                        backend,
                        term,
                        source,
                        target,
                        arrow,
                        source_bounds,
                        target_bounds,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if matches!(expression, DatatypeFamilyExpr::Sum(_)) {
                backend.sum_map(&sources, &targets, &arrows)
            } else {
                backend.product_map(&sources, &targets, &arrows)
            }
        }
        DatatypeFamilyExpr::Least(body) => {
            backend.least_map(body, source, target, arrow, source_bounds, target_bounds)
        }
        DatatypeFamilyExpr::Greatest(body) => {
            backend.greatest_map(body, source, target, arrow, source_bounds, target_bounds)
        }
    }
}

/// Evidence-producing companion to [`DatatypeFamilyBackend`].
///
/// The `combine_*` methods are the categorical laws for finite sums and
/// products. The generic traversal supplies their recursively derived premises.
/// Consequently, a backend needs datatype-specific law machinery only for the
/// two fixpoint methods.
pub trait DatatypeFamilyLaws<P>: DatatypeFamilyBackend<P> {
    /// Backend-native equality evidence, such as a kernel theorem handle.
    type Evidence: Clone;

    /// Evidence that mapping the identity arrow at a non-fixpoint leaf is the
    /// identity on that leaf.
    fn leaf_identity(
        &self,
        object: &Self::Object,
        mapped: &Self::Arrow,
    ) -> Result<Self::Evidence, Self::Error>;
    /// Compose identity evidence for a sum.
    fn sum_identity(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error>;
    /// Compose identity evidence for a product.
    fn product_identity(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error>;
    /// Identity law for a nested fixpoint map.
    fn fixpoint_identity(
        &self,
        kind: FamilyFixpointKind,
        body: &DatatypeFamilyExpr<P>,
        family: &Self::Object,
        outer_bounds: &[Self::Object],
    ) -> Result<Self::Evidence, Self::Error>;

    /// Evidence for preservation of composition at a leaf.
    fn leaf_composition(
        &self,
        source: &Self::Object,
        middle: &Self::Object,
        target: &Self::Object,
        first: &Self::Arrow,
        second: &Self::Arrow,
    ) -> Result<Self::Evidence, Self::Error>;
    /// Compose composition evidence for a sum.
    fn sum_composition(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error>;
    /// Compose composition evidence for a product.
    fn product_composition(
        &self,
        evidence: &[Self::Evidence],
    ) -> Result<Self::Evidence, Self::Error>;
    /// Composition law for a nested fixpoint map.
    #[allow(clippy::too_many_arguments)]
    fn fixpoint_composition(
        &self,
        kind: FamilyFixpointKind,
        body: &DatatypeFamilyExpr<P>,
        source: &Self::Object,
        middle: &Self::Object,
        target: &Self::Object,
        first: &Self::Arrow,
        second: &Self::Arrow,
        source_bounds: &[Self::Object],
        middle_bounds: &[Self::Object],
        target_bounds: &[Self::Object],
    ) -> Result<Self::Evidence, Self::Error>;

    /// Transport equality of arrows through a leaf map.
    fn leaf_congruence(
        &self,
        source: &Self::Object,
        target: &Self::Object,
        left: &Self::Arrow,
        right: &Self::Arrow,
        equal: &Self::Evidence,
    ) -> Result<Self::Evidence, Self::Error>;
    /// Compose congruence evidence for a sum.
    fn sum_congruence(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error>;
    /// Compose congruence evidence for a product.
    fn product_congruence(
        &self,
        evidence: &[Self::Evidence],
    ) -> Result<Self::Evidence, Self::Error>;
    /// Congruence law for a nested fixpoint map.
    #[allow(clippy::too_many_arguments)]
    fn fixpoint_congruence(
        &self,
        kind: FamilyFixpointKind,
        body: &DatatypeFamilyExpr<P>,
        source: &Self::Object,
        target: &Self::Object,
        left: &Self::Arrow,
        right: &Self::Arrow,
        equal: &Self::Evidence,
        source_bounds: &[Self::Object],
        target_bounds: &[Self::Object],
    ) -> Result<Self::Evidence, Self::Error>;
}

/// Derive evidence for `F(id) = id`.
pub fn family_map_identity<P, B: DatatypeFamilyLaws<P>>(
    backend: &B,
    family: &ValidatedDatatypeFamily<P>,
    object: &B::Object,
) -> Result<B::Evidence, B::Error> {
    identity_at(backend, family.expression(), object, &[])
}

fn identity_at<P, B: DatatypeFamilyLaws<P>>(
    backend: &B,
    expression: &DatatypeFamilyExpr<P>,
    variable: &B::Object,
    bounds: &[B::Object],
) -> Result<B::Evidence, B::Error> {
    match expression {
        DatatypeFamilyExpr::Sum(terms) | DatatypeFamilyExpr::Product(terms) => {
            let evidence = terms
                .iter()
                .map(|term| identity_at(backend, term, variable, bounds))
                .collect::<Result<Vec<_>, _>>()?;
            if matches!(expression, DatatypeFamilyExpr::Sum(_)) {
                backend.sum_identity(&evidence)
            } else {
                backend.product_identity(&evidence)
            }
        }
        DatatypeFamilyExpr::Least(body) => {
            backend.fixpoint_identity(FamilyFixpointKind::Least, body, variable, bounds)
        }
        DatatypeFamilyExpr::Greatest(body) => {
            backend.fixpoint_identity(FamilyFixpointKind::Greatest, body, variable, bounds)
        }
        leaf => {
            let object = interpret_at(backend, leaf, variable, bounds)?;
            let mapped = map_at(
                backend,
                leaf,
                variable,
                variable,
                &backend.identity(variable)?,
                bounds,
                bounds,
            )?;
            backend.leaf_identity(&object, &mapped)
        }
    }
}

/// Derive evidence for `F(g ∘ f) = F(g) ∘ F(f)`.
#[allow(clippy::too_many_arguments)]
pub fn family_map_composition<P, B: DatatypeFamilyLaws<P>>(
    backend: &B,
    family: &ValidatedDatatypeFamily<P>,
    source: &B::Object,
    middle: &B::Object,
    target: &B::Object,
    first: &B::Arrow,
    second: &B::Arrow,
) -> Result<B::Evidence, B::Error> {
    composition_at(
        backend,
        family.expression(),
        source,
        middle,
        target,
        first,
        second,
        &[],
        &[],
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
fn composition_at<P, B: DatatypeFamilyLaws<P>>(
    backend: &B,
    expression: &DatatypeFamilyExpr<P>,
    source: &B::Object,
    middle: &B::Object,
    target: &B::Object,
    first: &B::Arrow,
    second: &B::Arrow,
    source_bounds: &[B::Object],
    middle_bounds: &[B::Object],
    target_bounds: &[B::Object],
) -> Result<B::Evidence, B::Error> {
    match expression {
        DatatypeFamilyExpr::Sum(terms) | DatatypeFamilyExpr::Product(terms) => {
            let evidence = terms
                .iter()
                .map(|term| {
                    composition_at(
                        backend,
                        term,
                        source,
                        middle,
                        target,
                        first,
                        second,
                        source_bounds,
                        middle_bounds,
                        target_bounds,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if matches!(expression, DatatypeFamilyExpr::Sum(_)) {
                backend.sum_composition(&evidence)
            } else {
                backend.product_composition(&evidence)
            }
        }
        DatatypeFamilyExpr::Least(body) | DatatypeFamilyExpr::Greatest(body) => backend
            .fixpoint_composition(
                if matches!(expression, DatatypeFamilyExpr::Least(_)) {
                    FamilyFixpointKind::Least
                } else {
                    FamilyFixpointKind::Greatest
                },
                body,
                source,
                middle,
                target,
                first,
                second,
                source_bounds,
                middle_bounds,
                target_bounds,
            ),
        leaf => {
            let source_object = interpret_at(backend, leaf, source, source_bounds)?;
            let middle_object = interpret_at(backend, leaf, middle, middle_bounds)?;
            let target_object = interpret_at(backend, leaf, target, target_bounds)?;
            let mapped_first = map_at(
                backend,
                leaf,
                source,
                middle,
                first,
                source_bounds,
                middle_bounds,
            )?;
            let mapped_second = map_at(
                backend,
                leaf,
                middle,
                target,
                second,
                middle_bounds,
                target_bounds,
            )?;
            backend.leaf_composition(
                &source_object,
                &middle_object,
                &target_object,
                &mapped_first,
                &mapped_second,
            )
        }
    }
}

/// Derive congruence evidence from evidence that two input arrows are equal.
#[allow(clippy::too_many_arguments)]
pub fn family_map_congruence<P, B: DatatypeFamilyLaws<P>>(
    backend: &B,
    family: &ValidatedDatatypeFamily<P>,
    source: &B::Object,
    target: &B::Object,
    left: &B::Arrow,
    right: &B::Arrow,
    equal: &B::Evidence,
) -> Result<B::Evidence, B::Error> {
    congruence_at(
        backend,
        family.expression(),
        source,
        target,
        left,
        right,
        equal,
        &[],
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
fn congruence_at<P, B: DatatypeFamilyLaws<P>>(
    backend: &B,
    expression: &DatatypeFamilyExpr<P>,
    source: &B::Object,
    target: &B::Object,
    left: &B::Arrow,
    right: &B::Arrow,
    equal: &B::Evidence,
    source_bounds: &[B::Object],
    target_bounds: &[B::Object],
) -> Result<B::Evidence, B::Error> {
    match expression {
        DatatypeFamilyExpr::Sum(terms) | DatatypeFamilyExpr::Product(terms) => {
            let evidence = terms
                .iter()
                .map(|term| {
                    congruence_at(
                        backend,
                        term,
                        source,
                        target,
                        left,
                        right,
                        equal,
                        source_bounds,
                        target_bounds,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if matches!(expression, DatatypeFamilyExpr::Sum(_)) {
                backend.sum_congruence(&evidence)
            } else {
                backend.product_congruence(&evidence)
            }
        }
        DatatypeFamilyExpr::Least(body) | DatatypeFamilyExpr::Greatest(body) => backend
            .fixpoint_congruence(
                if matches!(expression, DatatypeFamilyExpr::Least(_)) {
                    FamilyFixpointKind::Least
                } else {
                    FamilyFixpointKind::Greatest
                },
                body,
                source,
                target,
                left,
                right,
                equal,
                source_bounds,
                target_bounds,
            ),
        leaf => {
            let source_object = interpret_at(backend, leaf, source, source_bounds)?;
            let target_object = interpret_at(backend, leaf, target, target_bounds)?;
            let mapped_left = map_at(
                backend,
                leaf,
                source,
                target,
                left,
                source_bounds,
                target_bounds,
            )?;
            let mapped_right = map_at(
                backend,
                leaf,
                source,
                target,
                right,
                source_bounds,
                target_bounds,
            )?;
            backend.leaf_congruence(
                &source_object,
                &target_object,
                &mapped_left,
                &mapped_right,
                equal,
            )
        }
    }
}

/// Proof-free evidence tree used by [`SymbolicFamilyBackend`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SymbolicFamilyEvidence<P> {
    Leaf(&'static str),
    Sum(Vec<Self>),
    Product(Vec<Self>),
    Fixpoint {
        kind: FamilyFixpointKind,
        body: DatatypeFamilyExpr<P>,
        law: &'static str,
    },
}

impl<P: Clone> DatatypeFamilyLaws<P> for SymbolicFamilyBackend {
    type Evidence = SymbolicFamilyEvidence<P>;

    fn leaf_identity(
        &self,
        _: &Self::Object,
        _: &Self::Arrow,
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Leaf("identity"))
    }
    fn sum_identity(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Sum(evidence.to_vec()))
    }
    fn product_identity(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Product(evidence.to_vec()))
    }
    fn fixpoint_identity(
        &self,
        kind: FamilyFixpointKind,
        body: &DatatypeFamilyExpr<P>,
        _: &Self::Object,
        _: &[Self::Object],
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Fixpoint {
            kind,
            body: body.clone(),
            law: "identity",
        })
    }
    fn leaf_composition(
        &self,
        _: &Self::Object,
        _: &Self::Object,
        _: &Self::Object,
        _: &Self::Arrow,
        _: &Self::Arrow,
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Leaf("composition"))
    }
    fn sum_composition(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Sum(evidence.to_vec()))
    }
    fn product_composition(
        &self,
        evidence: &[Self::Evidence],
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Product(evidence.to_vec()))
    }
    fn fixpoint_composition(
        &self,
        kind: FamilyFixpointKind,
        body: &DatatypeFamilyExpr<P>,
        _: &Self::Object,
        _: &Self::Object,
        _: &Self::Object,
        _: &Self::Arrow,
        _: &Self::Arrow,
        _: &[Self::Object],
        _: &[Self::Object],
        _: &[Self::Object],
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Fixpoint {
            kind,
            body: body.clone(),
            law: "composition",
        })
    }
    fn leaf_congruence(
        &self,
        _: &Self::Object,
        _: &Self::Object,
        _: &Self::Arrow,
        _: &Self::Arrow,
        _: &Self::Evidence,
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Leaf("congruence"))
    }
    fn sum_congruence(&self, evidence: &[Self::Evidence]) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Sum(evidence.to_vec()))
    }
    fn product_congruence(
        &self,
        evidence: &[Self::Evidence],
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Product(evidence.to_vec()))
    }
    fn fixpoint_congruence(
        &self,
        kind: FamilyFixpointKind,
        body: &DatatypeFamilyExpr<P>,
        _: &Self::Object,
        _: &Self::Object,
        _: &Self::Arrow,
        _: &Self::Arrow,
        _: &Self::Evidence,
        _: &[Self::Object],
        _: &[Self::Object],
    ) -> Result<Self::Evidence, Self::Error> {
        Ok(SymbolicFamilyEvidence::Fixpoint {
            kind,
            body: body.clone(),
            law: "congruence",
        })
    }
}

// TODO(cov:inductive.family-native-hol-laws, major): Implement DatatypeFamilyLaws for a NativeHol family backend once its μ/ν capability returns proof-bearing fixpoint packages; the structural derivation above must consume existing kernel theorems and must not mint law evidence.

#[cfg(test)]
mod tests {
    use super::*;

    struct Symbolic;

    impl DatatypeFamilyBackend<&'static str> for Symbolic {
        type Object = String;
        type Arrow = String;
        type Error = std::convert::Infallible;

        fn zero(&self) -> Result<String, Self::Error> {
            Ok("0".into())
        }
        fn one(&self) -> Result<String, Self::Error> {
            Ok("1".into())
        }
        fn parameter(&self, p: &&'static str) -> Result<String, Self::Error> {
            Ok(format!("P[{p}]"))
        }
        fn sum(&self, xs: &[String]) -> Result<String, Self::Error> {
            Ok(format!("({})", xs.join("+")))
        }
        fn product(&self, xs: &[String]) -> Result<String, Self::Error> {
            Ok(format!("({})", xs.join("×")))
        }
        fn identity(&self, x: &String) -> Result<String, Self::Error> {
            Ok(format!("id[{x}]"))
        }
        fn sum_map(
            &self,
            _: &[String],
            _: &[String],
            fs: &[String],
        ) -> Result<String, Self::Error> {
            Ok(format!("sum-map({})", fs.join(",")))
        }
        fn product_map(
            &self,
            _: &[String],
            _: &[String],
            fs: &[String],
        ) -> Result<String, Self::Error> {
            Ok(format!("product-map({})", fs.join(",")))
        }
        fn least_object(
            &self,
            body: &DatatypeFamilyExpr<&'static str>,
            x: &String,
            _: &[String],
        ) -> Result<String, Self::Error> {
            Ok(format!("μ({body:?})[{x}]"))
        }
        fn greatest_object(
            &self,
            body: &DatatypeFamilyExpr<&'static str>,
            x: &String,
            _: &[String],
        ) -> Result<String, Self::Error> {
            Ok(format!("ν({body:?})[{x}]"))
        }
        fn least_map(
            &self,
            _: &DatatypeFamilyExpr<&'static str>,
            _: &String,
            _: &String,
            f: &String,
            _: &[String],
            _: &[String],
        ) -> Result<String, Self::Error> {
            Ok(format!("μmap({f})"))
        }
        fn greatest_map(
            &self,
            _: &DatatypeFamilyExpr<&'static str>,
            _: &String,
            _: &String,
            f: &String,
            _: &[String],
            _: &[String],
        ) -> Result<String, Self::Error> {
            Ok(format!("νmap({f})"))
        }
    }

    #[test]
    fn nested_fixpoint_interpretation_and_map_are_derived() {
        let expression = DatatypeFamilyExpr::Sum(vec![
            DatatypeFamilyExpr::Param("label"),
            DatatypeFamilyExpr::least(DatatypeFamilyExpr::Sum(vec![
                DatatypeFamilyExpr::One,
                DatatypeFamilyExpr::Product(vec![
                    DatatypeFamilyExpr::FamilyVar,
                    DatatypeFamilyExpr::Bound(0),
                ]),
            ])),
        ]);
        let family = ValidatedDatatypeFamily::try_from(expression).unwrap();
        assert!(
            interpret_family(&Symbolic, &family, &"X".into())
                .unwrap()
                .contains("μ(")
        );
        assert_eq!(
            map_family(&Symbolic, &family, &"X".into(), &"Y".into(), &"f".into()).unwrap(),
            "sum-map(id[P[label]],μmap(f))"
        );
    }

    #[test]
    fn symbolic_law_evidence_preserves_nested_fixpoint_boundaries() {
        let family = ValidatedDatatypeFamily::try_from(DatatypeFamilyExpr::Sum(vec![
            DatatypeFamilyExpr::One,
            DatatypeFamilyExpr::least(DatatypeFamilyExpr::Sum(vec![
                DatatypeFamilyExpr::One,
                DatatypeFamilyExpr::Product(vec![
                    DatatypeFamilyExpr::<&str>::FamilyVar,
                    DatatypeFamilyExpr::Bound(0),
                ]),
            ])),
        ]))
        .unwrap();
        let source = SymbolicFamilyObject::Parameter("source");
        let middle = SymbolicFamilyObject::Parameter("middle");
        let target = SymbolicFamilyObject::Parameter("target");
        let first = symbolic_arrow(source.clone(), middle.clone(), "f");
        let second = symbolic_arrow(middle.clone(), target.clone(), "g");

        let SymbolicFamilyEvidence::Sum(identity) =
            family_map_identity(&SymbolicFamilyBackend, &family, &source).unwrap()
        else {
            panic!("sum evidence");
        };
        assert!(matches!(
            identity[1],
            SymbolicFamilyEvidence::Fixpoint {
                kind: FamilyFixpointKind::Least,
                law: "identity",
                ..
            }
        ));

        let SymbolicFamilyEvidence::Sum(composition) = family_map_composition(
            &SymbolicFamilyBackend,
            &family,
            &source,
            &middle,
            &target,
            &first,
            &second,
        )
        .unwrap() else {
            panic!("sum evidence");
        };
        assert!(matches!(
            composition[1],
            SymbolicFamilyEvidence::Fixpoint {
                law: "composition",
                ..
            }
        ));

        let input_equality = SymbolicFamilyEvidence::Leaf("f=f");
        let SymbolicFamilyEvidence::Sum(congruence) = family_map_congruence(
            &SymbolicFamilyBackend,
            &family,
            &source,
            &middle,
            &first,
            &first,
            &input_equality,
        )
        .unwrap() else {
            panic!("sum evidence");
        };
        assert!(matches!(
            congruence[1],
            SymbolicFamilyEvidence::Fixpoint {
                law: "congruence",
                ..
            }
        ));
    }
}
