//! A small reference backend for the coinductive stream shape `A × X`.
//!
//! This module is computational rather than trusted. It makes observation,
//! coalgebraic unfold, and stepwise bisimulation concrete enough to exercise
//! the coinductive API. Checking a finite prefix does **not** manufacture a
//! theorem that two infinite streams are equal.

use std::{fmt, rc::Rc};

use crate::{
    FieldSpec, FixpointSpec, FunctorExpr, PolynomialSpec, Position, StructuralPolynomial,
    Validated, VariantCase,
};

/// One observation of the stream functor `A × X`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamLayer<A, X> {
    /// The current element.
    pub head: A,
    /// The remaining stream.
    pub tail: X,
}

/// The minimal consumer capability for a stream: expose one `A × X` layer.
pub trait StreamObservation {
    /// Element type.
    type Item;
    /// Type of the observed continuation.
    type Tail;

    /// Observe one functor layer.
    fn observe(&self) -> StreamLayer<Self::Item, Self::Tail>;
}

/// The checked polynomial declaration for streams of `A`.
pub fn stream_fixpoint<P: Clone>(element: P) -> Validated<FixpointSpec<P>> {
    Validated::try_from(FixpointSpec::new(
        "stream",
        PolynomialSpec::new(
            "stream-f",
            vec![VariantCase::new(
                "next",
                vec![
                    FieldSpec::new("head", Position::Param(element)),
                    FieldSpec::new("tail", Position::Var),
                ],
            )],
        ),
    ))
    .expect("the fixed stream declaration is valid")
}

/// The structural expression `A × X` used by the reference backend.
pub fn stream_functor<P>(element: P) -> StructuralPolynomial<P> {
    StructuralPolynomial::try_from(FunctorExpr::Product(vec![
        FunctorExpr::Param(element),
        FunctorExpr::Var,
    ]))
    .expect("the stream functor has no composition")
}

/// A lazily observed reference stream.
///
/// Calling [`observe`](Self::observe) may run arbitrary Rust code supplied by
/// the coalgebra. This type demonstrates an API shape; it is not a productivity
/// certificate and belongs to no trusted base.
pub struct ReferenceStream<A> {
    observe: Rc<dyn Fn() -> StreamLayer<A, ReferenceStream<A>>>,
}

impl<A> Clone for ReferenceStream<A> {
    fn clone(&self) -> Self {
        Self {
            observe: Rc::clone(&self.observe),
        }
    }
}

impl<A> fmt::Debug for ReferenceStream<A> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ReferenceStream(..)")
    }
}

impl<A: 'static> StreamObservation for ReferenceStream<A> {
    type Item = A;
    type Tail = Self;

    fn observe(&self) -> StreamLayer<Self::Item, Self::Tail> {
        (self.observe)()
    }
}

impl<A: 'static> ReferenceStream<A> {
    /// Build a stream by repeatedly applying `coalgebra : S → A × S`.
    pub fn unfold<S, F>(seed: S, coalgebra: F) -> Self
    where
        S: Clone + 'static,
        F: Fn(S) -> StreamLayer<A, S> + 'static,
    {
        Self::unfold_shared(seed, Rc::new(coalgebra))
    }

    fn unfold_shared<S, F>(seed: S, coalgebra: Rc<F>) -> Self
    where
        S: Clone + 'static,
        F: Fn(S) -> StreamLayer<A, S> + 'static,
    {
        Self {
            observe: Rc::new(move || {
                let layer = coalgebra(seed.clone());
                StreamLayer {
                    head: layer.head,
                    tail: Self::unfold_shared(layer.tail, Rc::clone(&coalgebra)),
                }
            }),
        }
    }

    /// Collect a finite observational prefix.
    ///
    /// This is useful for tests and rendering, but its result is never evidence
    /// about the unobserved suffix.
    pub fn prefix(&self, count: usize) -> Vec<A> {
        let mut stream = self.clone();
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            let layer = stream.observe();
            values.push(layer.head);
            stream = layer.tail;
        }
        values
    }
}

/// The untrusted computational backend used by examples and conformance tests.
#[derive(Clone, Copy, Debug, Default)]
pub struct ReferenceStreamBackend;

impl ReferenceStreamBackend {
    /// Realize a stream from a Rust coalgebra.
    pub fn unfold<A: 'static, S, F>(&self, seed: S, coalgebra: F) -> ReferenceStream<A>
    where
        S: Clone + 'static,
        F: Fn(S) -> StreamLayer<A, S> + 'static,
    {
        ReferenceStream::unfold(seed, coalgebra)
    }
}

/// A candidate bisimulation and a checker for one pair of observed heads.
///
/// It can be advanced indefinitely one observation at a time. Each successful
/// step carries only the caller-defined evidence returned for that step.
#[derive(Clone)]
pub struct StreamBisimulation<A, E> {
    left: ReferenceStream<A>,
    right: ReferenceStream<A>,
    relate_heads: Rc<dyn Fn(&A, &A) -> Option<E>>,
}

impl<A: 'static, E> StreamBisimulation<A, E> {
    /// Propose a bisimulation relation between two streams.
    pub fn new(
        left: ReferenceStream<A>,
        right: ReferenceStream<A>,
        relate_heads: impl Fn(&A, &A) -> Option<E> + 'static,
    ) -> Self {
        Self {
            left,
            right,
            relate_heads: Rc::new(relate_heads),
        }
    }

    /// Check and expose one bisimulation step.
    pub fn observe(self) -> Option<StreamBisimulationStep<A, E>> {
        let left = self.left.observe();
        let right = self.right.observe();
        let evidence = (self.relate_heads)(&left.head, &right.head)?;
        Some(StreamBisimulationStep {
            left_head: left.head,
            right_head: right.head,
            evidence,
            tails: Self {
                left: left.tail,
                right: right.tail,
                relate_heads: self.relate_heads,
            },
        })
    }
}

/// Evidence from one checked observation of a bisimulation candidate.
pub struct StreamBisimulationStep<A, E> {
    /// Left observed head.
    pub left_head: A,
    /// Right observed head.
    pub right_head: A,
    /// Caller-defined evidence that the heads are related.
    pub evidence: E,
    /// Candidate relation between the observed tails.
    pub tails: StreamBisimulation<A, E>,
}

/// Check exactly `count` observations of a bisimulation candidate.
///
/// Success means only that these steps passed. The returned evidence is not a
/// proof of equality of the infinite streams.
pub fn check_bisimulation_prefix<A: 'static, E>(
    mut candidate: StreamBisimulation<A, E>,
    count: usize,
) -> Option<Vec<E>> {
    let mut evidence = Vec::with_capacity(count);
    for _ in 0..count {
        let step = candidate.observe()?;
        evidence.push(step.evidence);
        candidate = step.tails;
    }
    Some(evidence)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stream_shape_is_the_structural_polynomial_a_times_x() {
        assert_eq!(
            stream_functor("a").expression(),
            &FunctorExpr::Product(vec![FunctorExpr::Param("a"), FunctorExpr::Var])
        );
        assert_eq!(stream_fixpoint("a").functor.variants.len(), 1);
    }

    #[test]
    fn unfold_observes_a_coalgebra_one_layer_at_a_time() {
        let naturals = ReferenceStreamBackend.unfold(0_u64, |n| StreamLayer {
            head: n,
            tail: n + 1,
        });
        assert_eq!(naturals.prefix(5), vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn bisimulation_checker_returns_only_per_step_evidence() {
        let left = ReferenceStream::unfold(0_u64, |n| StreamLayer {
            head: n,
            tail: n + 1,
        });
        let right = ReferenceStream::unfold((0_u64, ()), |(n, ())| StreamLayer {
            head: n,
            tail: (n + 1, ()),
        });
        let candidate = StreamBisimulation::new(left, right, |a, b| (a == b).then_some((*a, *b)));
        assert_eq!(
            check_bisimulation_prefix(candidate, 4),
            Some(vec![(0, 0), (1, 1), (2, 2), (3, 3)])
        );
    }

    #[test]
    fn bisimulation_checker_rejects_the_first_bad_observation() {
        let left = ReferenceStream::unfold(0_u64, |n| StreamLayer {
            head: n,
            tail: n + 1,
        });
        let right = ReferenceStream::unfold(1_u64, |n| StreamLayer {
            head: n,
            tail: n + 1,
        });
        let candidate = StreamBisimulation::new(left, right, |a, b| (a == b).then_some(()));
        assert!(check_bisimulation_prefix(candidate, 1).is_none());
    }
}
