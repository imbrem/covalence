//! Host combinators for the **relational** capability: every interpretation found is
//! enumerated and retained.
//!
//! # There is no diagnostic here, and there never will be
//!
//! A relation has no notion of "the alternative failed", only of what it enumerated, and an
//! empty vector proves no negative fact. Granting this capability a diagnostic would hand it
//! exactly the material ordered choice needs and start the slide toward collapse. The
//! accepted cost is real and is stated plainly: a CFG backend whose own interface carries a
//! non-match diagnostic loses it when read through this capability.
//!
//! # Union is not ordered choice
//!
//! [`Union`] evaluates **both** arms and concatenates, with no early return anywhere. That
//! line-by-line difference from `partial::OrderedChoice` — which returns the moment its first
//! alternative matches — is the operational content of the distinction. Their law tables
//! differ accordingly: union is commutative up to permutation and left-distributes over
//! bind, and is **not** idempotent (`union(p, p)` has twice the results, because this is a
//! free multiset union and deduplicating inside the evaluator would destroy exactly the
//! ambiguity retention this capability exists to provide).
//!
//! [`Bind`] here continues *every* head result, where `partial::Bind` continues the single
//! one it found and never retries. The two binds cannot share an implementation, and the
//! `Clone` bounds below are the visible evidence: one head witness feeds many continuation
//! results.
//!
//! # How result limits reach the inner nodes
//!
//! [`RelationalPrefixParser::parse_prefixes`] has no context parameter, so limits cannot be
//! passed down through it. Rather than store a bound on each combinator node — which would
//! make one association of a union trip a limit the other does not, turning associativity
//! into a resource artifact — the combinators here implement [`BoundedRelational`], which
//! threads a [`RelationalCtx`] explicitly. A single [`RelationalEvaluation`] wrapper at the
//! outside holds the caller's [`RelationalLimits`], creates the context, and is the only
//! thing in this module that implements [`RelationalPrefixParser`].

use core::marker::PhantomData;

use covalence_parsing_api::{PrefixInterpretation, Span};

use crate::budget::{CombinatorLimit, CombinatorResource, RelationalLimits};
use crate::host::cursor::{CombinatorError, CursorViolation, SourceExtent, check_step, join};
use crate::host::witness::{SeqWitness, UnionWitness};
use crate::host::{Marker, PrefixEnumeration, RelationalPrefixParser};

// TODO(cov:lang.combinator-parsing.host-relational-limit-threading, major): RelationalLimits
// reach host::relational::{Union, Bind} through the outer RelationalEvaluation wrapper
// because RelationalPrefixParser has no context parameter; the BoundedRelational seam below
// is how inner nodes see them. Revisit if a foreign leaf ever needs to be bounded from the
// inside rather than charged for what it already produced.

// PERF(cov:lang.combinator-parsing.host-relational-sharing, major): No derivation sharing in
// the host encoding either. Ap and Bind clone one head value or witness per continuation
// result; the result limits are the only defence and truncation is always reported as an
// error rather than silently applied. Distinct from the syntax encoding's
// relational-sharing, which has its own value universe to fix.

/// Per-evaluation relational state.
///
/// `produced` is a **per-evaluation** counter charged on every result pushed anywhere in the
/// tree, not a per-node one. That is what keeps the global bound independent of how a union
/// is associated.
#[derive(Clone, Copy, Debug)]
pub struct RelationalCtx {
    limits: RelationalLimits,
    produced: usize,
}

impl RelationalCtx {
    /// Start a fresh evaluation under `limits`.
    pub const fn new(limits: RelationalLimits) -> Self {
        Self {
            limits,
            produced: 0,
        }
    }

    /// The limits this evaluation is running under.
    pub const fn limits(&self) -> RelationalLimits {
        self.limits
    }

    /// Results charged so far in this evaluation.
    pub const fn produced(&self) -> usize {
        self.produced
    }

    /// Charge one result about to be pushed into a node whose vector currently holds
    /// `node_results` entries.
    ///
    /// Checked **before** the push, never after: draining both arms of a union and then
    /// asserting a bound is not a bound, it is a post-hoc assertion an adversarial grammar
    /// has already defeated.
    pub fn admit(&mut self, node_results: usize) -> Result<(), CombinatorLimit> {
        if node_results >= self.limits.max_results_per_node {
            return Err(CombinatorLimit::new(
                CombinatorResource::ResultsPerNode,
                self.limits.max_results_per_node,
            ));
        }
        if self.produced >= self.limits.max_results {
            return Err(CombinatorLimit::new(
                CombinatorResource::Results,
                self.limits.max_results,
            ));
        }
        self.produced += 1;
        Ok(())
    }
}

/// A relational combinator that can see the evaluation's result limits.
///
/// This is the seam that makes limits reach inner nodes without any node storing a bound.
/// It is deliberately *not* [`RelationalPrefixParser`]: an unbounded entry point on these
/// combinators would let a caller sidestep the limits entirely. The only bridge is
/// [`RelationalEvaluation`].
pub trait BoundedRelational {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Error;

    fn parse_prefixes_within(
        &self,
        source: &Self::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> PrefixEnumeration<Self::Value, Self::Witness, Self::Error>;
}

/// The single bridge from a bounded combinator expression to the relational trait.
///
/// The caller's limits live here and nowhere else. Reassociating the expression inside does
/// not move a bound from one node to another.
pub struct RelationalEvaluation<P> {
    pub parser: P,
    pub limits: RelationalLimits,
}

impl<P> RelationalEvaluation<P> {
    /// Bound `parser` by `limits`.
    pub const fn new(parser: P, limits: RelationalLimits) -> Self {
        Self { parser, limits }
    }
}

impl<P: BoundedRelational> RelationalPrefixParser for RelationalEvaluation<P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefixes(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixEnumeration<P::Value, P::Witness, P::Error> {
        let mut ctx = RelationalCtx::new(self.limits);
        self.parser.parse_prefixes_within(source, start, &mut ctx)
    }
}

/// Lift an existing relational parser into a bounded expression as a leaf.
///
/// A foreign leaf enumerates on its own terms and cannot be bounded from the inside, so what
/// this does is *charge* for what the leaf produced. That is an honest weaker guarantee than
/// bounding the leaf, and it is why the marker above stays open.
pub struct Leaf<P>(pub P);

impl<P, E> BoundedRelational for Leaf<P>
where
    P: RelationalPrefixParser<Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Error = CombinatorError<E>;

    fn parse_prefixes_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<P::Value, P::Witness>>, CombinatorError<E>> {
        let results = self.0.parse_prefixes(source, start)?;
        for index in 0..results.len() {
            ctx.admit(index).map_err(CombinatorError::Limit)?;
        }
        Ok(results)
    }
}

/// Consumes nothing and enumerates exactly one interpretation.
pub struct Pure<S: ?Sized, F, E> {
    make: F,
    marker: Marker<S, E>,
}

/// Construct a [`Pure`].
pub fn pure<S: ?Sized, F, E>(make: F) -> Pure<S, F, E> {
    Pure {
        make,
        marker: PhantomData,
    }
}

impl<S: ?Sized, F, V, W, E> BoundedRelational for Pure<S, F, E>
where
    F: Fn() -> (V, W),
{
    type Source = S;
    type Value = V;
    type Witness = W;
    type Error = CombinatorError<E>;

    fn parse_prefixes_within(
        &self,
        _source: &S,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<V, W>>, CombinatorError<E>> {
        ctx.admit(0).map_err(CombinatorError::Limit)?;
        let (value, witness) = (self.make)();
        Ok(vec![PrefixInterpretation {
            value,
            witness,
            consumed: Span { start, end: start },
            remainder: start,
        }])
    }
}

/// The unit of [`Union`]: enumerates nothing, anywhere.
///
/// This is **not** `partial::Fail`. It carries no diagnostic, because there is nothing here
/// for a diagnostic to be about: an empty enumeration is not a claim that nothing matches.
pub struct Void<S: ?Sized, V, W, E> {
    marker: Marker<S, (V, W, E)>,
}

/// Construct a [`Void`].
pub fn void<S: ?Sized, V, W, E>() -> Void<S, V, W, E> {
    Void {
        marker: PhantomData,
    }
}

impl<S: ?Sized, V, W, E> BoundedRelational for Void<S, V, W, E> {
    type Source = S;
    type Value = V;
    type Witness = W;
    type Error = CombinatorError<E>;

    fn parse_prefixes_within(
        &self,
        _source: &S,
        _start: usize,
        _ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<V, W>>, CombinatorError<E>> {
        Ok(Vec::new())
    }
}

/// Borrowed reuse. The orphan rule forbids an impl on `&P` from this crate.
pub struct Ref<'p, P: ?Sized>(pub &'p P);

impl<P: BoundedRelational + ?Sized> BoundedRelational for Ref<'_, P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefixes_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> PrefixEnumeration<P::Value, P::Witness, P::Error> {
        self.0.parse_prefixes_within(source, start, ctx)
    }
}

/// Type erasure over the bounded seam.
pub struct DynRelational<'p, S: ?Sized, V, W, E>(
    pub Box<dyn BoundedRelational<Source = S, Value = V, Witness = W, Error = E> + 'p>,
);

impl<'p, S: ?Sized, V, W, E> DynRelational<'p, S, V, W, E> {
    /// Erase a concrete bounded combinator.
    pub fn new<P>(parser: P) -> Self
    where
        P: BoundedRelational<Source = S, Value = V, Witness = W, Error = E> + 'p,
    {
        Self(Box::new(parser))
    }
}

impl<S: ?Sized, V, W, E> BoundedRelational for DynRelational<'_, S, V, W, E> {
    type Source = S;
    type Value = V;
    type Witness = W;
    type Error = E;

    fn parse_prefixes_within(
        &self,
        source: &S,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<V, W>>, E> {
        self.0.parse_prefixes_within(source, start, ctx)
    }
}

/// Value mapping over every enumerated result.
pub struct Map<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, B> BoundedRelational for Map<P, F>
where
    P: BoundedRelational,
    F: Fn(P::Value) -> B,
{
    type Source = P::Source;
    type Value = B;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefixes_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<B, P::Witness>>, P::Error> {
        // Mapping creates no new results, so it charges nothing: it rewrites the vector it
        // was handed in place.
        Ok(self
            .parser
            .parse_prefixes_within(source, start, ctx)?
            .into_iter()
            .map(|matched| PrefixInterpretation {
                value: (self.function)(matched.value),
                witness: matched.witness,
                consumed: matched.consumed,
                remainder: matched.remainder,
            })
            .collect())
    }
}

/// Value-independent sequencing with application, over the full cross product.
///
/// `P::Value: Clone` and `P::Witness: Clone` because one function result is consumed once
/// per argument result. Those bounds are not incidental — they are the type-level trace of
/// the fact that this operator enumerates rather than commits.
pub struct Ap<P, Q> {
    pub functions: P,
    pub arguments: Q,
}

impl<P, Q, B, E> BoundedRelational for Ap<P, Q>
where
    P: BoundedRelational<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    P::Value: Fn(Q::Value) -> B + Clone,
    P::Witness: Clone,
    Q: BoundedRelational<Source = P::Source, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = B;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Error = CombinatorError<E>;

    fn parse_prefixes_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<B, Self::Witness>>, CombinatorError<E>> {
        let source_len = source.extent();
        let functions = self.functions.parse_prefixes_within(source, start, ctx)?;
        let mut results = Vec::new();
        for function in functions {
            let function =
                check_step(start, source_len, function).map_err(CombinatorError::Cursor)?;
            let split = function.remainder;
            let arguments = self.arguments.parse_prefixes_within(source, split, ctx)?;
            for argument in arguments {
                let argument =
                    check_step(split, source_len, argument).map_err(CombinatorError::Cursor)?;
                let consumed = join(function.consumed, argument.consumed).ok_or_else(|| {
                    CombinatorError::Cursor(CursorViolation {
                        invoked_at: start,
                        consumed: argument.consumed,
                        remainder: argument.remainder,
                        source_len,
                    })
                })?;
                ctx.admit(results.len()).map_err(CombinatorError::Limit)?;
                results.push(PrefixInterpretation {
                    value: (function.value.clone())(argument.value),
                    witness: SeqWitness {
                        first: function.witness.clone(),
                        second: argument.witness,
                        split,
                    },
                    consumed,
                    remainder: argument.remainder,
                });
            }
        }
        Ok(results)
    }
}

/// Value-dependent sequencing that continues **every** head result.
///
/// `P::Witness: Clone` because one head witness feeds many continuation results; a consumer
/// therefore cannot tell from the witness type alone whether that evidence is exclusive or
/// shared. This is the sharpest operational difference from `partial::Bind`, which continues
/// the single result it found and never retries its head.
pub struct Bind<P, F> {
    pub parser: P,
    pub continuation: F,
}

impl<P, F, Q, E> BoundedRelational for Bind<P, F>
where
    P: BoundedRelational<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    P::Witness: Clone,
    F: Fn(P::Value) -> Q,
    Q: BoundedRelational<Source = P::Source, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = Q::Value;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Error = CombinatorError<E>;

    fn parse_prefixes_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<Q::Value, Self::Witness>>, CombinatorError<E>> {
        let source_len = source.extent();
        let heads = self.parser.parse_prefixes_within(source, start, ctx)?;
        let mut results = Vec::new();
        for head in heads {
            let head = check_step(start, source_len, head).map_err(CombinatorError::Cursor)?;
            let split = head.remainder;
            let next = (self.continuation)(head.value);
            for tail in next.parse_prefixes_within(source, split, ctx)? {
                let tail = check_step(split, source_len, tail).map_err(CombinatorError::Cursor)?;
                let consumed = join(head.consumed, tail.consumed).ok_or_else(|| {
                    CombinatorError::Cursor(CursorViolation {
                        invoked_at: start,
                        consumed: tail.consumed,
                        remainder: tail.remainder,
                        source_len,
                    })
                })?;
                ctx.admit(results.len()).map_err(CombinatorError::Limit)?;
                results.push(PrefixInterpretation {
                    value: tail.value,
                    witness: SeqWitness {
                        first: head.witness.clone(),
                        second: tail.witness,
                        split,
                    },
                    consumed,
                    remainder: tail.remainder,
                });
            }
        }
        Ok(results)
    }
}

/// Unordered union: **both** arms are evaluated and every result is retained.
///
/// No early return anywhere, and no deduplication. `union(p, p)` therefore enumerates each of
/// `p`'s results twice; that is correct, and collapsing it inside the evaluator would destroy
/// the ambiguity this capability exists to retain. Idempotence holds only relative to a
/// caller-supplied dedup policy applied to the *results*, never inside the operator.
///
/// ```compile_fail,E0277
/// use covalence_parsing_api::PartialPrefixParser;
/// use covalence_combinator_parsing::host::relational::Union;
/// fn assert_partial<P: PartialPrefixParser>(_: P) {}
/// // Relational union is not a partial-capability operator and has no diagnostic channel.
/// fn use_it<P, Q>(union: Union<P, Q>) { assert_partial(union); }
/// ```
pub struct Union<P, Q> {
    pub left: P,
    pub right: Q,
}

impl<P, Q, E> BoundedRelational for Union<P, Q>
where
    P: BoundedRelational<Error = CombinatorError<E>>,
    Q: BoundedRelational<Source = P::Source, Value = P::Value, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = UnionWitness<P::Witness, Q::Witness>;
    type Error = CombinatorError<E>;

    fn parse_prefixes_within(
        &self,
        source: &P::Source,
        start: usize,
        ctx: &mut RelationalCtx,
    ) -> Result<Vec<PrefixInterpretation<P::Value, Self::Witness>>, CombinatorError<E>> {
        let mut results = Vec::new();
        // Both arms are evaluated. There is no early return: that is the whole difference
        // from ordered choice.
        for matched in self.left.parse_prefixes_within(source, start, ctx)? {
            ctx.admit(results.len()).map_err(CombinatorError::Limit)?;
            results.push(PrefixInterpretation {
                value: matched.value,
                witness: UnionWitness::Left(matched.witness),
                consumed: matched.consumed,
                remainder: matched.remainder,
            });
        }
        for matched in self.right.parse_prefixes_within(source, start, ctx)? {
            ctx.admit(results.len()).map_err(CombinatorError::Limit)?;
            results.push(PrefixInterpretation {
                value: matched.value,
                witness: UnionWitness::Right(matched.witness),
                consumed: matched.consumed,
                remainder: matched.remainder,
            });
        }
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Never;

    const GENEROUS: RelationalLimits = RelationalLimits::new(64, 64);

    /// Matches a byte, and additionally offers a zero-width interpretation, so that a single
    /// leaf is genuinely ambiguous at one offset. The relational corpus needs at least one
    /// such parser or every law about union degenerates.
    struct AmbiguousByte(u8);

    impl BoundedRelational for AmbiguousByte {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Error = CombinatorError<Never>;

        fn parse_prefixes_within(
            &self,
            source: &[u8],
            start: usize,
            ctx: &mut RelationalCtx,
        ) -> Result<Vec<PrefixInterpretation<u8, ()>>, CombinatorError<Never>> {
            let mut results = Vec::new();
            ctx.admit(results.len()).map_err(CombinatorError::Limit)?;
            results.push(PrefixInterpretation {
                value: 0,
                witness: (),
                consumed: Span { start, end: start },
                remainder: start,
            });
            if source.get(start) == Some(&self.0) {
                ctx.admit(results.len()).map_err(CombinatorError::Limit)?;
                results.push(PrefixInterpretation {
                    value: self.0,
                    witness: (),
                    consumed: Span {
                        start,
                        end: start + 1,
                    },
                    remainder: start + 1,
                });
            }
            Ok(results)
        }
    }

    fn evaluate<P: BoundedRelational>(
        parser: P,
        source: &P::Source,
        limits: RelationalLimits,
    ) -> PrefixEnumeration<P::Value, P::Witness, P::Error> {
        RelationalEvaluation::new(parser, limits).parse_prefixes(source, 0)
    }

    #[test]
    fn a_single_leaf_can_be_genuinely_ambiguous_at_one_offset() {
        let results =
            evaluate(AmbiguousByte(b'a'), b"ab".as_slice(), GENEROUS).expect("no failure");
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn union_evaluates_both_arms_and_retains_every_result() {
        let results = evaluate(
            Union {
                left: AmbiguousByte(b'a'),
                right: AmbiguousByte(b'a'),
            },
            b"ab".as_slice(),
            GENEROUS,
        )
        .expect("no failure");
        // Both arms ran; nothing was deduplicated.
        assert_eq!(results.len(), 4);
        assert!(matches!(results[0].witness, UnionWitness::Left(())));
        assert!(matches!(results[3].witness, UnionWitness::Right(())));
    }

    /// Union is a free multiset union, so it is **not** idempotent. Pinning this stops
    /// anyone from "fixing" the count by deduplicating inside the evaluator.
    #[test]
    fn union_is_not_idempotent() {
        let single = evaluate(AmbiguousByte(b'a'), b"ab".as_slice(), GENEROUS).expect("no failure");
        let doubled = evaluate(
            Union {
                left: AmbiguousByte(b'a'),
                right: AmbiguousByte(b'a'),
            },
            b"ab".as_slice(),
            GENEROUS,
        )
        .expect("no failure");
        assert_eq!(doubled.len(), 2 * single.len());
    }

    #[test]
    fn bind_continues_every_head_result() {
        let parser = Bind {
            parser: AmbiguousByte(b'a'),
            continuation: |_| AmbiguousByte(b'b'),
        };
        let results = evaluate(parser, b"ab".as_slice(), GENEROUS).expect("no failure");
        // Head yields two results (empty at 0, and 'a' ending at 1). The continuation yields
        // one at offset 0 (only the empty interpretation, since source[0] != 'b') and two at
        // offset 1. Every head result is continued; none is discarded.
        assert_eq!(results.len(), 3);
    }

    /// The sharpest separating law: union left-distributes over bind. The ordered analogue
    /// fails, because ordered choice commits to its first alternative's match.
    #[test]
    fn union_left_distributes_over_bind() {
        let distributed = evaluate(
            Union {
                left: Bind {
                    parser: AmbiguousByte(b'a'),
                    continuation: |_| AmbiguousByte(b'b'),
                },
                right: Bind {
                    parser: AmbiguousByte(b'b'),
                    continuation: |_| AmbiguousByte(b'b'),
                },
            },
            b"ab".as_slice(),
            GENEROUS,
        )
        .expect("no failure");
        let factored = evaluate(
            Bind {
                parser: Union {
                    left: AmbiguousByte(b'a'),
                    right: AmbiguousByte(b'b'),
                },
                continuation: |_| AmbiguousByte(b'b'),
            },
            b"ab".as_slice(),
            GENEROUS,
        )
        .expect("no failure");
        // Compared on extents only: the two sides record different witness types by
        // construction, and no law in this crate compares witnesses.
        fn extents<V, W>(results: &[PrefixInterpretation<V, W>]) -> Vec<(Span, usize)> {
            results
                .iter()
                .map(|matched| (matched.consumed, matched.remainder))
                .collect()
        }
        assert_eq!(extents(&distributed), extents(&factored));
    }

    #[test]
    fn void_enumerates_nothing_and_is_a_unit_for_union() {
        let alone = evaluate(void::<[u8], u8, (), Never>(), b"ab".as_slice(), GENEROUS)
            .expect("no failure");
        assert!(alone.is_empty());

        let with_unit = evaluate(
            Union {
                left: AmbiguousByte(b'a'),
                right: Map {
                    parser: void::<[u8], u8, (), Never>(),
                    function: |value: u8| value,
                },
            },
            b"ab".as_slice(),
            GENEROUS,
        )
        .expect("no failure");
        let alone_again =
            evaluate(AmbiguousByte(b'a'), b"ab".as_slice(), GENEROUS).expect("no failure");
        assert_eq!(with_unit.len(), alone_again.len());
    }

    #[test]
    fn the_global_result_bound_is_observable() {
        let error = evaluate(
            Union {
                left: AmbiguousByte(b'a'),
                right: AmbiguousByte(b'a'),
            },
            b"ab".as_slice(),
            RelationalLimits::new(3, 64),
        )
        .expect_err("the global bound must trip");
        assert_eq!(
            error,
            CombinatorError::Limit(CombinatorLimit::new(CombinatorResource::Results, 3))
        );
    }

    #[test]
    fn the_per_node_result_bound_is_observable() {
        let error = evaluate(
            Union {
                left: AmbiguousByte(b'a'),
                right: AmbiguousByte(b'a'),
            },
            b"ab".as_slice(),
            RelationalLimits::new(1024, 2),
        )
        .expect_err("the per-node bound must trip");
        assert_eq!(
            error,
            CombinatorError::Limit(CombinatorLimit::new(CombinatorResource::ResultsPerNode, 2))
        );
    }

    /// The global counter is per-evaluation, not per-node, so it does not care how the union
    /// was associated. This is the structural fix for association-dependent budgets.
    #[test]
    fn the_global_bound_does_not_depend_on_association() {
        let left_nested = evaluate(
            Union {
                left: Union {
                    left: AmbiguousByte(b'a'),
                    right: AmbiguousByte(b'a'),
                },
                right: AmbiguousByte(b'a'),
            },
            b"ab".as_slice(),
            RelationalLimits::new(5, 1024),
        );
        let right_nested = evaluate(
            Union {
                left: AmbiguousByte(b'a'),
                right: Union {
                    left: AmbiguousByte(b'a'),
                    right: AmbiguousByte(b'a'),
                },
            },
            b"ab".as_slice(),
            RelationalLimits::new(5, 1024),
        );
        assert!(left_nested.is_err());
        assert!(right_nested.is_err());
        assert_eq!(left_nested.unwrap_err(), right_nested.unwrap_err());
    }
}
