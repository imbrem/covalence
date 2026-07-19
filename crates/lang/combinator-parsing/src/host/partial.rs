//! Host combinators for the **partial** capability: zero or one interpretation, with a
//! caller-shaped diagnostic on the zero case.
//!
//! This is the only one of the three modules that has a choice operator, and the reason is
//! structural rather than stylistic: stating ordered choice needs a non-match channel *and* a
//! diagnostic to carry forward from the declined alternative. The total capability has
//! neither, and the relational capability has neither and never will.
//!
//! # Diagnostics are caller policy
//!
//! `Diagnostic` is an associated type all the way down, and [`OrderedChoice`] takes a
//! caller-supplied `merge` rather than fixing a shape. A caller who wants a structural
//! diagnostic gets one; a caller who wants the flat `{ offset, kind }` of the syntax
//! encoding gets that too. This is the whole reason the host encoding is kept alongside the
//! syntax encoding, so nothing here may quietly fix a diagnostic shape.
//!
//! # Ordered choice is a monoid only in the diagnostic-forgetting quotient
//!
//! `oc(oc(p, q), r)` and `oc(p, oc(q, r))` agree on values and extents, but fold diagnostics
//! as `merge(merge(dp, dq), dr)` against `merge(dp, merge(dq, dr))`. Those are equal exactly
//! when the caller's `merge` is itself associative — which this crate cannot check and does
//! not assume. "Ordered choice is a monoid" is therefore true only after forgetting
//! diagnostics, or under an associative `merge`. Stated flat, it is false.
//!
//! # Backtracking enters only through ordered choice
//!
//! [`Bind`] does not retry its first parser when the continuation declines, and
//! [`OrderedChoice`] does not evaluate its second alternative when the first matched. Both
//! are semantic commitments, not implementation details, and both are what separate this
//! capability from [`relational`](crate::host::relational).

use core::marker::PhantomData;

use covalence_parsing_api::{
    ParseAttempt, PartialPrefixParser, PrefixInterpretation, PrefixParseResult, Span,
};

use crate::host::Marker;
use crate::host::cursor::{CombinatorError, CursorViolation, SourceExtent, check_step, join};
use crate::host::witness::{ChoiceWitness, SeqWitness};

// FIXME(cov:lang.combinator-parsing.host-recursion-unbounded, major): A knot tied through
// `Lazy` (or through any hand-written `parse_prefix` impl) is bounded only by the native
// stack, so a left-recursive expression built from *this* module still overflows.
// `host::recursion` is the bounded route and returns a Depth limit instead, but `Lazy`
// cannot be routed through it: `parse_prefix` takes no evaluator state, and the only other
// channels surviving a call into an opaque sub-parser are per-node storage and the source
// carrier, both rejected in that module's header. Closing this needs either an
// evaluator-state parameter in A0015 or the removal of `Lazy` in favour of
// `recursion::Recurse`.

/// Consumes nothing and always yields the same interpretation.
///
/// The **factory is forced, not stylistic.** `parse_prefix` takes `&self`, so a stored value
/// would need `Clone`; but the applicative laws need function-typed values, and
/// `Box<dyn Fn>` implements `Fn` (as [`Ap`] requires) yet not `Clone`, while `Rc<dyn Fn>` is
/// `Clone` yet does not implement `Fn`. A `Fn() -> (V, W)` factory dissolves the dilemma by
/// constructing a fresh value per call. Do not "simplify" this back to a stored value.
pub struct Pure<S: ?Sized, F, D, E> {
    make: F,
    marker: Marker<S, (D, E)>,
}

/// Construct a [`Pure`]. The source, diagnostic, and error types are free and normally
/// pinned by the expression this is embedded in.
pub fn pure<S: ?Sized, F, D, E>(make: F) -> Pure<S, F, D, E> {
    Pure {
        make,
        marker: PhantomData,
    }
}

impl<S: ?Sized, F, V, W, D, E> PartialPrefixParser for Pure<S, F, D, E>
where
    F: Fn() -> (V, W),
{
    type Source = S;
    type Value = V;
    type Witness = W;
    type Diagnostic = D;
    type Error = E;

    fn parse_prefix(&self, _source: &S, start: usize) -> PrefixParseResult<V, W, D, E> {
        let (value, witness) = (self.make)();
        Ok(ParseAttempt::Match(PrefixInterpretation {
            value,
            witness,
            consumed: Span { start, end: start },
            remainder: start,
        }))
    }
}

/// The unit of ordered choice: never matches, always reports `diagnostic`.
pub struct Fail<S: ?Sized, V, W, D, E> {
    diagnostic: D,
    marker: Marker<S, (V, W, E)>,
}

/// Construct a [`Fail`] reporting `diagnostic` at every offset.
pub fn fail<S: ?Sized, V, W, D, E>(diagnostic: D) -> Fail<S, V, W, D, E> {
    Fail {
        diagnostic,
        marker: PhantomData,
    }
}

impl<S: ?Sized, V, W, D: Clone, E> PartialPrefixParser for Fail<S, V, W, D, E> {
    type Source = S;
    type Value = V;
    type Witness = W;
    type Diagnostic = D;
    type Error = E;

    fn parse_prefix(&self, _source: &S, _start: usize) -> PrefixParseResult<V, W, D, E> {
        Ok(ParseAttempt::NoMatch(self.diagnostic.clone()))
    }
}

/// Borrowed reuse of a parser.
///
/// The orphan rule forbids `impl PartialPrefixParser for &P` in this crate — the trait is
/// foreign and the type parameter is uncovered, and `&` being `#[fundamental]` does not
/// help — so reuse goes through this local newtype.
pub struct Ref<'p, P: ?Sized>(pub &'p P);

impl<P: PartialPrefixParser + ?Sized> PartialPrefixParser for Ref<'_, P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = P::Error;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, P::Error> {
        self.0.parse_prefix(source, start)
    }
}

/// Type erasure.
///
/// **Required, not an ergonomic footnote:** `impl PartialPrefixParser for Box<dyn
/// PartialPrefixParser<..>>` is E0117 from this crate, because neither `Box` nor the trait is
/// local. A boxed parser therefore cannot be fed to a combinator without this local
/// forwarding newtype. Every recursion point and every compilation from the syntax encoding
/// returns one.
pub struct DynPartial<'p, S: ?Sized, V, W, D, E>(
    pub  Box<
        dyn PartialPrefixParser<Source = S, Value = V, Witness = W, Diagnostic = D, Error = E> + 'p,
    >,
);

impl<'p, S: ?Sized, V, W, D, E> DynPartial<'p, S, V, W, D, E> {
    /// Erase a concrete parser.
    pub fn new<P>(parser: P) -> Self
    where
        P: PartialPrefixParser<Source = S, Value = V, Witness = W, Diagnostic = D, Error = E> + 'p,
    {
        Self(Box::new(parser))
    }
}

impl<S: ?Sized, V, W, D, E> PartialPrefixParser for DynPartial<'_, S, V, W, D, E> {
    type Source = S;
    type Value = V;
    type Witness = W;
    type Diagnostic = D;
    type Error = E;

    fn parse_prefix(&self, source: &S, start: usize) -> PrefixParseResult<V, W, D, E> {
        self.0.parse_prefix(source, start)
    }
}

/// Recursion, by rebuilding the sub-expression on entry.
///
/// **Unbounded.** This operator ties its knot through `parse_prefix`, which carries no
/// evaluator state, so a left-recursive expression built with it overflows the native stack
/// rather than reporting a bound. For a knot that is bounded, use
/// [`recursion::Recurse`](crate::host::recursion::Recurse), whose expression reports a
/// [`CombinatorResource::Depth`](crate::budget::CombinatorResource::Depth) limit and reaches
/// `PartialPrefixParser` through
/// [`recursion::PartialEvaluation`](crate::host::recursion::PartialEvaluation). This one is
/// kept for knots already known to be productive, where rebuilding is all that is wanted.
pub struct Lazy<F> {
    pub make: F,
}

/// Construct a [`Lazy`].
pub fn lazy<F>(make: F) -> Lazy<F> {
    Lazy { make }
}

// PERF(cov:lang.combinator-parsing.lazy-rebuilds-subtree, minor): host::Lazy rebuilds its
// expression on every entry at every offset, not one allocation per nonterminal. The syntax
// encoding's indexed Rule table is the in-tree answer for grammars that feel this.

impl<F, P> PartialPrefixParser for Lazy<F>
where
    F: Fn() -> P,
    P: PartialPrefixParser,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = P::Error;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, P::Error> {
        (self.make)().parse_prefix(source, start)
    }
}

/// Value mapping.
///
/// Error-transparent: `map` cannot fail, so it does not impose the [`CombinatorError`]
/// convention on its argument. `B` appears only in the where-clause `Fn` binding and still
/// constrains the impl; no `PhantomData<B>` is needed.
pub struct Map<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, B> PartialPrefixParser for Map<P, F>
where
    P: PartialPrefixParser,
    F: Fn(P::Value) -> B,
{
    type Source = P::Source;
    type Value = B;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = P::Error;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<B, P::Witness, P::Diagnostic, P::Error> {
        Ok(match self.parser.parse_prefix(source, start)? {
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch(diagnostic),
            ParseAttempt::Match(matched) => ParseAttempt::Match(PrefixInterpretation {
                value: (self.function)(matched.value),
                witness: matched.witness,
                consumed: matched.consumed,
                remainder: matched.remainder,
            }),
        })
    }
}

/// Value-independent sequencing with application.
///
/// Kept because the applicative laws are stated in terms of it. In Rust the
/// function-carrying parser's `Value` is usually an unnameable closure type, so a `map2`
/// would be the ergonomic primitive and this is mostly a conformance target; expect to need
/// a turbofish at call sites.
pub struct Ap<P, Q> {
    pub functions: P,
    pub arguments: Q,
}

impl<P, Q, B, E> PartialPrefixParser for Ap<P, Q>
where
    P: PartialPrefixParser<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    P::Value: FnOnce(Q::Value) -> B,
    Q: PartialPrefixParser<
            Source = P::Source,
            Diagnostic = P::Diagnostic,
            Error = CombinatorError<E>,
        >,
{
    type Source = P::Source;
    type Value = B;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<B, Self::Witness, P::Diagnostic, CombinatorError<E>> {
        let source_len = source.extent();
        let function = match self.functions.parse_prefix(source, start)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(start, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let split = function.remainder;
        let argument = match self.arguments.parse_prefix(source, split)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(split, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let consumed = join(function.consumed, argument.consumed).ok_or_else(|| {
            CombinatorError::Cursor(CursorViolation {
                invoked_at: start,
                consumed: argument.consumed,
                remainder: argument.remainder,
                source_len,
            })
        })?;
        Ok(ParseAttempt::Match(PrefixInterpretation {
            value: (function.value)(argument.value),
            witness: SeqWitness {
                first: function.witness,
                second: argument.witness,
                split,
            },
            consumed,
            remainder: argument.remainder,
        }))
    }
}

/// Value-dependent sequencing.
///
/// Three load-bearing facts, none hidden:
///
/// 1. `continuation` is invoked on *every* successful first parse; there is no memoization.
/// 2. `Q` is one concrete type per node, so a grammar dispatching to structurally different
///    parsers must unify them through [`DynPartial`] or a caller-defined sum. This is not a
///    recursion limitation — it is intrinsic to bind in Rust.
/// 3. If the continuation does not match, this parser does not match; it does **not** retry
///    the first parser. Backtracking enters only through [`OrderedChoice`]. This is a
///    semantic difference from `relational::Bind`, not an implementation detail.
pub struct Bind<P, F> {
    pub parser: P,
    pub continuation: F,
}

// DEVIATION from the brief (§6.3), minimal and deliberate: `Bind` requires
// `Error = CombinatorError<E>` and `Source: SourceExtent`, where the brief left it
// error-transparent. Sequencing has to join two extents, and with no error channel a
// mis-reported sub-extent could only be papered over by fabricating a span or by panicking.
// A cursor violation is evaluator failure and must be reportable as one.
impl<P, F, Q, E> PartialPrefixParser for Bind<P, F>
where
    P: PartialPrefixParser<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    F: Fn(P::Value) -> Q,
    Q: PartialPrefixParser<
            Source = P::Source,
            Diagnostic = P::Diagnostic,
            Error = CombinatorError<E>,
        >,
{
    type Source = P::Source;
    type Value = Q::Value;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<Q::Value, Self::Witness, P::Diagnostic, CombinatorError<E>> {
        let source_len = source.extent();
        let head = match self.parser.parse_prefix(source, start)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(start, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let split = head.remainder;
        let next = (self.continuation)(head.value);
        // The head is not retried: a partial parser has exactly one result at this offset.
        let tail = match next.parse_prefix(source, split)? {
            ParseAttempt::NoMatch(diagnostic) => return Ok(ParseAttempt::NoMatch(diagnostic)),
            ParseAttempt::Match(matched) => {
                check_step(split, source_len, matched).map_err(CombinatorError::Cursor)?
            }
        };
        let consumed = join(head.consumed, tail.consumed).ok_or_else(|| {
            CombinatorError::Cursor(CursorViolation {
                invoked_at: start,
                consumed: tail.consumed,
                remainder: tail.remainder,
                source_len,
            })
        })?;
        Ok(ParseAttempt::Match(PrefixInterpretation {
            value: tail.value,
            witness: SeqWitness {
                first: head.witness,
                second: tail.witness,
                split,
            },
            consumed,
            remainder: tail.remainder,
        }))
    }
}

/// Ordered, committing choice.
///
/// The second alternative is explored only when the first produced no match at this offset,
/// and the witness records that. `merge` is caller policy: this layer cannot know whether the
/// reported diagnostic should be the farthest failure, the last failure, or a structured
/// combination.
///
/// This operator exists only in this module. It has no analogue in
/// [`relational`](crate::host::relational) — `Union` is a different operator with a different
/// law table, not a spelling of this one — and no analogue in [`total`](crate::host::total),
/// where a second alternative could never be consulted.
///
/// Associativity folds diagnostics differently on the two sides, so ordered choice is a
/// monoid only in the diagnostic-forgetting quotient; see the module doc.
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::host::RelationalPrefixParser;
/// use covalence_combinator_parsing::host::partial::OrderedChoice;
/// fn assert_relational<P: RelationalPrefixParser>(_: P) {}
/// // Ordered choice is a partial-capability operator and implements no relational trait.
/// fn use_it<P, Q, M>(choice: OrderedChoice<P, Q, M>) { assert_relational(choice); }
/// ```
pub struct OrderedChoice<P, Q, M> {
    pub first: P,
    pub second: Q,
    pub merge: M,
}

impl<P, Q, M, E> PartialPrefixParser for OrderedChoice<P, Q, M>
where
    P: PartialPrefixParser<Error = CombinatorError<E>>,
    Q: PartialPrefixParser<
            Source = P::Source,
            Value = P::Value,
            Diagnostic = P::Diagnostic,
            Error = CombinatorError<E>,
        >,
    M: Fn(P::Diagnostic, P::Diagnostic) -> P::Diagnostic,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = ChoiceWitness<P::Witness, Q::Witness, P::Diagnostic>;
    type Diagnostic = P::Diagnostic;
    type Error = CombinatorError<E>;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, Self::Witness, P::Diagnostic, CombinatorError<E>> {
        // The early return is the operational content of "committing": on a first match the
        // second alternative is never evaluated at all.
        let first_diagnostic = match self.first.parse_prefix(source, start)? {
            ParseAttempt::Match(matched) => {
                return Ok(ParseAttempt::Match(PrefixInterpretation {
                    value: matched.value,
                    witness: ChoiceWitness::First(matched.witness),
                    consumed: matched.consumed,
                    remainder: matched.remainder,
                }));
            }
            ParseAttempt::NoMatch(diagnostic) => diagnostic,
        };
        // `first_diagnostic` moves into exactly one of the two arms below, so no `Clone`
        // bound on the diagnostic is needed.
        Ok(match self.second.parse_prefix(source, start)? {
            ParseAttempt::Match(matched) => ParseAttempt::Match(PrefixInterpretation {
                value: matched.value,
                witness: ChoiceWitness::Second {
                    first_diagnostic,
                    witness: matched.witness,
                },
                consumed: matched.consumed,
                remainder: matched.remainder,
            }),
            ParseAttempt::NoMatch(second_diagnostic) => {
                ParseAttempt::NoMatch((self.merge)(first_diagnostic, second_diagnostic))
            }
        })
    }
}

/// Bring a foreign leaf's error type to the expression's convention.
///
/// Required, not optional: every leaf entering [`Ap`], [`Bind`], or [`OrderedChoice`] must
/// first be brought to `Error = CombinatorError<E>`. Without this the claim that an existing
/// PEG or CFG evaluator can be a combinator leaf would be false.
pub struct MapErr<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, E2> PartialPrefixParser for MapErr<P, F>
where
    P: PartialPrefixParser,
    F: Fn(P::Error) -> E2,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = P::Diagnostic;
    type Error = E2;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, P::Witness, P::Diagnostic, E2> {
        self.parser
            .parse_prefix(source, start)
            .map_err(&self.function)
    }
}

/// Bring a foreign leaf's diagnostic type to the expression's unified diagnostic.
///
/// The companion of [`MapErr`]: an expression's alternatives must agree on `Diagnostic`
/// before `merge` can fold them, and a foreign leaf arrives with its own.
pub struct MapDiagnostic<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, D2> PartialPrefixParser for MapDiagnostic<P, F>
where
    P: PartialPrefixParser,
    F: Fn(P::Diagnostic) -> D2,
{
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Diagnostic = D2;
    type Error = P::Error;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, P::Witness, D2, P::Error> {
        Ok(match self.parser.parse_prefix(source, start)? {
            ParseAttempt::Match(matched) => ParseAttempt::Match(matched),
            ParseAttempt::NoMatch(diagnostic) => ParseAttempt::NoMatch((self.function)(diagnostic)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A leaf matching one specific byte, with its own error type so that `MapErr` has
    /// something to do.
    struct Byte(u8);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Missing(u8);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct ForeignError;

    impl PartialPrefixParser for Byte {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Diagnostic = Missing;
        type Error = ForeignError;

        fn parse_prefix(
            &self,
            source: &[u8],
            start: usize,
        ) -> PrefixParseResult<u8, (), Missing, ForeignError> {
            match source.get(start) {
                Some(&byte) if byte == self.0 => Ok(ParseAttempt::Match(PrefixInterpretation {
                    value: byte,
                    witness: (),
                    consumed: Span {
                        start,
                        end: start + 1,
                    },
                    remainder: start + 1,
                })),
                _ => Ok(ParseAttempt::NoMatch(Missing(self.0))),
            }
        }
    }

    /// A leaf that fails the evaluator if it is ever consulted. Ordered choice must not
    /// evaluate it after its first alternative matched.
    struct Poisoned;

    impl PartialPrefixParser for Poisoned {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Diagnostic = Missing;
        type Error = CombinatorError<ForeignError>;

        fn parse_prefix(
            &self,
            _source: &[u8],
            _start: usize,
        ) -> PrefixParseResult<u8, (), Missing, CombinatorError<ForeignError>> {
            Err(CombinatorError::Parser(ForeignError))
        }
    }

    fn leaf(byte: u8) -> MapErr<Byte, fn(ForeignError) -> CombinatorError<ForeignError>> {
        MapErr {
            parser: Byte(byte),
            function: CombinatorError::Parser,
        }
    }

    fn last(_left: Missing, right: Missing) -> Missing {
        right
    }

    #[test]
    fn pure_consumes_nothing_at_the_offset_it_was_invoked() {
        let parser = pure::<[u8], _, Missing, CombinatorError<ForeignError>>(|| (7u8, ()));
        let matched = parser
            .parse_prefix(b"abc", 2)
            .expect("no evaluator failure");
        let ParseAttempt::Match(matched) = matched else {
            panic!("pure always matches");
        };
        assert_eq!(matched.consumed, Span { start: 2, end: 2 });
        assert_eq!(matched.remainder, 2);
        assert_eq!(matched.value, 7);
    }

    #[test]
    fn fail_never_matches_and_reports_its_diagnostic() {
        let parser = fail::<[u8], u8, (), Missing, CombinatorError<ForeignError>>(Missing(b'z'));
        let attempt = parser
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure");
        assert_eq!(attempt, ParseAttempt::NoMatch(Missing(b'z')));
    }

    #[test]
    fn bind_threads_the_offset_and_records_the_split() {
        let parser = Bind {
            parser: leaf(b'a'),
            continuation: |value: u8| {
                assert_eq!(value, b'a');
                leaf(b'b')
            },
        };
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure")
        else {
            panic!("expected a match");
        };
        assert_eq!(matched.consumed, Span { start: 0, end: 2 });
        assert_eq!(matched.remainder, 2);
        assert_eq!(matched.witness.split, 1);
    }

    #[test]
    fn bind_does_not_retry_its_head_when_the_continuation_declines() {
        let parser = Bind {
            parser: leaf(b'a'),
            continuation: |_| leaf(b'z'),
        };
        let attempt = parser.parse_prefix(b"ab", 0).expect("no evaluator failure");
        assert_eq!(attempt, ParseAttempt::NoMatch(Missing(b'z')));
    }

    #[test]
    fn ap_applies_a_parsed_function_to_a_parsed_argument() {
        let parser = Ap {
            functions: Map {
                parser: leaf(b'a'),
                function: |first: u8| move |second: u8| (first, second),
            },
            arguments: leaf(b'b'),
        };
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure")
        else {
            panic!("expected a match");
        };
        assert_eq!(matched.value, (b'a', b'b'));
        assert_eq!(matched.consumed, Span { start: 0, end: 2 });
        assert_eq!(matched.witness.split, 1);
    }

    /// The operational signature of ordered choice, and the single highest-value test here:
    /// the second alternative is not evaluated at all once the first matched. Taking the
    /// first result of a union would have evaluated both and surfaced the poison.
    #[test]
    fn ordered_choice_does_not_evaluate_its_second_arm() {
        let parser = OrderedChoice {
            first: leaf(b'a'),
            second: Poisoned,
            merge: last as fn(Missing, Missing) -> Missing,
        };
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"abc", 0)
            .expect("the second arm must not be consulted")
        else {
            panic!("expected a match from the first alternative");
        };
        assert!(matches!(matched.witness, ChoiceWitness::First(())));
    }

    #[test]
    fn ordered_choice_records_the_first_diagnostic_when_the_second_wins() {
        let parser = OrderedChoice {
            first: leaf(b'z'),
            second: leaf(b'a'),
            merge: last as fn(Missing, Missing) -> Missing,
        };
        let ParseAttempt::Match(matched) = parser
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure")
        else {
            panic!("expected a match from the second alternative");
        };
        let ChoiceWitness::Second {
            first_diagnostic, ..
        } = matched.witness
        else {
            panic!("expected the second alternative's witness");
        };
        assert_eq!(first_diagnostic, Missing(b'z'));
    }

    #[test]
    fn ordered_choice_merges_diagnostics_when_both_decline() {
        let parser = OrderedChoice {
            first: leaf(b'y'),
            second: leaf(b'z'),
            merge: last as fn(Missing, Missing) -> Missing,
        };
        let attempt = parser
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure");
        assert_eq!(attempt, ParseAttempt::NoMatch(Missing(b'z')));
    }

    /// Ordered choice is associative on positive content while folding diagnostics
    /// differently. With a non-associative `merge` the two associations disagree on the
    /// declined case, which is exactly why the monoid law holds only in the
    /// diagnostic-forgetting quotient.
    #[test]
    fn ordered_choice_associativity_is_only_up_to_the_diagnostic_fold() {
        // `first` is not associative: it keeps the leftmost, so folding order shows.
        fn keep_left(left: Missing, _right: Missing) -> Missing {
            left
        }
        fn keep_right(_left: Missing, right: Missing) -> Missing {
            right
        }

        let left_nested = OrderedChoice {
            first: OrderedChoice {
                first: leaf(b'x'),
                second: leaf(b'y'),
                merge: keep_right as fn(Missing, Missing) -> Missing,
            },
            second: leaf(b'z'),
            merge: keep_left as fn(Missing, Missing) -> Missing,
        };
        let right_nested = OrderedChoice {
            first: leaf(b'x'),
            second: OrderedChoice {
                first: leaf(b'y'),
                second: leaf(b'z'),
                merge: keep_right as fn(Missing, Missing) -> Missing,
            },
            merge: keep_left as fn(Missing, Missing) -> Missing,
        };

        // Positive content agrees.
        let left_positive = left_nested.parse_prefix(b"z", 0).expect("no failure");
        let right_positive = right_nested.parse_prefix(b"z", 0).expect("no failure");
        let (ParseAttempt::Match(left_matched), ParseAttempt::Match(right_matched)) =
            (&left_positive, &right_positive)
        else {
            panic!("both associations match on this source");
        };
        assert_eq!(left_matched.value, right_matched.value);
        assert_eq!(left_matched.consumed, right_matched.consumed);

        // Diagnostics do not. The two attempts cannot even be compared directly — their
        // witness types differ by association — so the diagnostics are projected out first.
        fn declined<P: PartialPrefixParser>(parser: &P, source: &P::Source) -> P::Diagnostic {
            match parser.parse_prefix(source, 0).ok().expect("no failure") {
                ParseAttempt::NoMatch(diagnostic) => diagnostic,
                ParseAttempt::Match(_) => panic!("expected both associations to decline"),
            }
        }

        let left_declined = declined(&left_nested, b"a");
        let right_declined = declined(&right_nested, b"a");
        assert_eq!(left_declined, Missing(b'y'));
        assert_eq!(right_declined, Missing(b'x'));
        assert_ne!(left_declined, right_declined);
    }

    #[test]
    fn erased_and_borrowed_parsers_forward_faithfully() {
        let concrete = leaf(b'a');
        let borrowed = Ref(&concrete);
        let erased: DynPartial<'_, [u8], u8, (), Missing, CombinatorError<ForeignError>> =
            DynPartial::new(borrowed);
        let ParseAttempt::Match(matched) = erased
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure")
        else {
            panic!("expected a match");
        };
        assert_eq!(matched.value, b'a');
    }

    #[test]
    fn map_diagnostic_unifies_a_foreign_leafs_diagnostic() {
        let parser = MapDiagnostic {
            parser: leaf(b'z'),
            function: |Missing(byte)| byte,
        };
        let attempt = parser
            .parse_prefix(b"abc", 0)
            .expect("no evaluator failure");
        assert_eq!(attempt, ParseAttempt::NoMatch(b'z'));
    }

    #[test]
    fn a_cursor_violation_is_evaluator_failure_not_a_non_match() {
        /// A leaf that reports a match running past the end of the source.
        struct Overrun;

        impl PartialPrefixParser for Overrun {
            type Source = [u8];
            type Value = u8;
            type Witness = ();
            type Diagnostic = Missing;
            type Error = CombinatorError<ForeignError>;

            fn parse_prefix(
                &self,
                source: &[u8],
                start: usize,
            ) -> PrefixParseResult<u8, (), Missing, CombinatorError<ForeignError>> {
                Ok(ParseAttempt::Match(PrefixInterpretation {
                    value: 0,
                    witness: (),
                    consumed: Span {
                        start,
                        end: source.len() + 5,
                    },
                    remainder: source.len() + 5,
                }))
            }
        }

        let parser = Bind {
            parser: Overrun,
            continuation: |_| leaf(b'a'),
        };
        assert!(matches!(
            parser.parse_prefix(b"abc", 0),
            Err(CombinatorError::Cursor(_))
        ));
    }
}
