//! Host combinators for the **total** capability: every in-range start yields exactly one
//! interpretation.
//!
//! # This module exports no failure operator, and that is structural
//!
//! There is no `Fail`, no `OrderedChoice`, and no `Union` here. A total parser has no
//! non-match channel, so a second alternative could never be consulted: choice is not merely
//! unimplemented for this capability, it is unstatable. Adding a failure operator here would
//! mean giving [`TotalPrefixParser`] a non-match channel, which is precisely the collapse the
//! separation of these three modules exists to prevent.
//!
//! # "Total" is not total, and the crate says so
//!
//! Two honest caveats. First, totality is modulo resources: a cursor violation from a
//! misbehaving leaf is still `Err`, exactly as budget exhaustion is `Err` on the other
//! capabilities. Second, a total parser whose `Value` is `Option<A>` — or any type with a
//! distinguished failure inhabitant — has smuggled the non-match channel back *inside the
//! value*, at which point total-versus-partial is a naming convention and nothing more. This
//! crate cannot detect that, so it is a caller obligation, and it is why the conformance
//! corpus for this capability must exclude such value types.
//!
//! `start > source.extent()` is a caller precondition rather than a reported outcome, since
//! there is no channel in which to report it.

use core::marker::PhantomData;

use covalence_parsing_api::{PrefixInterpretation, Span};

use crate::host::cursor::{CombinatorError, CursorViolation, SourceExtent, check_step, join};
use crate::host::witness::SeqWitness;
use crate::host::{Marker, TotalPrefixParser};

/// Consumes nothing and always yields the same interpretation.
///
/// The factory is forced for the same reason as in the partial capability: `&self` methods
/// plus function-typed values leave no workable stored-value shape.
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

impl<S: ?Sized, F, V, W, E> TotalPrefixParser for Pure<S, F, E>
where
    F: Fn() -> (V, W),
{
    type Source = S;
    type Value = V;
    type Witness = W;
    type Error = E;

    fn parse_prefix_total(
        &self,
        _source: &S,
        start: usize,
    ) -> Result<PrefixInterpretation<V, W>, E> {
        let (value, witness) = (self.make)();
        Ok(PrefixInterpretation {
            value,
            witness,
            consumed: Span { start, end: start },
            remainder: start,
        })
    }
}

/// Borrowed reuse. The orphan rule forbids an impl on `&P` from this crate.
pub struct Ref<'p, P: ?Sized>(pub &'p P);

impl<P: TotalPrefixParser + ?Sized> TotalPrefixParser for Ref<'_, P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefix_total(
        &self,
        source: &P::Source,
        start: usize,
    ) -> Result<PrefixInterpretation<P::Value, P::Witness>, P::Error> {
        self.0.parse_prefix_total(source, start)
    }
}

/// Type erasure, for the same E0117 reason as `partial::DynPartial`.
pub struct DynTotal<'p, S: ?Sized, V, W, E>(
    pub Box<dyn TotalPrefixParser<Source = S, Value = V, Witness = W, Error = E> + 'p>,
);

impl<'p, S: ?Sized, V, W, E> DynTotal<'p, S, V, W, E> {
    /// Erase a concrete parser.
    pub fn new<P>(parser: P) -> Self
    where
        P: TotalPrefixParser<Source = S, Value = V, Witness = W, Error = E> + 'p,
    {
        Self(Box::new(parser))
    }
}

impl<S: ?Sized, V, W, E> TotalPrefixParser for DynTotal<'_, S, V, W, E> {
    type Source = S;
    type Value = V;
    type Witness = W;
    type Error = E;

    fn parse_prefix_total(
        &self,
        source: &S,
        start: usize,
    ) -> Result<PrefixInterpretation<V, W>, E> {
        self.0.parse_prefix_total(source, start)
    }
}

/// Value mapping. Error-transparent: mapping cannot fail.
pub struct Map<P, F> {
    pub parser: P,
    pub function: F,
}

impl<P, F, B> TotalPrefixParser for Map<P, F>
where
    P: TotalPrefixParser,
    F: Fn(P::Value) -> B,
{
    type Source = P::Source;
    type Value = B;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefix_total(
        &self,
        source: &P::Source,
        start: usize,
    ) -> Result<PrefixInterpretation<B, P::Witness>, P::Error> {
        let matched = self.parser.parse_prefix_total(source, start)?;
        Ok(PrefixInterpretation {
            value: (self.function)(matched.value),
            witness: matched.witness,
            consumed: matched.consumed,
            remainder: matched.remainder,
        })
    }
}

/// Value-independent sequencing with application.
pub struct Ap<P, Q> {
    pub functions: P,
    pub arguments: Q,
}

impl<P, Q, B, E> TotalPrefixParser for Ap<P, Q>
where
    P: TotalPrefixParser<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    P::Value: FnOnce(Q::Value) -> B,
    Q: TotalPrefixParser<Source = P::Source, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = B;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Error = CombinatorError<E>;

    fn parse_prefix_total(
        &self,
        source: &P::Source,
        start: usize,
    ) -> Result<PrefixInterpretation<B, Self::Witness>, CombinatorError<E>> {
        let source_len = source.extent();
        let function = check_step(
            start,
            source_len,
            self.functions.parse_prefix_total(source, start)?,
        )
        .map_err(CombinatorError::Cursor)?;
        let split = function.remainder;
        let argument = check_step(
            split,
            source_len,
            self.arguments.parse_prefix_total(source, split)?,
        )
        .map_err(CombinatorError::Cursor)?;
        let consumed = join(function.consumed, argument.consumed).ok_or_else(|| {
            CombinatorError::Cursor(CursorViolation {
                invoked_at: start,
                consumed: argument.consumed,
                remainder: argument.remainder,
                source_len,
            })
        })?;
        Ok(PrefixInterpretation {
            value: (function.value)(argument.value),
            witness: SeqWitness {
                first: function.witness,
                second: argument.witness,
                split,
            },
            consumed,
            remainder: argument.remainder,
        })
    }
}

/// Value-dependent sequencing.
///
/// The continuation is invoked on every parse; there is no memoization. Unlike the partial
/// and relational binds there is no "the continuation declined" case at all, because the
/// continuation is itself total.
pub struct Bind<P, F> {
    pub parser: P,
    pub continuation: F,
}

impl<P, F, Q, E> TotalPrefixParser for Bind<P, F>
where
    P: TotalPrefixParser<Error = CombinatorError<E>>,
    P::Source: SourceExtent,
    F: Fn(P::Value) -> Q,
    Q: TotalPrefixParser<Source = P::Source, Error = CombinatorError<E>>,
{
    type Source = P::Source;
    type Value = Q::Value;
    type Witness = SeqWitness<P::Witness, Q::Witness>;
    type Error = CombinatorError<E>;

    fn parse_prefix_total(
        &self,
        source: &P::Source,
        start: usize,
    ) -> Result<PrefixInterpretation<Q::Value, Self::Witness>, CombinatorError<E>> {
        let source_len = source.extent();
        let head = check_step(
            start,
            source_len,
            self.parser.parse_prefix_total(source, start)?,
        )
        .map_err(CombinatorError::Cursor)?;
        let split = head.remainder;
        let tail = check_step(
            split,
            source_len,
            (self.continuation)(head.value).parse_prefix_total(source, split)?,
        )
        .map_err(CombinatorError::Cursor)?;
        let consumed = join(head.consumed, tail.consumed).ok_or_else(|| {
            CombinatorError::Cursor(CursorViolation {
                invoked_at: start,
                consumed: tail.consumed,
                remainder: tail.remainder,
                source_len,
            })
        })?;
        Ok(PrefixInterpretation {
            value: tail.value,
            witness: SeqWitness {
                first: head.witness,
                second: tail.witness,
                split,
            },
            consumed,
            remainder: tail.remainder,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Never;

    /// Reads one byte, saturating at the end of the source. Total: there is no offset at
    /// which it declines. Its value type has no distinguished failure inhabitant.
    struct SaturatingByte;

    impl TotalPrefixParser for SaturatingByte {
        type Source = [u8];
        type Value = u8;
        type Witness = ();
        type Error = CombinatorError<Never>;

        fn parse_prefix_total(
            &self,
            source: &[u8],
            start: usize,
        ) -> Result<PrefixInterpretation<u8, ()>, CombinatorError<Never>> {
            match source.get(start) {
                Some(&byte) => Ok(PrefixInterpretation {
                    value: byte,
                    witness: (),
                    consumed: Span {
                        start,
                        end: start + 1,
                    },
                    remainder: start + 1,
                }),
                None => Ok(PrefixInterpretation {
                    value: 0,
                    witness: (),
                    consumed: Span { start, end: start },
                    remainder: start,
                }),
            }
        }
    }

    #[test]
    fn pure_yields_an_empty_extent_at_the_start_offset() {
        let parser = pure::<[u8], _, Never>(|| (1u8, ()));
        let matched = parser.parse_prefix_total(b"abc", 1).expect("total");
        assert_eq!(matched.consumed, Span { start: 1, end: 1 });
        assert_eq!(matched.remainder, 1);
    }

    #[test]
    fn bind_sequences_and_records_the_split() {
        let parser = Bind {
            parser: SaturatingByte,
            continuation: |_| SaturatingByte,
        };
        let matched = parser.parse_prefix_total(b"ab", 0).expect("total");
        assert_eq!(matched.value, b'b');
        assert_eq!(matched.consumed, Span { start: 0, end: 2 });
        assert_eq!(matched.witness.split, 1);
    }

    #[test]
    fn ap_applies_across_a_sequence() {
        let parser = Ap {
            functions: Map {
                parser: SaturatingByte,
                function: |first: u8| move |second: u8| (first, second),
            },
            arguments: SaturatingByte,
        };
        let matched = parser.parse_prefix_total(b"ab", 0).expect("total");
        assert_eq!(matched.value, (b'a', b'b'));
    }

    /// Totality is modulo resources: a misbehaving leaf still yields `Err`. This is the
    /// honest content of the caveat in the module doc.
    #[test]
    fn a_cursor_violation_is_still_an_error_in_the_total_capability() {
        struct Backwards;

        impl TotalPrefixParser for Backwards {
            type Source = [u8];
            type Value = u8;
            type Witness = ();
            type Error = CombinatorError<Never>;

            fn parse_prefix_total(
                &self,
                _source: &[u8],
                start: usize,
            ) -> Result<PrefixInterpretation<u8, ()>, CombinatorError<Never>> {
                Ok(PrefixInterpretation {
                    value: 0,
                    witness: (),
                    consumed: Span { start, end: start },
                    // Steps backwards from where it was invoked.
                    remainder: start.saturating_sub(1),
                })
            }
        }

        let parser = Bind {
            parser: Backwards,
            continuation: |_| SaturatingByte,
        };
        assert!(matches!(
            parser.parse_prefix_total(b"abc", 2),
            Err(CombinatorError::Cursor(_))
        ));
    }
}
