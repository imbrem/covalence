//! Cursor bookkeeping and the error convention every host combinator expression agrees on.
//!
//! A combinator must be able to reject a sub-parser that ran off the end of its source or
//! stepped backwards. Unlike the parsing API's adapters it cannot take `source_len` as an
//! argument, because combinators nest: the length has to be recoverable from the source
//! value itself. That is what [`SourceExtent`] is for.
//!
//! A cursor violation is *evaluator failure*, never ordinary non-match. A sub-parser that
//! simply does not match reports that through its own diagnostic channel; a sub-parser that
//! reports a match at an impossible extent is broken.

use core::fmt;

use covalence_parsing_api::{PrefixInterpretation, Span};

use crate::budget::CombinatorLimit;

/// The length of a source in the parser's own carrier units.
///
/// **There is deliberately no `impl SourceExtent for str`.** The parsing API's `Span`
/// documents that byte and Unicode-scalar offsets must not be silently mixed, and every text
/// parser in this family is over `[UnicodeScalar]`. A `str` impl would hand back a byte
/// count that a scalar-indexed combinator would then compare against scalar remainders
/// inside [`check_step`], which is exactly the confusion `Span` warns about.
pub trait SourceExtent {
    fn extent(&self) -> usize;
}

impl<A> SourceExtent for [A] {
    fn extent(&self) -> usize {
        self.len()
    }
}

/// A sub-parser returned an extent that is not a forward step from where it was invoked.
///
/// Evaluator failure, never ordinary non-match.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CursorViolation {
    pub invoked_at: usize,
    pub consumed: Span,
    pub remainder: usize,
    pub source_len: usize,
}

impl fmt::Display for CursorViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "sub-parser invoked at {} reported consumed {}..{} with remainder {} over a source of length {}",
            self.invoked_at,
            self.consumed.start,
            self.consumed.end,
            self.remainder,
            self.source_len
        )
    }
}

impl core::error::Error for CursorViolation {}

/// The error type every host combinator expression agrees on.
///
/// Idempotent by construction: a combinator built over parsers whose `Error` is already
/// `CombinatorError<E>` again has error type `CombinatorError<E>`, so long chains do not
/// build an error tower. Foreign leaves are brought to this convention with
/// [`MapErr`](crate::host::partial::MapErr) rather than by implementing a trait.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CombinatorError<E> {
    /// A leaf parser's own evaluator failure.
    Parser(E),
    /// A sub-parser reported an impossible extent.
    Cursor(CursorViolation),
    /// A caller-supplied bound was reached.
    ///
    /// Raised by the relational capability for result limits, and by
    /// [`recursion`](crate::host::recursion) for the partial capability's depth bound. The
    /// total capability raises it for neither: it produces exactly one result per offset and
    /// has no recursion operator.
    Limit(CombinatorLimit),
}

impl<E: fmt::Display> fmt::Display for CombinatorError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parser(error) => write!(f, "parser error: {error}"),
            Self::Cursor(violation) => write!(f, "cursor violation: {violation}"),
            Self::Limit(limit) => write!(
                f,
                "combinator evaluation exhausted {:?} (limit {})",
                limit.resource, limit.limit
            ),
        }
    }
}

impl<E: core::error::Error + 'static> core::error::Error for CombinatorError<E> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Parser(error) => Some(error),
            Self::Cursor(violation) => Some(violation),
            Self::Limit(_) => None,
        }
    }
}

/// Validate that an interpretation is a forward step from `invoked_at` that stays inside the
/// source.
///
/// Checks all four conditions a combinator relies on and cannot otherwise recover: the
/// extent starts where the sub-parser was invoked, the remainder agrees with the extent's
/// end, the step does not move backwards, and it does not run past the end of the source.
pub fn check_step<V, W>(
    invoked_at: usize,
    source_len: usize,
    step: PrefixInterpretation<V, W>,
) -> Result<PrefixInterpretation<V, W>, CursorViolation> {
    let violated = step.consumed.start != invoked_at
        || step.consumed.end != step.remainder
        || step.remainder < invoked_at
        || step.remainder > source_len;
    if violated {
        return Err(CursorViolation {
            invoked_at,
            consumed: step.consumed,
            remainder: step.remainder,
            source_len,
        });
    }
    Ok(step)
}

/// Concatenate two adjacent extents.
///
/// Validates adjacency *and* `start <= end`, because `Span`'s fields are public and
/// `Span::new` is the only checked constructor, so a `Span` reaching this function has not
/// necessarily been through one.
pub fn join(first: Span, second: Span) -> Option<Span> {
    if first.end != second.start {
        return None;
    }
    Span::new(first.start, second.end)
}

/// Concatenate the extent of a completed first step with the step that followed it,
/// reporting non-adjacency as a cursor violation attributed to `invoked_at`.
///
/// Every sequencing combinator in every capability needs exactly this: the two extents were
/// each validated by [`check_step`] against their own invocation offset, but adjacency
/// between them is a separate condition that only the combinator joining them can check.
/// It is extent bookkeeping, not semantics, which is why one helper serves all three
/// capabilities without relating them.
pub fn join_steps<V, W, E>(
    invoked_at: usize,
    source_len: usize,
    first: Span,
    second: &PrefixInterpretation<V, W>,
) -> Result<Span, CombinatorError<E>> {
    join(first, second.consumed).ok_or(CombinatorError::Cursor(CursorViolation {
        invoked_at,
        consumed: second.consumed,
        remainder: second.remainder,
        source_len,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn step(start: usize, end: usize, remainder: usize) -> PrefixInterpretation<(), ()> {
        PrefixInterpretation {
            value: (),
            witness: (),
            consumed: Span { start, end },
            remainder,
        }
    }

    #[test]
    fn slices_report_their_length_as_extent() {
        assert_eq!([1u8, 2, 3][..].extent(), 3);
        assert_eq!(<[u8]>::extent(&[]), 0);
    }

    #[test]
    fn a_forward_step_inside_the_source_is_accepted() {
        assert!(check_step(2, 8, step(2, 5, 5)).is_ok());
        // An empty step is forward.
        assert!(check_step(2, 8, step(2, 2, 2)).is_ok());
    }

    #[test]
    fn check_step_rejects_every_way_a_cursor_can_be_wrong() {
        // Does not start where it was invoked.
        assert!(check_step(2, 8, step(1, 5, 5)).is_err());
        // Remainder disagrees with the extent.
        assert!(check_step(2, 8, step(2, 5, 4)).is_err());
        // Runs past the end of the source.
        assert!(check_step(2, 8, step(2, 9, 9)).is_err());
    }

    #[test]
    fn join_requires_adjacency() {
        assert_eq!(
            join(Span { start: 0, end: 3 }, Span { start: 3, end: 7 }),
            Span::new(0, 7)
        );
        assert_eq!(
            join(Span { start: 0, end: 3 }, Span { start: 4, end: 7 }),
            None
        );
        // A `Span` with public fields need not have passed through `Span::new`.
        assert_eq!(
            join(Span { start: 5, end: 3 }, Span { start: 3, end: 4 }),
            None
        );
    }
}
