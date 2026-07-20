//! Axis 1 — the widening adapters, and nothing that undoes them.
//!
//! Each adapter is a named newtype. There is deliberately no blanket impl anywhere
//! in this module: a blanket `impl<P: PartialPrefixParser> RelationalPrefixParser for
//! P` *is* the collapse that the three capabilities exist to prevent, and the absence
//! of such an impl is the enforcement mechanism. Widening is something a caller
//! *asks for* by naming an adapter, never something that happens to a parser because
//! it was passed to a function expecting a wider capability.
//!
//! # Notation used by the laws below
//!
//! Fix a source `s` and a start offset `i`. Write the three evaluations as
//!
//! ```text
//! T⟦p⟧(s,i) : Result<PrefixInterpretation<V,W>, E>
//! P⟦p⟧(s,i) : Result<ParseAttempt<PrefixInterpretation<V,W>, D>, E>
//! R⟦p⟧(s,i) : Result<Vec<PrefixInterpretation<V,W>>, E>
//! ```
//!
//! and write `obs(m) = (m.value, m.consumed, m.remainder)` for the **positive
//! projection**. Witnesses are never compared by any law in this module: two
//! law-equal programs must record different witnesses, so a law demanding witness
//! equality is false.

use crate::host::{RelationalPrefixParser, TotalPrefixParser};
use core::convert::Infallible;
use covalence_parsing_api::{
    ParseAttempt, PartialPrefixParser, PrefixInterpretation, PrefixParseResult,
};

// TODO(cov:lang.combinator-parsing.no-take-first, severe): Do not add a `first()`,
// `take_first`, or any narrowing adapter that picks a result. Ordered choice agrees with
// take-first only on the image of `WidenPartialToRelational` (M4) and diverges the moment a
// bind sits above the choice or either operand is genuinely relational: a continuation that
// declines on the first alternative's value and succeeds on the second makes ordered choice
// decline where take-first over the union matches. A helper would make a scoped agreement
// look like a general identity. `narrow_relational` returning `Narrowed { NoResult, Unique,
// Ambiguous }` is the only sanctioned surface.

// TODO(cov:lang.combinator-parsing.widening-laws-unproved, minor): M1, M2 and M5 are
// stated exactly in the docs below and can be checked only by falsification over a finite
// corpus under a finite budget. Their universal forms — in particular M2's "no retraction
// exists" and M5's cardinality-exactly-one — quantify over all sources, all start offsets
// and all environments, and are provable only at the logic level through
// `theory::CombinatorMorphismLaws`. Host evaluation must never be allowed to mint them.

/// **M1 · total ↪ partial.** Read a total prefix parser as a partial one.
///
/// # Law
///
/// > for all `p`, `s`, `i`:
/// > `P⟦WidenTotalToPartial(p)⟧(s,i) == T⟦p⟧(s,i).map(ParseAttempt::Match)`
///
/// # Status: **isomorphism onto its image** — an injective, information-preserving
/// embedding; a split mono whose retraction is *partial*, defined exactly on `Match`.
///
/// Nothing is discarded in either direction on the image, which is what separates this
/// adapter from [`WidenPartialToRelational`]. `Diagnostic = Infallible` is the
/// load-bearing part and is not a stylistic choice: on the image of this adapter
/// `ParseAttempt::NoMatch` is **uninhabited**, not merely unused. That is the one place
/// in this crate where "a total parser is a partial parser that never declines" is a
/// type-level fact rather than a comment.
///
/// Totality remains modulo resources: budget exhaustion is still `Err` on both sides, so
/// this law says nothing about genuine totality (see the crate's non-goals).
pub struct WidenTotalToPartial<P>(pub P);

impl<P: TotalPrefixParser> PartialPrefixParser for WidenTotalToPartial<P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    /// Uninhabited: a widened total parser cannot construct a non-match.
    type Diagnostic = Infallible;
    type Error = P::Error;

    fn parse_prefix(
        &self,
        source: &P::Source,
        start: usize,
    ) -> PrefixParseResult<P::Value, P::Witness, Infallible, P::Error> {
        self.0
            .parse_prefix_total(source, start)
            .map(ParseAttempt::Match)
    }
}

/// **M2 · partial ↪ relational.** Read a partial prefix parser as a relation.
///
/// # Law
///
/// > for all `p`, `s`, `i`:
/// > ```text
/// > R⟦WidenPartialToRelational(p)⟧(s,i) ==
/// >   match P⟦p⟧(s,i) {
/// >     Ok(Match(m))   => Ok(vec![m]),
/// >     Ok(NoMatch(_)) => Ok(vec![]),
/// >     Err(e)         => Err(e),
/// >   }
/// > ```
/// >
/// > **cardinality corollary:** the result is `Err` or has length **at most one**.
///
/// # Status: **one-way refinement.** Semantics-preserving on positive content; lossy and
/// **non-injective** on negative content.
///
/// **Named for what it discards.** This is a policy, not a coercion. A `NoMatch` carries
/// the claim "no interpretation exists here, and here is why"; the image carries only the
/// far weaker "this evaluator enumerated nothing". Two partial parsers differing *only*
/// in their diagnostics have identical images.
///
/// # §e.8 — there is no retraction
///
/// Because the adapter is non-injective, **no function `narrow` satisfies
/// `narrow(WidenPartialToRelational(p)) == p`.** Such a law is false, not merely
/// unimplemented: it would have to recover a diagnostic that was destroyed. The
/// strongest true statement is agreement *up to diagnostic*, which is a strictly weaker
/// claim about a strictly smaller observation. Nothing in this crate offers a retraction,
/// and [`crate::morphism::narrow_relational`] is not one — it forces a policy decision on
/// the caller and cannot invent a diagnostic either.
///
/// Note also that the empty vector on the image is *not* the same fact as `Declined`.
/// The two are different variants of different observation types, and they are identified
/// in exactly one place: the explicitly named lossy coercion in the harness.
pub struct WidenPartialToRelational<P>(pub P);

impl<P: PartialPrefixParser> RelationalPrefixParser for WidenPartialToRelational<P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefixes(
        &self,
        source: &P::Source,
        start: usize,
    ) -> Result<Vec<PrefixInterpretation<P::Value, P::Witness>>, P::Error> {
        Ok(match self.0.parse_prefix(source, start)? {
            // The diagnostic is dropped here, and this is the only line in the crate that
            // does so. It is why the adapter is named for the loss and has no inverse.
            ParseAttempt::NoMatch(_) => Vec::new(),
            ParseAttempt::Match(matched) => vec![matched],
        })
    }
}

/// **M5 · total ↪ relational.** Read a total prefix parser directly as a relation.
///
/// # Law
///
/// > for all `p`, `s`, `i`:
/// > `R⟦WidenTotalToRelational(p)⟧(s,i) == T⟦p⟧(s,i).map(|m| vec![m])`
/// >
/// > **cardinality:** the result is `Err` or has length **exactly one**.
///
/// # Status: **one-way refinement**, strictly stronger than composing M1 with M2.
///
/// This is its own newtype rather than a type alias for
/// `WidenPartialToRelational<WidenTotalToPartial<P>>` precisely so the exactly-one law
/// has a subject that cannot be mistaken for M2's at-most-one. The two adapters are
/// extensionally equal on observations, but the stronger law is a property of *this*
/// type, and stating it about the composite would attach it to a type whose other
/// inhabitants do not satisfy it.
///
/// This length-one law is the only behavioural pin on "total" the host can apply at all,
/// and it is still per-sample. A total parser whose `Value` has a distinguished failure
/// inhabitant — `Option<A>`, say — has smuggled the non-match channel back inside the
/// value, and the law becomes vacuous without a corpus obligation excluding such types.
pub struct WidenTotalToRelational<P>(pub P);

impl<P: TotalPrefixParser> RelationalPrefixParser for WidenTotalToRelational<P> {
    type Source = P::Source;
    type Value = P::Value;
    type Witness = P::Witness;
    type Error = P::Error;

    fn parse_prefixes(
        &self,
        source: &P::Source,
        start: usize,
    ) -> Result<Vec<PrefixInterpretation<P::Value, P::Witness>>, P::Error> {
        self.0
            .parse_prefix_total(source, start)
            .map(|matched| vec![matched])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::budget::CombinatorDiagnostic;

    /// A total parser that consumes one atom.
    struct OneByte;

    impl TotalPrefixParser for OneByte {
        type Source = [u8];
        type Value = usize;
        type Witness = ();
        type Error = ();

        fn parse_prefix_total(
            &self,
            source: &[u8],
            start: usize,
        ) -> Result<PrefixInterpretation<usize, ()>, ()> {
            let end = (start + 1).min(source.len());
            Ok(PrefixInterpretation {
                value: end,
                witness: (),
                consumed: covalence_parsing_api::Span::new(start, end).expect("forward"),
                remainder: end,
            })
        }
    }

    /// A partial parser that declines on an empty remainder.
    struct MaybeByte;

    impl PartialPrefixParser for MaybeByte {
        type Source = [u8];
        type Value = usize;
        type Witness = ();
        type Diagnostic = CombinatorDiagnostic;
        type Error = ();

        fn parse_prefix(
            &self,
            source: &[u8],
            start: usize,
        ) -> PrefixParseResult<usize, (), CombinatorDiagnostic, ()> {
            if start >= source.len() {
                return Ok(ParseAttempt::NoMatch(CombinatorDiagnostic::new(
                    start,
                    crate::budget::CombinatorDiagnosticKind::NoMatch,
                )));
            }
            Ok(ParseAttempt::Match(PrefixInterpretation {
                value: start + 1,
                witness: (),
                consumed: covalence_parsing_api::Span::new(start, start + 1).expect("forward"),
                remainder: start + 1,
            }))
        }
    }

    /// **M1, compared rather than merely typed.**
    ///
    /// The `NoMatch` arm is uninhabited by type — `Diagnostic = Infallible` — so
    /// matching on it establishes nothing that the type checker had not already
    /// established. The *content* of M1 is the other half: the `Match` carries the
    /// inner total parser's own interpretation, unchanged. So that is what this
    /// compares, on the positive projection, against a direct call to the inner
    /// parser. An adapter that matched everywhere while altering the observation
    /// would satisfy the old shape of this test and violate the law.
    #[test]
    fn m1_widened_total_matches_with_the_inner_interpretation() {
        let widened = WidenTotalToPartial(OneByte);
        // `start <= source.len()` is the total capability's caller precondition.
        for start in 0..=2 {
            let inner = OneByte
                .parse_prefix_total(b"ab", start)
                .expect("no failure");
            match widened.parse_prefix(b"ab", start).expect("no failure") {
                ParseAttempt::Match(matched) => assert_eq!(
                    (matched.value, matched.consumed, matched.remainder),
                    (inner.value, inner.consumed, inner.remainder),
                    "M1 must not alter the observation it embeds"
                ),
                ParseAttempt::NoMatch(never) => match never {},
            }
        }
    }

    #[test]
    fn m2_cardinality_is_at_most_one_and_decline_enumerates_nothing() {
        let widened = WidenPartialToRelational(MaybeByte);
        assert_eq!(
            widened.parse_prefixes(b"ab", 0).expect("no failure").len(),
            1
        );
        // The diagnostic is gone. That loss is the content of "no retraction exists".
        assert!(
            widened
                .parse_prefixes(b"ab", 2)
                .expect("no failure")
                .is_empty()
        );
    }

    #[test]
    fn m5_cardinality_is_exactly_one() {
        let widened = WidenTotalToRelational(OneByte);
        for start in 0..=2 {
            assert_eq!(
                widened
                    .parse_prefixes(b"ab", start)
                    .expect("no failure")
                    .len(),
                1
            );
        }
    }
}
