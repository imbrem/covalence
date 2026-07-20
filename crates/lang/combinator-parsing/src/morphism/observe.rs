//! What a law is allowed to compare.
//!
//! Three observation types, one per capability, with explicit named lossy
//! coercions between them. This is the one place the design comes near a single
//! normal form for all three capabilities, so the separation is made
//! *structural* rather than conventional: [`PartialObserved::Declined`] and
//! [`RelationalObserved::Enumerated`] of an empty vector are different variants
//! of **different types**, and the only place they are ever identified is the
//! named function [`partial_as_relational`].
//!
//! `Failed` is a distinct variant in all three. Collapsing evaluator failure
//! into the same case as ordinary non-match would make two parsers that differ
//! in exactly that respect satisfy every law in the suite — which is the failure
//! mode this crate exists to prevent.
//!
//! # Witnesses are not observable
//!
//! [`Observation`] has no witness field, and that is load-bearing rather than an
//! omission. `map g (map f p)` and `map (g ∘ f) p` are law-equal and *must*
//! record different witnesses; a law demanding witness equality would be false.
//! [`Observation::of`] is the projection that discards it, and it is the only
//! way an observation is built from a parse result, so no law can reach a
//! witness even by accident.
//!
//! The one sound witness-level statement is a span projection, and it is offered
//! only as an optional law gated on a caller-supplied `fn(&W) -> Span` — see
//! [`observe_span`].

use covalence_parsing_api::{ParseAttempt, PrefixInterpretation, PrefixParseResult, Span};

/// The positive projection: value, consumed extent, remainder. Never the witness.
#[derive(Clone, Debug)]
pub struct Observation<V> {
    pub value: V,
    pub consumed: Span,
    pub remainder: usize,
}

impl<V> Observation<V> {
    /// Project an interpretation onto what laws may compare, **discarding the
    /// witness**. This is the only constructor used by the harness.
    pub fn of<W>(interpretation: PrefixInterpretation<V, W>) -> Self {
        Self {
            value: interpretation.value,
            consumed: interpretation.consumed,
            remainder: interpretation.remainder,
        }
    }

    /// The extent half of the projection. Compared with host `==`, which is
    /// admitted because spans and remainders are host offsets — A0015 data, not
    /// object values.
    ///
    /// **Valid within one carrier only.** A byte-indexed and a scalar-indexed
    /// encoding of the "same" parser produce different spans for the same
    /// source, so every agreement law is indexed by carrier; cross-carrier
    /// comparison must go through a decoding, never through `==`.
    pub fn extent(&self) -> (Span, usize) {
        (self.consumed, self.remainder)
    }
}

/// The optional witness-level law: project a witness to a span and compare that.
///
/// Offered as a free function rather than a field on [`Observation`] so that the
/// default path cannot reach a witness at all. Every in-house witness type
/// exposes a `span`, so the caller always has a projection to supply.
pub fn observe_span<W>(witness: &W, project: &mut impl FnMut(&W) -> Span) -> Span {
    project(witness)
}

/// A total observation. There is no `Declined` variant, and its absence is the
/// point: a total parser has no channel in which to report ordinary non-match.
#[derive(Clone, Debug)]
pub enum TotalObserved<V, E> {
    Produced(Observation<V>),
    Failed(E),
}

/// A partial observation. `Declined` carries no diagnostic, because diagnostics
/// are never compared across encodings — only the trichotomy is.
#[derive(Clone, Debug)]
pub enum PartialObserved<V, E> {
    Matched(Observation<V>),
    Declined,
    Failed(E),
}

/// A relational observation. There is no diagnostic here and there never will
/// be; an empty enumeration is not a negative fact and carries no explanation.
#[derive(Clone, Debug)]
pub enum RelationalObserved<V, E> {
    Enumerated(Vec<Observation<V>>),
    Failed(E),
}

/// Observe a total parse. Discards the witness and nothing else.
pub fn observe_total<V, W, E>(
    result: Result<PrefixInterpretation<V, W>, E>,
) -> TotalObserved<V, E> {
    match result {
        Ok(produced) => TotalObserved::Produced(Observation::of(produced)),
        Err(error) => TotalObserved::Failed(error),
    }
}

/// Observe a partial parse.
///
/// **This is where the diagnostic dies, and it is the only place it does.** A
/// `NoMatch(d)` becomes a bare `Declined`, so two parsers that decline with
/// *different* diagnostics have the same observation. That is the observation-level
/// shadow of M2's non-injectivity, and it is why no law in this crate may compare
/// diagnostic payloads: by the time a law sees anything, there is no diagnostic left
/// to compare.
pub fn observe_partial<V, W, D, E>(result: PrefixParseResult<V, W, D, E>) -> PartialObserved<V, E> {
    match result {
        Ok(ParseAttempt::Match(matched)) => PartialObserved::Matched(Observation::of(matched)),
        Ok(ParseAttempt::NoMatch(_)) => PartialObserved::Declined,
        Err(error) => PartialObserved::Failed(error),
    }
}

/// Observe a relational parse. Enumeration order is preserved: it is meaningful data
/// in this family, not an artifact, so nothing here sorts or deduplicates.
pub fn observe_relational<V, W, E>(
    result: Result<Vec<PrefixInterpretation<V, W>>, E>,
) -> RelationalObserved<V, E> {
    match result {
        Ok(enumerated) => {
            RelationalObserved::Enumerated(enumerated.into_iter().map(Observation::of).collect())
        }
        Err(error) => RelationalObserved::Failed(error),
    }
}

/// **M1, as a function on observations.** Injective and information-preserving:
/// the image never contains `Declined`.
pub fn total_as_partial<V, E>(observed: TotalObserved<V, E>) -> PartialObserved<V, E> {
    match observed {
        TotalObserved::Produced(observation) => PartialObserved::Matched(observation),
        TotalObserved::Failed(error) => PartialObserved::Failed(error),
    }
}

/// **M2, as a function on observations.** `Declined` maps to `Enumerated(vec![])`:
/// the "no interpretation exists here, and here is why" claim implicit in a decline
/// becomes the weaker "this evaluator enumerated nothing".
///
/// This is the *only* place partial-non-match and relational-emptiness are
/// identified anywhere in the crate.
///
/// # Where the non-injectivity actually lives
///
/// **This function is injective**, and saying otherwise would misplace the loss. Its
/// three cases land in three distinguishable images, so as a map on *observations* it
/// discards nothing and could be inverted.
///
/// M2 is non-injective at the **parser** level, on
/// [`crate::morphism::WidenPartialToRelational`]: two partial parsers differing only
/// in the diagnostics they report have identical relational behaviour. The diagnostic
/// is already gone by the time an observation exists — it was dropped by
/// [`observe_partial`] — so no function on this type could exhibit the loss, and the
/// no-retraction statement (§e.8) is a claim about the adapter, not about this
/// coercion. See `parsers_differing_only_in_diagnostic_are_indistinguishable` below,
/// which exhibits it where it is real.
pub fn partial_as_relational<V, E>(observed: PartialObserved<V, E>) -> RelationalObserved<V, E> {
    match observed {
        PartialObserved::Matched(observation) => RelationalObserved::Enumerated(vec![observation]),
        PartialObserved::Declined => RelationalObserved::Enumerated(Vec::new()),
        PartialObserved::Failed(error) => RelationalObserved::Failed(error),
    }
}

/// **M5, as a function on observations.** Distinguished from
/// `partial_as_relational ∘ total_as_partial` only by the law it carries: the
/// result is `Failed` or has length **exactly** one, where M2 gives only `≤ 1`.
pub fn total_as_relational<V, E>(observed: TotalObserved<V, E>) -> RelationalObserved<V, E> {
    partial_as_relational(total_as_partial(observed))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn observation(value: u8) -> Observation<u8> {
        Observation {
            value,
            consumed: Span::new(0, 1).expect("well-ordered"),
            remainder: 1,
        }
    }

    /// **§e.8, exhibited where it is real.**
    ///
    /// Two partial parses that decline with *different* diagnostics are already
    /// indistinguishable as observations, and so remain indistinguishable after
    /// widening. That — not any property of `partial_as_relational` itself, which is
    /// injective — is the content of "M2 has no retraction": there is nothing left
    /// from which a diagnostic could be recovered.
    ///
    /// The earlier version of this test compared `Declined` against `Declined` and
    /// asserted they agreed, which is true of every function and proves nothing.
    #[test]
    fn parsers_differing_only_in_diagnostic_are_indistinguishable() {
        let declined_here: PrefixParseResult<u8, (), &str, ()> =
            Ok(ParseAttempt::NoMatch("expected a digit"));
        let declined_there: PrefixParseResult<u8, (), &str, ()> =
            Ok(ParseAttempt::NoMatch("unexpected end of input"));

        // Distinct diagnostics; identical observations, before any widening happens.
        assert!(matches!(
            observe_partial(declined_here),
            PartialObserved::Declined
        ));
        assert!(matches!(
            observe_partial(declined_there),
            PartialObserved::Declined
        ));

        // And therefore identical relational images.
        assert!(matches!(
            partial_as_relational(PartialObserved::<u8, ()>::Declined),
            RelationalObserved::Enumerated(members) if members.is_empty()
        ));
    }

    /// The counterpart, and the reason the doc above corrects itself: as a map on
    /// observations this coercion *is* injective — a decline and a match land in
    /// distinguishable images, so nothing is lost at this step.
    #[test]
    fn the_coercion_itself_loses_nothing() {
        let from_decline = partial_as_relational(PartialObserved::<u8, ()>::Declined);
        let from_match = partial_as_relational(PartialObserved::<u8, ()>::Matched(observation(7)));
        assert!(matches!(
            (from_decline, from_match),
            (
                RelationalObserved::Enumerated(empty),
                RelationalObserved::Enumerated(single)
            ) if empty.is_empty() && single.len() == 1
        ));
    }

    /// Evaluator failure never becomes an empty enumeration. If it did, a parser
    /// that crashed and a parser that found nothing would satisfy every law
    /// alike.
    #[test]
    fn failure_never_becomes_emptiness() {
        assert!(matches!(
            partial_as_relational(PartialObserved::<u8, &str>::Failed("boom")),
            RelationalObserved::Failed("boom")
        ));
    }

    /// M5's cardinality is exactly one, not merely at most one.
    #[test]
    fn total_widens_to_exactly_one_result() {
        assert!(matches!(
            total_as_relational(TotalObserved::<u8, ()>::Produced(observation(7))),
            RelationalObserved::Enumerated(results) if results.len() == 1
        ));
    }
}
