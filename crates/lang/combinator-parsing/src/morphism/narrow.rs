//! Axis 1, the other direction — **M6 · relational → partial is NOT a morphism.**
//!
//! There is no canonical narrowing. Enumeration order is *meaningful data* in this
//! family — a chart parser sorts its derivations deterministically and its stability is
//! asserted by test — but deterministic is not the same as canonical, and picking the
//! first result would be a policy choice about enumeration order dressed up as a
//! coercion.
//!
//! So this module offers no adapter and no trait impl. It offers a three-way outcome
//! that *forces the caller to decide*, and a function that classifies without picking.
//!
//! # Status of the relationship: **not a morphism.** No law of the form
//! `narrow(widen(p)) == p` holds — see the no-retraction discussion on
//! [`crate::morphism::WidenPartialToRelational`] (§e.8). What is true is only that
//! narrowing *classifies*: it reports emptiness, uniqueness, or ambiguity, and it is the
//! caller who supplies the meaning of each.

use covalence_parsing_api::PrefixInterpretation;

/// The result of classifying an enumeration, with ambiguity as a distinguished answer.
///
/// **`Ambiguous` is not an `Err`.** Ambiguity is a property of the grammar and the
/// source, not a failure of the evaluator, and reporting it as an error would put an
/// ordinary parsing outcome into the channel this crate reserves for evaluator failure.
///
/// **`NoResult` is not a diagnostic either.** An empty enumeration proves no negative
/// fact: it records that this evaluator, under this budget, enumerated nothing. It does
/// not record that nothing matches, and the relational capability has no channel that
/// could say why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Narrowed<V, W> {
    NoResult,
    Unique(PrefixInterpretation<V, W>),
    Ambiguous(Vec<PrefixInterpretation<V, W>>),
}

/// Classify an enumeration without choosing among its members.
///
/// # Law
///
/// > `narrow_relational(rs)` is `NoResult` iff `rs.is_empty()`, `Unique(m)` iff
/// > `rs == vec![m]`, and `Ambiguous(rs)` otherwise, retaining `rs` in enumeration order.
///
/// # Status: **total classification, not a retraction.**
///
/// This function never picks a result, never reorders, never deduplicates and never
/// discards. Deduplication would need a caller-supplied agreement that is an equivalence,
/// which this signature does not take and this crate does not assume; doing it here would
/// destroy the ambiguity retention the relational capability exists to provide.
///
/// It is not an inverse of any widening: on the image of
/// [`crate::morphism::WidenPartialToRelational`] it returns `NoResult` exactly where the
/// original returned `NoMatch(d)`, and `d` is unrecoverable.
pub fn narrow_relational<V, W>(mut results: Vec<PrefixInterpretation<V, W>>) -> Narrowed<V, W> {
    match results.len() {
        0 => Narrowed::NoResult,
        1 => Narrowed::Unique(results.pop().expect("length checked")),
        _ => Narrowed::Ambiguous(results),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_parsing_api::Span;

    fn interpretation(value: u8) -> PrefixInterpretation<u8, ()> {
        PrefixInterpretation {
            value,
            witness: (),
            consumed: Span::new(0, 1).expect("forward"),
            remainder: 1,
        }
    }

    #[test]
    fn narrowing_classifies_and_never_picks() {
        assert_eq!(narrow_relational::<u8, ()>(Vec::new()), Narrowed::NoResult);
        assert_eq!(
            narrow_relational(vec![interpretation(1)]),
            Narrowed::Unique(interpretation(1))
        );
        // Two results stay two results, in enumeration order. Nothing is chosen.
        assert_eq!(
            narrow_relational(vec![interpretation(1), interpretation(2)]),
            Narrowed::Ambiguous(vec![interpretation(1), interpretation(2)])
        );
    }
}
