//! Evidence recorded by host combinators.
//!
//! Witnesses are untrusted data. They record what an evaluation did, and grant no theorem
//! authority whatsoever.
//!
//! The two nondeterminism witnesses are separate types on purpose. [`ChoiceWitness`] carries
//! a bounded *negative* control record — the first alternative's diagnostic — because
//! ordered choice is a deterministic evaluation that consulted the second alternative only
//! after the first declined. [`UnionWitness`] carries no such record, because a relational
//! union asserts nothing about the branch that did not produce *this* result: that branch
//! may well have produced results of its own. A witness cannot be reinterpreted across
//! capabilities.

/// Sequencing evidence.
///
/// `split` is the offset where the second parser was invoked. It is redundant with the
/// sub-witnesses' own extents and is retained anyway for two reasons: the bind-associativity
/// reassociation isomorphism below is not definable without it, and a checker can validate a
/// witness without re-deriving the interior boundary.
///
/// Shared across all three capabilities. One caveat, and it is real: in the relational
/// capability a single `first` witness is cloned into many results (hence the `Clone` bound
/// there), so a consumer cannot tell from the type alone whether `first` is exclusive or
/// shared evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeqWitness<A, B> {
    pub first: A,
    pub second: B,
    pub split: usize,
}

/// Evidence for **ordered** choice.
///
/// `Second` retains the first alternative's diagnostic: a control fact about a deterministic
/// evaluation, namely that the first alternative was consulted at this offset and declined.
/// It is a record of control flow, not a proof that the first alternative *cannot* match.
///
/// Deliberately not [`UnionWitness`], and deliberately not convertible to one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChoiceWitness<A, B, D> {
    First(A),
    Second { first_diagnostic: D, witness: B },
}

/// Evidence for **relational** union: which side produced *this one* interpretation.
///
/// It asserts nothing about the other side, which may have produced further interpretations
/// of its own. There is no diagnostic here and there never will be one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnionWitness<A, B> {
    Left(A),
    Right(B),
}

/// The explicit isomorphism that monadic associativity holds only up to.
///
/// Bind-associativity is not statable on the nose in any encoding, because the two sides
/// have different witness *types*: `SeqWitness<SeqWitness<A, B>, C>` against
/// `SeqWitness<A, SeqWitness<B, C>>`. This function and its inverse are the only bridge, and
/// they are only trustworthy because they are total, information-preserving, and covered by
/// a round-trip test — a `reassociate` that dropped a `split` would make the associativity
/// law pass vacuously.
pub fn reassociate_right<A, B, C>(
    witness: SeqWitness<SeqWitness<A, B>, C>,
) -> SeqWitness<A, SeqWitness<B, C>> {
    let SeqWitness {
        first: inner,
        second: third,
        split: outer_split,
    } = witness;
    SeqWitness {
        first: inner.first,
        second: SeqWitness {
            first: inner.second,
            second: third,
            split: outer_split,
        },
        split: inner.split,
    }
}

/// The inverse of [`reassociate_right`].
///
/// Required, not optional: without a verified round trip the associativity law it serves is
/// worthless.
pub fn reassociate_left<A, B, C>(
    witness: SeqWitness<A, SeqWitness<B, C>>,
) -> SeqWitness<SeqWitness<A, B>, C> {
    let SeqWitness {
        first,
        second: inner,
        split: outer_split,
    } = witness;
    SeqWitness {
        first: SeqWitness {
            first,
            second: inner.first,
            split: outer_split,
        },
        second: inner.second,
        split: inner.split,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn left_nested() -> SeqWitness<SeqWitness<&'static str, &'static str>, &'static str> {
        SeqWitness {
            first: SeqWitness {
                first: "a",
                second: "b",
                split: 3,
            },
            second: "c",
            split: 7,
        }
    }

    fn right_nested() -> SeqWitness<&'static str, SeqWitness<&'static str, &'static str>> {
        SeqWitness {
            first: "a",
            second: SeqWitness {
                first: "b",
                second: "c",
                split: 7,
            },
            split: 3,
        }
    }

    #[test]
    fn reassociation_round_trips_from_the_left() {
        assert_eq!(
            reassociate_left(reassociate_right(left_nested())),
            left_nested()
        );
    }

    #[test]
    fn reassociation_round_trips_from_the_right() {
        assert_eq!(
            reassociate_right(reassociate_left(right_nested())),
            right_nested()
        );
    }

    /// The point of the round-trip tests: both split offsets survive, in both directions. A
    /// `reassociate` that dropped one would still round-trip on a fixture whose splits were
    /// equal, so the fixtures above use distinct splits deliberately.
    #[test]
    fn reassociation_preserves_both_split_offsets() {
        assert_eq!(reassociate_right(left_nested()), right_nested());
        assert_eq!(reassociate_left(right_nested()), left_nested());
    }
}
