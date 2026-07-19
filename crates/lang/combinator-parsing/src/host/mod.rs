//! Encoding T — host combinator values over three unrelated traits, with host
//! closures as continuations.
//!
//! This encoding is not data, so it is not property-generatable at the program
//! level; the syntax encoding is kept precisely because it is. What this encoding
//! buys instead is diagnostic completeness — `Diagnostic` is an associated type
//! and ordered choice takes a caller-supplied merge, so diagnostic shape stays a
//! caller decision — and foreign leaves: an existing PEG or CFG evaluator can sit
//! as a leaf of a combinator expression, which the syntax encoding cannot express
//! because its leaves must be primitive symbols its environment understands.
//!
//! # Three trait families, and the graph between them is empty
//!
//! The partial capability reuses the parsing API's existing `PartialPrefixParser`
//! unchanged. [`TotalPrefixParser`] and [`RelationalPrefixParser`] are defined here
//! because the parsing API's total and relational traits are whole-source and carry
//! no offset, so they cannot sequence.
//!
//! None of the three is a supertrait or a subtrait of any other, and there is no
//! blanket impl anywhere between them. This is not an omission to be tidied up
//! later. A supertrait relation would hand every total parser a non-match channel
//! by inheritance, and a blanket `impl<P: PartialPrefixParser> RelationalPrefixParser
//! for P` *is* the collapse these three modules exist to prevent. The refinement
//! chain between the capabilities lives entirely in `morphism`'s named adapters,
//! where each step is explicit about what it discards. The absence of impls here is
//! the enforcement mechanism, and the `compile_fail` doctests on the two traits
//! below pin it.
//!
//! # Per-capability operator sets
//!
//! | module | operators | why the difference |
//! |---|---|---|
//! | [`total`] | `Pure`, `Map`, `Ap`, `Bind` | no failure channel, so a choice operator is unstatable, not merely absent |
//! | [`partial`] | the above plus `Fail`, `OrderedChoice`, `MapErr`, `MapDiagnostic` | ordered choice needs a non-match channel *and* a diagnostic to carry forward |
//! | [`relational`] | `Pure`, `Void`, `Map`, `Ap`, `Bind`, `Union` | union needs neither, and has no diagnostic by permanent design |
//!
//! `OrderedChoice` and `Union` are different operators with different law tables,
//! not two spellings of one operator. Ordered choice commits and never evaluates
//! its second alternative after a match; union always evaluates both.
//!
//! # Bounded seams
//!
//! Two of the three capabilities need evaluator state that `parse_prefix` /
//! `parse_prefixes` cannot carry, and both solve it the same way: a *separate*
//! trait taking the state explicitly, with a single wrapper at the outside that
//! constructs it and is the only thing implementing the capability trait.
//! [`relational::BoundedRelational`] does this for result limits;
//! [`recursion::BoundedPartial`] does it for the partial capability's recursion
//! depth. Neither is a fourth capability, and neither disturbs the empty graph
//! between the three above.
//!
//! # Error and cursor conventions
//!
//! Sequencing combinators agree on [`CombinatorError`], which is idempotent so long
//! chains do not build an error tower, and they validate every sub-parser's reported
//! extent with [`check_step`]. A cursor violation is evaluator failure, never
//! ordinary non-match. Foreign leaves reach the convention through
//! [`partial::MapErr`] and [`partial::MapDiagnostic`] rather than by implementing
//! anything.

pub mod alphabet;
pub mod cursor;
pub mod partial;
pub mod recursion;
pub mod relational;
pub mod total;
pub mod witness;

pub use alphabet::{
    BytePartialParser, ByteRelationalParser, ByteTotalParser, TextPartialParser,
    TextRelationalParser, TextTotalParser,
};
pub use cursor::{CombinatorError, CursorViolation, SourceExtent, check_step, join};
pub use witness::{ChoiceWitness, SeqWitness, UnionWitness, reassociate_left, reassociate_right};

use core::marker::PhantomData;

use covalence_parsing_api::PrefixInterpretation;

/// The result of enumerating prefix interpretations.
///
/// Mirrors the parsing API's `RelationalParseResult` naming: there is no diagnostic
/// channel, because an empty enumeration proves no negative fact.
pub type PrefixEnumeration<V, W, E> = Result<Vec<PrefixInterpretation<V, W>>, E>;

/// Ties a combinator's otherwise-unused type parameters to its impl.
///
/// `fn(&S) -> T` rather than `(S, T)`: the combinator neither owns an `S` nor borrows
/// one for its own lifetime, so this marker must not imply drop obligations or make the
/// struct invariant in a source it merely reads.
pub type Marker<S, T> = PhantomData<fn(&S) -> T>;

/// Prefix parsing as a total function: every in-range start yields one interpretation.
///
/// There is no diagnostic and no `ParseAttempt`, mirroring A0015's whole-source
/// `TotalParser`. `Error` is evaluator failure only. A total parser has no non-match
/// channel, which is precisely why [`total`] has no choice operator: a second
/// alternative could never be consulted.
///
/// This is **not** a supertrait of, nor a subtrait of, `PartialPrefixParser`. The
/// refinement chain lives in `morphism`'s adapters; a supertrait relation would grant every
/// total parser a non-match channel by inheritance and reopen the collapse.
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::host::TotalPrefixParser;
/// use covalence_parsing_api::PartialPrefixParser;
/// fn assert_partial<P: PartialPrefixParser>(_: P) {}
/// // A total parser is not a partial parser: the chain is in the adapters, not the traits.
/// fn use_it<P: TotalPrefixParser>(parser: P) { assert_partial(parser); }
/// ```
///
/// `start > source_len` is a caller precondition, not a reported outcome.
pub trait TotalPrefixParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Error;

    fn parse_prefix_total(
        &self,
        source: &Self::Source,
        start: usize,
    ) -> Result<PrefixInterpretation<Self::Value, Self::Witness>, Self::Error>;
}

/// Prefix parsing as a relation.
///
/// Deliberately no `Diagnostic`: a relation has no notion of "the alternative failed", only
/// of what it enumerated. An empty vector proves no negative fact. Enumeration order is
/// meaningful data, so conformance compares as a sequence by default and as a multiset only
/// under an explicit caller policy.
///
/// Like [`TotalPrefixParser`], this stands in no sub- or supertrait relation to
/// `PartialPrefixParser`, and no blanket impl bridges them.
///
/// ```compile_fail,E0277
/// use covalence_combinator_parsing::host::RelationalPrefixParser;
/// use covalence_parsing_api::PartialPrefixParser;
/// fn assert_relational<P: RelationalPrefixParser>(_: P) {}
/// // A partial parser is not a relational parser; `WidenPartialToRelational` is, and it is
/// // named for the diagnostic it discards.
/// fn use_it<P: PartialPrefixParser>(parser: P) { assert_relational(parser); }
/// ```
pub trait RelationalPrefixParser {
    type Source: ?Sized;
    type Value;
    type Witness;
    type Error;

    fn parse_prefixes(
        &self,
        source: &Self::Source,
        start: usize,
    ) -> PrefixEnumeration<Self::Value, Self::Witness, Self::Error>;
}

// TODO(cov:lang.combinator-parsing.prefix-traits-to-a0015, minor): Promote
// TotalPrefixParser and RelationalPrefixParser into A0015 once a second consumer exists;
// A0015 currently has only whole-source total and relational traits.

// TODO(cov:lang.combinator-parsing.mode-generic-encoding, minor): A `Mode`-GAT encoding
// (one `Parser<M>` trait, `M::Outcome<T>` carrier) was evaluated and dropped: unsealed it
// lets a downstream mode implement both ordered choice and relational union, and sealed it
// collapses to the three `host/` traits. Reconsider only with a sealed `Mode`, a fourth
// concrete mode with a real consumer, and an axis-2 translation law against `host/`.

// TODO(cov:lang.combinator-parsing.repetition-combinators, minor): No many/some in either
// encoding; needs the nullable-repetition guard PegParser already has.
