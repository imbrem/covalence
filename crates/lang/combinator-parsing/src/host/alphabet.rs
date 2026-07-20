//! Ergonomic on-ramps for the two source carriers house consumers actually use.
//!
//! These are aliases, not new types: byte parsers are over `[u8]` and text parsers are over
//! `[UnicodeScalar]`, mirroring `peg-parsing`'s `BytePegParser` / `TextPegParser`.
//!
//! The two carriers are kept apart deliberately. Offsets in one are not offsets in the
//! other, so a span produced by a byte parser and a span produced by a scalar parser for the
//! "same" source are not comparable; crossing between them goes through the parsing API's
//! `DecodedText::byte_span` and never through `==`. That is also why there is no
//! `SourceExtent for str`.

use covalence_logic_api::UnicodeScalar;

use crate::host::partial::DynPartial;
use crate::host::relational::DynRelational;
use crate::host::total::DynTotal;

/// A type-erased partial byte parser.
pub type BytePartialParser<'p, V, W, D, E> = DynPartial<'p, [u8], V, W, D, E>;

/// A type-erased partial text parser over abstract Unicode scalars.
pub type TextPartialParser<'p, V, W, D, E> = DynPartial<'p, [UnicodeScalar], V, W, D, E>;

/// A type-erased total byte parser.
pub type ByteTotalParser<'p, V, W, E> = DynTotal<'p, [u8], V, W, E>;

/// A type-erased total text parser over abstract Unicode scalars.
pub type TextTotalParser<'p, V, W, E> = DynTotal<'p, [UnicodeScalar], V, W, E>;

/// A type-erased relational byte combinator. Evaluating one still requires wrapping it in a
/// [`RelationalEvaluation`](crate::host::relational::RelationalEvaluation) with the caller's
/// result limits.
pub type ByteRelationalParser<'p, V, W, E> = DynRelational<'p, [u8], V, W, E>;

/// A type-erased relational text combinator over abstract Unicode scalars.
pub type TextRelationalParser<'p, V, W, E> = DynRelational<'p, [UnicodeScalar], V, W, E>;
