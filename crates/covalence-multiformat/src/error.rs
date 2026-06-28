use covalence_parse::leb128::DecodeError;

use crate::cid::Cid;

/// Failures decoding a CID, a multibase string, or a [`DerivationFact`] body.
///
/// [`DerivationFact`]: crate::DerivationFact
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected end of input")]
    Eof,
    #[error("leb128: {0}")]
    Leb(#[from] DecodeError),
    #[error("unsupported multihash code {0:#x} (only blake3 = 0x1e is supported)")]
    UnsupportedMultihash(u64),
    #[error("unexpected digest length {0} (expected 32)")]
    BadDigestLength(u64),
    #[error("unsupported format version {0}")]
    BadVersion(u64),
    #[error("invalid multibase prefix {0:?} (expected 'f' = base16-lower)")]
    BadMultibase(char),
    #[error("empty multibase string")]
    EmptyMultibase,
    #[error("invalid base16 encoding")]
    BadHex,
    #[error("{0} trailing byte(s) after value")]
    Trailing(usize),
}

/// Failures admitting a fact: the recursive constraint check over the store.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CheckError {
    #[error("unsatisfied citation: {0} not in store")]
    MissingCitation(Cid),
    #[error("hash mismatch: stored body for {0} does not hash to it")]
    HashMismatch(Cid),
    #[error("malformed body for {0}: {1}")]
    Malformed(Cid, ParseError),
}
