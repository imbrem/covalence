use std::ops::Range;

/// Errors from key-value store operations.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// The requested key does not exist in the store.
    #[error("key not found: {key:?}")]
    NotFound { key: String },

    /// The key was rejected by the backend's sanitization rules.
    ///
    /// Recoverable: the caller may retry with a corrected key.
    #[error("invalid key {key:?}: {reason}")]
    InvalidKey { key: String, reason: String },

    /// A range read requested bytes outside the value.
    #[error("range {}..{} out of bounds for value of length {len}", range.start, range.end)]
    RangeOutOfBounds { range: Range<u64>, len: u64 },

    /// Authentication or authorization failure at the backend.
    #[error("auth failure: {0}")]
    Auth(String),

    /// Underlying backend I/O or transport error.
    #[error("backend error: {0}")]
    Backend(String),
}
