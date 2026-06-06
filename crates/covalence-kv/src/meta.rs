use std::time::SystemTime;

/// Metadata about a value in the store, returned by [`KvStore::head`](crate::KvStore::head).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    /// Size of the value in bytes.
    pub size: u64,

    /// Last modification time, if the backend tracks it.
    pub modified: Option<SystemTime>,

    /// Backend-specific entity tag, useful for conditional reads.
    pub etag: Option<String>,
}
