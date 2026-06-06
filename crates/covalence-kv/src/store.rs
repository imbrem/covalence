use std::ops::Range;

use async_trait::async_trait;
use bytes::Bytes;

use crate::{Error, Meta, Result};

/// Async, fallible key-value store.
///
/// The canonical store trait. Designed for remote / untrusted backends
/// where every operation may fail with network, auth, or I/O errors.
///
/// Keys are slash-separated `&str`; backends sanitize at the boundary.
/// Bad keys produce [`Error::InvalidKey`] — a recoverable failure.
#[async_trait]
pub trait KvStore: Send + Sync {
    /// Fetch the full value at `key`.
    async fn get(&self, key: &str) -> Result<Bytes>;

    /// Fetch a byte range of the value at `key`.
    ///
    /// Default implementation fetches the full value via [`get`](Self::get)
    /// and slices it. Backends that support real ranged reads (HTTP `Range:`)
    /// should override this for efficiency.
    async fn get_range(&self, key: &str, range: Range<u64>) -> Result<Bytes> {
        let full = self.get(key).await?;
        let len = full.len() as u64;
        if range.start > range.end || range.end > len {
            return Err(Error::RangeOutOfBounds { range, len });
        }
        let start = range.start as usize;
        let end = range.end as usize;
        Ok(full.slice(start..end))
    }

    /// Store `value` under `key`, overwriting any existing value.
    async fn put(&self, key: &str, value: Bytes) -> Result<()>;

    /// Delete the value at `key`. Idempotent — succeeds whether or not the key existed.
    async fn delete(&self, key: &str) -> Result<()>;

    /// Fetch metadata for `key` without fetching the value.
    async fn head(&self, key: &str) -> Result<Meta>;
}
