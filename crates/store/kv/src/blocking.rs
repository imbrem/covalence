//! Blocking wrapper around the async [`KvStore`] trait.
//!
//! Drives the underlying async calls via a tokio runtime [`Handle`]. The
//! caller supplies the handle; this crate doesn't pick a runtime for you.
//!
//! `Handle::block_on` blocks the current thread. Do not call from inside
//! a tokio runtime — use the async trait directly there.

use std::ops::Range;
use std::sync::Arc;

use bytes::Bytes;
use tokio::runtime::Handle;

use crate::{KvStore, Meta, Result};

/// Sync façade over an async [`KvStore`].
pub struct BlockingKv {
    inner: Arc<dyn KvStore>,
    handle: Handle,
}

impl BlockingKv {
    pub fn new(inner: Arc<dyn KvStore>, handle: Handle) -> Self {
        Self { inner, handle }
    }

    /// The underlying async store.
    pub fn inner(&self) -> &Arc<dyn KvStore> {
        &self.inner
    }

    pub fn get(&self, key: &str) -> Result<Bytes> {
        let inner = self.inner.clone();
        let key = key.to_string();
        self.handle.block_on(async move { inner.get(&key).await })
    }

    pub fn get_range(&self, key: &str, range: Range<u64>) -> Result<Bytes> {
        let inner = self.inner.clone();
        let key = key.to_string();
        self.handle
            .block_on(async move { inner.get_range(&key, range).await })
    }

    pub fn put(&self, key: &str, value: Bytes) -> Result<()> {
        let inner = self.inner.clone();
        let key = key.to_string();
        self.handle
            .block_on(async move { inner.put(&key, value).await })
    }

    pub fn delete(&self, key: &str) -> Result<()> {
        let inner = self.inner.clone();
        let key = key.to_string();
        self.handle
            .block_on(async move { inner.delete(&key).await })
    }

    pub fn head(&self, key: &str) -> Result<Meta> {
        let inner = self.inner.clone();
        let key = key.to_string();
        self.handle.block_on(async move { inner.head(&key).await })
    }
}

impl Clone for BlockingKv {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
            handle: self.handle.clone(),
        }
    }
}
