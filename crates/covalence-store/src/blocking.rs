//! Sync façade over an [`AsyncContentStore`] via a tokio runtime [`Handle`].
//!
//! Mirrors [`covalence_kv::BlockingKv`](https://docs.rs/covalence-kv). The
//! caller supplies the handle; this crate doesn't pick a runtime for you.
//!
//! `Handle::block_on` blocks the current thread. Do not call from inside a
//! tokio runtime worker — use the async trait directly there.

use std::ops::Range;
use std::sync::Arc;

use bytes::Bytes;
use tokio::runtime::Handle;

use crate::StoreError;
use crate::async_store::{AsyncBlobStore, AsyncContentStore};
use crate::range::{BlobInfo, ByteRange, ResolvedRange};

/// Sync façade over an [`AsyncContentStore`].
///
/// Holds an `Arc<dyn AsyncContentStore<K>>` plus a tokio runtime handle.
/// Construct via [`new`](Self::new) (from any async impl) or
/// [`from_async`](Self::from_async) (from an existing [`AsyncBlobStore`]).
pub struct BlockingBlobStore<K: ?Sized + Send + Sync + 'static> {
    inner: Arc<dyn AsyncContentStore<K>>,
    handle: Handle,
}

impl<K: Send + Sync + 'static> BlockingBlobStore<K> {
    /// Wrap an async store + runtime handle.
    pub fn new(inner: impl AsyncContentStore<K> + 'static, handle: Handle) -> Self {
        Self {
            inner: Arc::new(inner),
            handle,
        }
    }

    /// Build from an existing [`AsyncBlobStore`] (cheap — shares the `Arc`).
    pub fn from_async(store: AsyncBlobStore<K>, handle: Handle) -> Self {
        Self {
            inner: Arc::clone(store.as_arc()),
            handle,
        }
    }

    /// The underlying async store.
    pub fn inner(&self) -> &Arc<dyn AsyncContentStore<K>> {
        &self.inner
    }

    pub fn get(&self, key: &K) -> Result<Bytes, StoreError>
    where
        K: Clone,
    {
        let inner = Arc::clone(&self.inner);
        let key = key.clone();
        self.handle.block_on(async move { inner.get(&key).await })
    }

    pub fn get_range(&self, key: &K, range: ByteRange) -> Result<(Bytes, ResolvedRange), StoreError>
    where
        K: Clone,
    {
        let inner = Arc::clone(&self.inner);
        let key = key.clone();
        self.handle
            .block_on(async move { inner.get_range(&key, range).await })
    }

    /// Half-open `Range<u64>` convenience — delegates to `get_range` with
    /// a closed [`ByteRange`].
    pub fn get_slice(&self, key: &K, range: Range<u64>) -> Result<Bytes, StoreError>
    where
        K: Clone,
    {
        let inner = Arc::clone(&self.inner);
        let key = key.clone();
        self.handle
            .block_on(async move { inner.get_slice(&key, range).await })
    }

    pub fn head(&self, key: &K) -> Result<BlobInfo, StoreError>
    where
        K: Clone,
    {
        let inner = Arc::clone(&self.inner);
        let key = key.clone();
        self.handle.block_on(async move { inner.head(&key).await })
    }

    pub fn put(&self, key: K, data: Bytes) -> Result<(), StoreError> {
        let inner = Arc::clone(&self.inner);
        self.handle
            .block_on(async move { inner.put(key, data).await })
    }

    pub fn insert(&self, data: Bytes) -> Result<K, StoreError> {
        let inner = Arc::clone(&self.inner);
        self.handle
            .block_on(async move { inner.insert(data).await })
    }

    pub fn contains(&self, key: &K) -> Result<bool, StoreError>
    where
        K: Clone,
    {
        let inner = Arc::clone(&self.inner);
        let key = key.clone();
        self.handle
            .block_on(async move { inner.contains(&key).await })
    }

    pub fn len(&self) -> Option<usize> {
        let inner = Arc::clone(&self.inner);
        self.handle.block_on(async move { inner.len().await })
    }
}

impl<K: Send + Sync + 'static> Clone for BlockingBlobStore<K> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
            handle: self.handle.clone(),
        }
    }
}

#[cfg(test)]
#[cfg(feature = "memory")]
mod tests {
    use super::*;
    use crate::SharedMemoryStore;
    use crate::async_store::AsyncOverSync;
    use covalence_hash::O256;

    fn store() -> BlockingBlobStore<O256> {
        let rt = tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap();
        let handle = rt.handle().clone();
        // Leak the runtime so the handle stays valid for the test scope.
        // In production, the caller owns the runtime.
        std::mem::forget(rt);
        BlockingBlobStore::new(AsyncOverSync(SharedMemoryStore::new()), handle)
    }

    #[test]
    fn round_trip() {
        let s = store();
        let hash = s.insert(Bytes::from_static(b"hello")).unwrap();
        assert_eq!(s.get(&hash).unwrap(), b"hello"[..]);
        assert_eq!(s.head(&hash).unwrap(), BlobInfo { size: 5 });
        assert!(s.contains(&hash).unwrap());
        assert_eq!(s.get_slice(&hash, 1..4).unwrap(), b"ell"[..]);
        let (bytes, resolved) = s.get_range(&hash, ByteRange::Suffix { length: 2 }).unwrap();
        assert_eq!(bytes, b"lo"[..]);
        assert_eq!(resolved.to_content_range(), "bytes 3-4/5");
    }

    #[test]
    fn missing_is_not_found() {
        let s = store();
        let missing = O256::blob(b"nope");
        assert!(matches!(s.get(&missing), Err(StoreError::NotFound)));
        assert!(!s.contains(&missing).unwrap());
    }
}
