//! Async content-addressed store trait, shaped to mirror HTTP semantics
//! (RFC 9110 `Range:` / `Content-Range:`) so the HTTP server can parse a
//! request header directly into a trait call, and an HTTP-backed
//! implementation can emit the same value back over the wire without
//! lossy translation.
//!
//! The trait surface uses only `async-trait` + `bytes` — no runtime types
//! — so it compiles to `wasm32-wasip1-threads`. Native and WASM backends
//! share the same API; implementations differ.
//!
//! Pieces in this module:
//! * [`ByteRange`] — request side, mirrors `Range: bytes=...` (closed,
//!   open-ended, suffix).
//! * [`ResolvedRange`] — response side, mirrors `Content-Range: bytes
//!   A-B/total`. Always concrete bounds.
//! * [`BlobInfo`] — `HEAD` response.
//! * [`AsyncContentStore`] — the trait. Four primaries (`get_range`,
//!   `head`, `insert`, `put`) maps 1:1 to HTTP `GET` (with `Range`),
//!   `HEAD`, `POST`, `PUT`. Convenience methods (`get`, `get_slice`,
//!   `contains`, `len`) delegate.
//! * [`AsyncBlobStore`] — `Arc<dyn AsyncContentStore<K>>` wrapper.
//! * [`AsyncOverSync`] — adapt any sync [`ContentStore`](crate::ContentStore)
//!   to the async trait.
//!
//! For a sync façade over an async store, see
//! [`BlockingBlobStore`](crate::BlockingBlobStore) under the `blocking`
//! feature.

use std::ops::Range;
use std::sync::Arc;

use async_trait::async_trait;
use bytes::Bytes;

use crate::range::{BlobInfo, ByteRange, ResolvedRange};
use crate::{ContentStore, StoreError};

// ---------------------------------------------------------------------------
// AsyncContentStore trait
// ---------------------------------------------------------------------------

/// Async content-addressed store.
///
/// Same three-layer read story as the sync [`ContentStore`]:
/// [`get_slice`](Self::get_slice) is the simple API (half-open range or
/// error); [`get_range`](Self::get_range) is the HTTP-shaped form on top
/// (built from `head` + `get_slice`); [`get`](Self::get) is the full-blob
/// convenience. **Override `get_slice` for native partial reads**;
/// `head` and `insert`/`put` are required.
///
/// `K: Send + Sync` is a trait-level bound so default impls can hold
/// `&K` across `.await` points.
#[async_trait]
pub trait AsyncContentStore<K: Send + Sync>: Send + Sync {
    /// Fetch a half-open byte range — the simple API.
    ///
    /// Errors: [`StoreError::NotFound`] (HTTP 404),
    /// [`StoreError::RangeNotSatisfiable`] (HTTP 416). `start >= end`
    /// returns empty after an existence check; `end > total` clamps
    /// silently.
    ///
    /// **Override here for native partial reads** — HTTP `Range:`,
    /// sqlite incremental I/O, FS `pread`. `get` and `get_range`
    /// automatically benefit.
    async fn get_slice(&self, key: &K, range: Range<u64>) -> Result<Bytes, StoreError>;

    /// Blob metadata without fetching the body — HTTP `HEAD`.
    ///
    /// Required: most backends can answer cheaply (HTTP HEAD, `SELECT
    /// length(...)`, `Vec::len`).
    async fn head(&self, key: &K) -> Result<BlobInfo, StoreError>;

    /// Hash and store; backend returns the derived key — HTTP `POST`.
    async fn insert(&self, data: Bytes) -> Result<K, StoreError>;

    /// Store at a specific key; backend may verify the hash — HTTP `PUT`.
    async fn put(&self, key: K, data: Bytes) -> Result<(), StoreError>;

    /// Fetch the full blob. Default: `head` + `get_slice(0..size)`.
    async fn get(&self, key: &K) -> Result<Bytes, StoreError> {
        let info = self.head(key).await?;
        self.get_slice(key, 0..info.size).await
    }

    /// Fetch a byte range — HTTP `GET` with a `Range:` header.
    ///
    /// Default: `head` to learn total size, resolve [`ByteRange`] to
    /// concrete bounds, then delegate to `get_slice`. Two backend hits
    /// per call; override on backends that can answer in one round trip
    /// (HTTP `Range:` returns body + `Content-Range` together).
    async fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<(Bytes, ResolvedRange), StoreError> {
        let info = self.head(key).await?;
        let resolved = range.resolve(info.size)?;
        let bytes = self
            .get_slice(key, resolved.start..resolved.end + 1)
            .await?;
        Ok((bytes, resolved))
    }

    /// Cheap existence check. Default uses `head`.
    async fn contains(&self, key: &K) -> Result<bool, StoreError> {
        match self.head(key).await {
            Ok(_) => Ok(true),
            Err(StoreError::NotFound) => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// Number of entries if cheaply available. Most remote backends return `None`.
    async fn len(&self) -> Option<usize> {
        None
    }
}

// ---------------------------------------------------------------------------
// AsyncBlobStore — Arc<dyn AsyncContentStore<K>> wrapper
// ---------------------------------------------------------------------------

/// `Arc<dyn AsyncContentStore<K>>` wrapper — cheap clone, dynamic dispatch.
///
/// Mirrors [`BlobStore`](crate::BlobStore) on the sync side. This is the
/// type that consumers (FUSE, axum handlers, the layered kernel cache)
/// hold by value.
pub struct AsyncBlobStore<K>(Arc<dyn AsyncContentStore<K>>);

impl<K: Send + Sync> AsyncBlobStore<K> {
    pub fn new(store: impl AsyncContentStore<K> + 'static) -> Self {
        Self(Arc::new(store))
    }

    pub fn from_arc(store: Arc<dyn AsyncContentStore<K>>) -> Self {
        Self(store)
    }

    /// Direct access to the underlying `Arc`. Useful when handing off to
    /// adapter types that hold the trait object directly (e.g.
    /// [`BlockingBlobStore`](crate::BlockingBlobStore)).
    pub fn as_arc(&self) -> &Arc<dyn AsyncContentStore<K>> {
        &self.0
    }
}

impl<K: Send + Sync> Clone for AsyncBlobStore<K> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

#[async_trait]
impl<K: Send + Sync> AsyncContentStore<K> for AsyncBlobStore<K> {
    async fn get_slice(&self, key: &K, range: Range<u64>) -> Result<Bytes, StoreError> {
        self.0.get_slice(key, range).await
    }
    async fn head(&self, key: &K) -> Result<BlobInfo, StoreError> {
        self.0.head(key).await
    }
    async fn insert(&self, data: Bytes) -> Result<K, StoreError> {
        self.0.insert(data).await
    }
    async fn put(&self, key: K, data: Bytes) -> Result<(), StoreError> {
        self.0.put(key, data).await
    }
    async fn get(&self, key: &K) -> Result<Bytes, StoreError> {
        self.0.get(key).await
    }
    async fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<(Bytes, ResolvedRange), StoreError> {
        self.0.get_range(key, range).await
    }
    async fn contains(&self, key: &K) -> Result<bool, StoreError> {
        self.0.contains(key).await
    }
    async fn len(&self) -> Option<usize> {
        self.0.len().await
    }
}

// ---------------------------------------------------------------------------
// AsyncOverSync — adapt any sync ContentStore as an AsyncContentStore
// ---------------------------------------------------------------------------

/// Adapter: present a sync [`ContentStore`] as an [`AsyncContentStore`].
///
/// All operations execute inline on the caller's task — non-blocking for
/// in-memory backends. For blocking backends (sqlite, FS) wrap this in a
/// `spawn_blocking` shim at the call site; we deliberately don't pull a
/// runtime into this crate's core path.
pub struct AsyncOverSync<S>(pub S);

impl<S> AsyncOverSync<S> {
    pub fn new(inner: S) -> Self {
        Self(inner)
    }

    pub fn inner(&self) -> &S {
        &self.0
    }

    pub fn into_inner(self) -> S {
        self.0
    }
}

#[async_trait]
impl<K, S> AsyncContentStore<K> for AsyncOverSync<S>
where
    K: Send + Sync + 'static,
    S: ContentStore<K> + 'static,
{
    async fn get_slice(&self, key: &K, range: Range<u64>) -> Result<Bytes, StoreError> {
        self.0.get_slice(key, range).map(Bytes::from)
    }

    async fn head(&self, key: &K) -> Result<BlobInfo, StoreError> {
        self.0.head(key).ok_or(StoreError::NotFound)
    }

    async fn insert(&self, data: Bytes) -> Result<K, StoreError> {
        self.0.insert(&data)
    }

    async fn put(&self, key: K, data: Bytes) -> Result<(), StoreError> {
        self.0.put(key, &data)
    }

    // Override get_range to pass through the sync trait's optimized one
    // (skips the head + get_slice round trip when the inner store can
    // serve them together — e.g. an HTTP backend with one Range: request).
    async fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<(Bytes, ResolvedRange), StoreError> {
        match self.0.get_range(key, range)? {
            Some((vec, resolved)) => Ok((Bytes::from(vec), resolved)),
            None => Err(StoreError::NotFound),
        }
    }

    async fn contains(&self, key: &K) -> Result<bool, StoreError> {
        Ok(self.0.contains(key))
    }

    async fn len(&self) -> Option<usize> {
        self.0.len()
    }
}

// Canonical lift: any BlobStore<K> is trivially an AsyncBlobStore<K>.
impl<K: Send + Sync + 'static> From<crate::BlobStore<K>> for AsyncBlobStore<K> {
    fn from(sync: crate::BlobStore<K>) -> Self {
        AsyncBlobStore::new(AsyncOverSync(sync))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // AsyncContentStore round-trip via AsyncOverSync. Range-type unit
    // tests live in `range.rs`.
    #[cfg(feature = "memory")]
    mod with_memory {
        use super::*;
        use crate::{BlobStore, SharedMemoryStore};
        use covalence_hash::O256;

        fn store() -> AsyncBlobStore<O256> {
            AsyncBlobStore::new(AsyncOverSync(SharedMemoryStore::new()))
        }

        #[tokio::test]
        async fn insert_and_get() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"hello")).await.unwrap();
            assert_eq!(s.get(&hash).await.unwrap(), b"hello"[..]);
        }

        #[tokio::test]
        async fn head_returns_size() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"abcdef")).await.unwrap();
            assert_eq!(s.head(&hash).await.unwrap(), BlobInfo { size: 6 });
        }

        #[tokio::test]
        async fn get_missing_is_not_found() {
            let s = store();
            let missing = O256::blob(b"nope");
            assert!(matches!(s.get(&missing).await, Err(StoreError::NotFound)));
            assert!(matches!(s.head(&missing).await, Err(StoreError::NotFound)));
            assert!(!s.contains(&missing).await.unwrap());
        }

        #[tokio::test]
        async fn get_range_closed() {
            let s = store();
            let hash = s
                .insert(Bytes::from_static(b"the quick brown fox"))
                .await
                .unwrap();
            let (bytes, resolved) = s
                .get_range(&hash, ByteRange::Closed { start: 4, end: 8 })
                .await
                .unwrap();
            assert_eq!(bytes, b"quick"[..]);
            assert_eq!(resolved.start, 4);
            assert_eq!(resolved.end, 8);
            assert_eq!(resolved.total, 19);
            assert_eq!(resolved.content_length(), 5);
        }

        #[tokio::test]
        async fn get_range_open_ended() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"0123456789")).await.unwrap();
            let (bytes, r) = s
                .get_range(&hash, ByteRange::From { start: 6 })
                .await
                .unwrap();
            assert_eq!(bytes, b"6789"[..]);
            assert_eq!((r.start, r.end, r.total), (6, 9, 10));
        }

        #[tokio::test]
        async fn get_range_suffix() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"0123456789")).await.unwrap();
            let (bytes, r) = s
                .get_range(&hash, ByteRange::Suffix { length: 3 })
                .await
                .unwrap();
            assert_eq!(bytes, b"789"[..]);
            assert_eq!((r.start, r.end, r.total), (7, 9, 10));
        }

        #[tokio::test]
        async fn get_range_unsatisfiable() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"hello")).await.unwrap();
            match s.get_range(&hash, ByteRange::From { start: 100 }).await {
                Err(StoreError::RangeNotSatisfiable { total }) => assert_eq!(total, 5),
                other => panic!("expected RangeNotSatisfiable, got {other:?}"),
            }
        }

        #[tokio::test]
        async fn get_slice_convenience() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"0123456789")).await.unwrap();
            assert_eq!(s.get_slice(&hash, 2..5).await.unwrap(), b"234"[..]);
        }

        #[tokio::test]
        async fn get_slice_empty_range() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"hello")).await.unwrap();
            assert_eq!(s.get_slice(&hash, 3..3).await.unwrap(), b""[..]);
        }

        #[tokio::test]
        async fn from_blob_store() {
            let sync = BlobStore::new(SharedMemoryStore::new());
            let async_store: AsyncBlobStore<O256> = sync.clone().into();
            let hash = sync.insert(b"shared").unwrap();
            assert_eq!(async_store.get(&hash).await.unwrap(), b"shared"[..]);
        }

        #[tokio::test]
        async fn arc_clone_shares() {
            let s = store();
            let hash = s.insert(Bytes::from_static(b"data")).await.unwrap();
            let twin = s.clone();
            assert_eq!(twin.get(&hash).await.unwrap(), b"data"[..]);
        }
    }
}
