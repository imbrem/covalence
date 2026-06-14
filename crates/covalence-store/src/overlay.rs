//! Store combinators: read-fallback overlay and size-based write routing.
//!
//! Neither type is content-aware — they compose any
//! [`ContentStore<K>`](crate::ContentStore) layers behind the same
//! [`BlobStore<K>`](crate::BlobStore) facade. They are the native,
//! hand-wired analogue of a [`StoreManifest`](crate::metadata)
//! `depends_on` graph.
//!
//! - [`OverlayStore`] — reads try each layer in order, first hit wins;
//!   writes go to a single writable primary.
//! - [`SizeRouter`] — writes route by blob size (small vs. large);
//!   reads consult both layers.

use crate::{BlobInfo, BlobStore, ByteRange, ContentStore, ResolvedRange, StoreError};

/// Read-fallback / write-routing overlay over a stack of stores.
///
/// Reads consult `primary` first, then each store in `fallbacks` in
/// order, and the first hit wins. Writes (`put`/`insert`) always go to
/// `primary` — the single writable layer. Fallbacks are read-only as far
/// as this store is concerned.
///
/// Mirrors [`StoreManifest`](crate::metadata) `depends_on`: a missing or
/// empty fallback is survivable, not a correctness bug.
pub struct OverlayStore<K> {
    primary: BlobStore<K>,
    fallbacks: Vec<BlobStore<K>>,
}

impl<K: Send + Sync> OverlayStore<K> {
    /// Build an overlay with a writable `primary` and ordered read-only
    /// `fallbacks`.
    pub fn new(primary: BlobStore<K>, fallbacks: Vec<BlobStore<K>>) -> Self {
        Self { primary, fallbacks }
    }

    /// Add another read-only fallback at the end of the chain.
    pub fn push_fallback(&mut self, store: BlobStore<K>) {
        self.fallbacks.push(store);
    }

    /// Iterate every layer in read order: primary, then fallbacks.
    fn layers(&self) -> impl Iterator<Item = &BlobStore<K>> {
        std::iter::once(&self.primary).chain(self.fallbacks.iter())
    }
}

impl<K: Send + Sync> ContentStore<K> for OverlayStore<K> {
    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        self.primary.put(key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        self.primary.insert(data)
    }

    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.layers().find_map(|s| s.get(key))
    }

    fn get_slice(&self, key: &K, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        // First layer that has the key serves the slice. A layer that
        // *has* the key but rejects the range (RangeNotSatisfiable)
        // surfaces that error rather than masking it with a later layer.
        for store in self.layers() {
            match store.get_slice(key, range.clone()) {
                Err(StoreError::NotFound) => continue,
                other => return other,
            }
        }
        Err(StoreError::NotFound)
    }

    fn head(&self, key: &K) -> Option<BlobInfo> {
        self.layers().find_map(|s| s.head(key))
    }

    fn contains(&self, key: &K) -> bool {
        self.layers().any(|s| s.contains(key))
    }

    fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<Option<(Vec<u8>, ResolvedRange)>, StoreError> {
        for store in self.layers() {
            match store.get_range(key, range) {
                Ok(None) => continue,
                other => return other,
            }
        }
        Ok(None)
    }
}

/// Default size threshold (1 MiB): blobs `>=` this go to the large
/// store, smaller ones to the small store.
pub const DEFAULT_SIZE_THRESHOLD: u64 = 1 << 20;

/// Routes writes by blob size; reads consult both layers.
///
/// `insert`/`put` send blobs of `threshold` bytes or larger to `large`
/// and everything else to `small`. Reads check `small` first, then
/// `large`. Typical wiring: `small` = SQLite (`WITHOUT ROWID`, native
/// `substr` ranges), `large` = a raw loose-file store (OS page cache,
/// cheap `pread`).
pub struct SizeRouter<K> {
    small: BlobStore<K>,
    large: BlobStore<K>,
    threshold: u64,
}

impl<K: Send + Sync> SizeRouter<K> {
    /// Build a router with an explicit byte threshold.
    pub fn new(small: BlobStore<K>, large: BlobStore<K>, threshold: u64) -> Self {
        Self {
            small,
            large,
            threshold,
        }
    }

    /// Build a router with [`DEFAULT_SIZE_THRESHOLD`].
    pub fn with_default_threshold(small: BlobStore<K>, large: BlobStore<K>) -> Self {
        Self::new(small, large, DEFAULT_SIZE_THRESHOLD)
    }

    /// The store a blob of `len` bytes is written to.
    fn route(&self, len: usize) -> &BlobStore<K> {
        if len as u64 >= self.threshold {
            &self.large
        } else {
            &self.small
        }
    }
}

impl<K: Send + Sync> ContentStore<K> for SizeRouter<K> {
    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        self.route(data.len()).put(key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        self.route(data.len()).insert(data)
    }

    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.small.get(key).or_else(|| self.large.get(key))
    }

    fn get_slice(&self, key: &K, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        match self.small.get_slice(key, range.clone()) {
            Err(StoreError::NotFound) => self.large.get_slice(key, range),
            other => other,
        }
    }

    fn head(&self, key: &K) -> Option<BlobInfo> {
        self.small.head(key).or_else(|| self.large.head(key))
    }

    fn contains(&self, key: &K) -> bool {
        self.small.contains(key) || self.large.contains(key)
    }

    fn get_range(
        &self,
        key: &K,
        range: ByteRange,
    ) -> Result<Option<(Vec<u8>, ResolvedRange)>, StoreError> {
        match self.small.get_range(key, range)? {
            Some(hit) => Ok(Some(hit)),
            None => self.large.get_range(key, range),
        }
    }
}

#[cfg(all(test, feature = "memory"))]
mod tests {
    use super::*;
    use crate::SharedMemoryStore;
    use covalence_hash::O256;

    fn mem() -> BlobStore<O256> {
        BlobStore::new(SharedMemoryStore::new())
    }

    #[test]
    fn overlay_reads_fall_through() {
        let primary = mem();
        let backing = mem();
        let key = backing.insert(b"from backing").unwrap();

        let overlay = OverlayStore::new(primary, vec![backing]);
        assert_eq!(overlay.get(&key).unwrap(), b"from backing");
        assert!(overlay.contains(&key));
        assert_eq!(overlay.head(&key).unwrap().size, 12);
    }

    #[test]
    fn overlay_primary_wins_and_writes_local() {
        let primary = mem();
        let backing = mem();
        // Same content hashes identically in both layers; insert into the
        // backing layer, then prove writes land in primary only.
        let overlay = OverlayStore::new(primary.clone(), vec![backing.clone()]);
        let key = overlay.insert(b"written").unwrap();
        assert!(primary.contains(&key));
        assert!(!backing.contains(&key));
        assert_eq!(overlay.get(&key).unwrap(), b"written");
    }

    #[test]
    fn overlay_miss_is_none() {
        let overlay = OverlayStore::new(mem(), vec![mem()]);
        let absent = O256::blob(b"nope");
        assert!(overlay.get(&absent).is_none());
        assert!(!overlay.contains(&absent));
        assert!(matches!(
            overlay.get_slice(&absent, 0..4),
            Err(StoreError::NotFound)
        ));
    }

    #[test]
    fn size_router_routes_by_size() {
        let small = mem();
        let large = mem();
        let router = SizeRouter::new(small.clone(), large.clone(), 8);

        let s = router.insert(b"tiny").unwrap(); // 4 bytes -> small
        let l = router.insert(b"a much larger blob").unwrap(); // >=8 -> large

        assert!(small.contains(&s) && !large.contains(&s));
        assert!(large.contains(&l) && !small.contains(&l));

        // Reads find both regardless of which layer holds them.
        assert_eq!(router.get(&s).unwrap(), b"tiny");
        assert_eq!(router.get(&l).unwrap(), b"a much larger blob");
        assert_eq!(router.get_slice(&l, 0..1).unwrap(), b"a");
    }
}
