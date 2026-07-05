use std::collections::HashMap;
use std::sync::RwLock;

use indexmap::IndexMap;

use covalence_hash::{IdentityBuildHasher, O256};

use crate::{BlobInfo, ContentStore, TaggedStore, slice_range};

// ---------------------------------------------------------------------------
// MemoryStore — single-threaded, &mut self, no locking overhead
// ---------------------------------------------------------------------------

/// In-memory content-addressed blob store backed by an [`IndexMap`].
///
/// Uses an identity hasher since [`O256`] keys are already BLAKE3 hashes —
/// their first 8 bytes are used directly as the bucket hash.
///
/// Blobs are stored once by content hash in the `IndexMap`. Tagged entries
/// are tracked in a separate `HashMap` mapping keyed hashes to `(tag, index)`.
///
/// For concurrent use, wrap in [`SharedMemoryStore`].
#[derive(Debug, Clone)]
pub struct MemoryStore {
    /// All blob data, keyed by content hash.
    blobs: IndexMap<O256, Vec<u8>, IdentityBuildHasher>,
    /// Tag index: keyed_hash → (tag, index into `blobs`).
    tags: HashMap<O256, (O256, usize), IdentityBuildHasher>,
}

impl MemoryStore {
    pub fn new() -> Self {
        Self {
            blobs: IndexMap::with_hasher(IdentityBuildHasher::default()),
            tags: HashMap::with_hasher(IdentityBuildHasher::default()),
        }
    }

    /// Get a blob by content hash (direct lookup). Does **not** resolve
    /// keyed-hash entries — use [`get_repr`](Self::get_repr) for that.
    pub fn get(&self, key: &O256) -> Option<&[u8]> {
        self.blobs.get(key).map(|v| v.as_slice())
    }

    /// Check whether a content hash exists in the store.
    pub fn contains(&self, key: &O256) -> bool {
        self.blobs.contains_key(key)
    }

    /// Insert a blob, returning its content hash `O256::blob(data)`.
    pub fn insert(&mut self, data: &[u8]) -> O256 {
        let hash = O256::blob(data);
        self.blobs.entry(hash).or_insert_with(|| data.to_vec());
        hash
    }

    /// Store a blob under a specific key.
    pub fn put(&mut self, key: O256, data: &[u8]) {
        self.blobs.entry(key).or_insert_with(|| data.to_vec());
    }

    /// Number of blobs stored (not counting tag index entries).
    pub fn len(&self) -> usize {
        self.blobs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.blobs.is_empty()
    }

    // --- Tagged operations ---

    /// Store a blob with a tag, returning the keyed hash `tag.tag(data)`.
    ///
    /// The blob is stored once by content hash; a tag-index entry maps the
    /// keyed hash to `(tag, blob_index)`.
    pub fn insert_tagged(&mut self, tag: O256, data: &[u8]) -> O256 {
        let content_hash = O256::blob(data);
        let index = match self.blobs.entry(content_hash) {
            indexmap::map::Entry::Occupied(e) => e.index(),
            indexmap::map::Entry::Vacant(e) => {
                let idx = e.index();
                e.insert(data.to_vec());
                idx
            }
        };
        let keyed_hash = tag.tag(data);
        self.tags.entry(keyed_hash).or_insert((tag, index));
        keyed_hash
    }

    /// Get blob data by any key — content hash *or* keyed hash.
    pub fn get_repr(&self, key: &O256) -> Option<&[u8]> {
        if let Some(data) = self.blobs.get(key) {
            return Some(data.as_slice());
        }
        if let Some(&(_, index)) = self.tags.get(key) {
            return self.blobs.get_index(index).map(|(_, v)| v.as_slice());
        }
        None
    }

    /// Get the tag for a keyed-hash entry. Returns `None` for plain blobs.
    pub fn get_tag(&self, key: &O256) -> Option<O256> {
        self.tags.get(key).map(|&(tag, _)| tag)
    }

    /// Get blob data given both tag and key.
    ///
    /// Checks the tag index first (validating the tag matches), then falls
    /// back to a direct content-hash lookup.
    pub fn get_repr_with(&self, tag: &O256, key: &O256) -> Option<&[u8]> {
        if let Some(&(t, index)) = self.tags.get(key)
            && &t == tag
        {
            return self.blobs.get_index(index).map(|(_, v)| v.as_slice());
        }
        self.blobs.get(key).map(|v| v.as_slice())
    }

    /// Get the tag given both tag and key (validates the stored tag matches).
    pub fn get_tag_with(&self, tag: &O256, key: &O256) -> Option<O256> {
        if let Some(&(t, _)) = self.tags.get(key)
            && &t == tag
        {
            return Some(t);
        }
        None
    }
}

impl Default for MemoryStore {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// SharedMemoryStore — concurrent via RwLock (no internal Arc)
// ---------------------------------------------------------------------------

/// Thread-safe wrapper around [`MemoryStore`].
///
/// Adds a [`RwLock`] for interior mutability so it can implement
/// [`ContentStore`] and [`TaggedStore`].
/// Wrap in [`BlobStore`](crate::BlobStore) or
/// [`TaggedBlobStore`](crate::TaggedBlobStore) for cheap cloning via Arc.
pub struct SharedMemoryStore(RwLock<MemoryStore>);

impl SharedMemoryStore {
    pub fn new() -> Self {
        Self(RwLock::new(MemoryStore::new()))
    }
}

impl Default for SharedMemoryStore {
    fn default() -> Self {
        Self::new()
    }
}

impl ContentStore<O256> for SharedMemoryStore {
    fn get(&self, key: &O256) -> Option<Vec<u8>> {
        self.0.read().unwrap().get(key).map(|s| s.to_vec())
    }

    fn put(&self, key: O256, data: &[u8]) -> Result<(), crate::StoreError> {
        self.0.write().unwrap().put(key, data);
        Ok(())
    }

    fn insert(&self, data: &[u8]) -> Result<O256, crate::StoreError> {
        Ok(self.0.write().unwrap().insert(data))
    }

    fn contains(&self, key: &O256) -> bool {
        self.0.read().unwrap().contains(key)
    }

    fn len(&self) -> Option<usize> {
        Some(self.0.read().unwrap().len())
    }

    fn head(&self, key: &O256) -> Option<BlobInfo> {
        self.0.read().unwrap().get(key).map(|s| BlobInfo {
            size: s.len() as u64,
        })
    }

    fn get_slice(
        &self,
        key: &O256,
        range: std::ops::Range<u64>,
    ) -> Result<Vec<u8>, crate::StoreError> {
        let store = self.0.read().unwrap();
        let Some(data) = store.get(key) else {
            return Err(crate::StoreError::NotFound);
        };
        // Slice while holding the borrow — final Vec is sized to the range,
        // not the whole blob.
        slice_range(data, range)
    }
}

impl TaggedStore<O256> for SharedMemoryStore {
    fn get_repr(&self, key: &O256) -> Option<Vec<u8>> {
        self.0.read().unwrap().get_repr(key).map(|s| s.to_vec())
    }

    fn get_tag(&self, key: &O256) -> Option<O256> {
        self.0.read().unwrap().get_tag(key)
    }

    fn insert_tagged(&self, tag: O256, data: &[u8]) -> Result<O256, crate::StoreError> {
        Ok(self.0.write().unwrap().insert_tagged(tag, data))
    }

    fn get_repr_with(&self, tag: &O256, key: &O256) -> Option<Vec<u8>> {
        self.0
            .read()
            .unwrap()
            .get_repr_with(tag, key)
            .map(|s| s.to_vec())
    }

    fn get_tag_with(&self, tag: &O256, key: &O256) -> Option<O256> {
        self.0.read().unwrap().get_tag_with(tag, key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BlobStore, TaggedBlobStore};

    #[test]
    fn memory_store_basics() {
        let mut store = MemoryStore::new();
        let hash = store.insert(b"hello");
        assert_eq!(store.get(&hash), Some(b"hello".as_slice()));
        assert!(store.contains(&hash));
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn content_addressed() {
        let mut store = MemoryStore::new();
        let h1 = store.insert(b"data");
        let h2 = store.insert(b"data");
        assert_eq!(h1, h2);
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn shared_head_and_get_slice() {
        let store = SharedMemoryStore::new();
        let hash = store.insert(b"0123456789").unwrap();
        assert_eq!(store.head(&hash), Some(BlobInfo { size: 10 }));
        assert_eq!(store.get_slice(&hash, 2..5).unwrap(), b"234");
        // Missing key.
        let missing = covalence_hash::O256::blob(b"missing");
        assert_eq!(store.head(&missing), None);
        assert!(matches!(
            store.get_slice(&missing, 0..1),
            Err(crate::StoreError::NotFound)
        ));
    }

    #[test]
    fn shared_store() {
        let store = SharedMemoryStore::new();
        let hash = store.insert(b"hello").unwrap();
        assert_eq!(ContentStore::get(&store, &hash), Some(b"hello".to_vec()));
        assert!(store.contains(&hash));
        assert_eq!(store.len(), Some(1));
    }

    #[test]
    fn blobstore_clone_shares() {
        let store = BlobStore::new(SharedMemoryStore::new());
        let hash = store.insert(b"shared").unwrap();
        let clone = store.clone();
        assert_eq!(clone.get(&hash), Some(b"shared".to_vec()));
    }

    // --- Tagged tests ---

    #[test]
    fn tagged_insert_and_get_repr() {
        let mut store = MemoryStore::new();
        let tag = O256::blob(b"my-tag");
        let key = store.insert_tagged(tag, b"payload");

        // keyed hash differs from content hash
        let content_hash = O256::blob(b"payload");
        assert_ne!(key, content_hash);

        // get_repr finds it by keyed hash
        assert_eq!(store.get_repr(&key), Some(b"payload".as_slice()));

        // get_repr also finds it by content hash (blob is stored under both)
        assert_eq!(store.get_repr(&content_hash), Some(b"payload".as_slice()));

        // plain get does NOT find it by keyed hash
        assert_eq!(store.get(&key), None);

        // plain get DOES find it by content hash (the IndexMap key)
        assert_eq!(store.get(&content_hash), Some(b"payload".as_slice()));
    }

    #[test]
    fn tagged_get_tag() {
        let mut store = MemoryStore::new();
        let tag = O256::blob(b"my-tag");
        let key = store.insert_tagged(tag, b"data");

        assert_eq!(store.get_tag(&key), Some(tag));

        // plain blob has no tag
        let plain = store.insert(b"plain");
        assert_eq!(store.get_tag(&plain), None);
    }

    #[test]
    fn tagged_get_with() {
        let mut store = MemoryStore::new();
        let tag = O256::blob(b"my-tag");
        let key = store.insert_tagged(tag, b"data");

        // get_repr_with with correct tag
        assert_eq!(store.get_repr_with(&tag, &key), Some(b"data".as_slice()));

        // get_repr_with with wrong tag falls back to direct lookup (misses)
        let wrong = O256::blob(b"wrong");
        assert_eq!(store.get_repr_with(&wrong, &key), None);

        // get_tag_with validates the tag
        assert_eq!(store.get_tag_with(&tag, &key), Some(tag));
        assert_eq!(store.get_tag_with(&wrong, &key), None);
    }

    #[test]
    fn tagged_dedup() {
        let mut store = MemoryStore::new();
        let tag1 = O256::blob(b"tag-1");
        let tag2 = O256::blob(b"tag-2");

        let k1 = store.insert_tagged(tag1, b"same-data");
        let k2 = store.insert_tagged(tag2, b"same-data");

        // Different tags produce different keyed hashes
        assert_ne!(k1, k2);

        // But only one blob is stored
        assert_eq!(store.len(), 1);

        // Both resolve to the same data
        assert_eq!(store.get_repr(&k1), Some(b"same-data".as_slice()));
        assert_eq!(store.get_repr(&k2), Some(b"same-data".as_slice()));
    }

    #[test]
    fn tagged_and_plain_coexist() {
        let mut store = MemoryStore::new();
        let plain_hash = store.insert(b"shared-data");
        let tag = O256::blob(b"my-tag");
        let keyed = store.insert_tagged(tag, b"shared-data");

        // Still only one blob stored
        assert_eq!(store.len(), 1);

        // Plain get works for content hash
        assert_eq!(store.get(&plain_hash), Some(b"shared-data".as_slice()));

        // Plain get does NOT work for keyed hash
        assert_eq!(store.get(&keyed), None);

        // get_repr works for both
        assert_eq!(store.get_repr(&plain_hash), Some(b"shared-data".as_slice()));
        assert_eq!(store.get_repr(&keyed), Some(b"shared-data".as_slice()));
    }

    #[test]
    fn shared_tagged_store() {
        let store = SharedMemoryStore::new();
        let tag = O256::blob(b"tag");

        let key = store.insert_tagged(tag, b"hello").unwrap();
        assert_eq!(store.get_repr(&key), Some(b"hello".to_vec()));
        assert_eq!(store.get_tag(&key), Some(tag));

        // plain get misses keyed hash
        assert_eq!(ContentStore::get(&store, &key), None);
    }

    #[test]
    fn tagged_blobstore() {
        let store = TaggedBlobStore::new(SharedMemoryStore::new());
        let tag = O256::blob(b"tag");

        let key = store.insert_tagged(tag, b"world").unwrap();
        assert_eq!(store.get_repr(&key), Some(b"world".to_vec()));
        assert_eq!(store.get_tag(&key), Some(tag));

        // ContentStore::get misses keyed hash
        assert_eq!(ContentStore::get(&store, &key), None);

        // ContentStore::insert works normally
        let plain = ContentStore::insert(&store, b"plain").unwrap();
        assert_eq!(ContentStore::get(&store, &plain), Some(b"plain".to_vec()));
    }

    #[test]
    fn tagged_blobstore_converts_to_blobstore() {
        let tagged = TaggedBlobStore::new(SharedMemoryStore::new());
        let hash = ContentStore::insert(&tagged, b"data").unwrap();

        let blob_store: BlobStore<O256> = tagged.into();
        assert_eq!(blob_store.get(&hash), Some(b"data".to_vec()));
    }
}
