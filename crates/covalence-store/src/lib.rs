use std::sync::Arc;

pub use covalence_hash::O256;

mod object;
pub use object::{
    AnyObject, Blob, Commit, KeyedObjectStore, Object, ObjectKind, ObjectStore, Tag, Tree,
};

// ---------------------------------------------------------------------------
// TreeStore — POSIX-style virtual filesystem trait
// ---------------------------------------------------------------------------

/// Hierarchical store of byte values addressed by raw byte keys, with
/// named child subtrees — structurally a POSIX-style virtual filesystem
/// (or a collection of them, via [`ns`](Self::ns)).
///
/// Designed to be object-safe for use behind `Arc<dyn TreeStore>`.
/// Keys and values are raw byte slices — type tagging (if needed)
/// is the caller's responsibility.
///
/// Distinct from [`covalence_kv::KvStore`]: that's a flat key/value
/// blob store (S3-shaped). This is a tree of namespaces with read
/// tracking, suited to kernel-internal scaffolding.
pub trait TreeStore: Send + Sync {
    /// Insert or overwrite a value.
    fn set(&self, key: &[u8], value: &[u8]);

    /// Look up a value by key.
    fn get(&self, key: &[u8]) -> Option<Vec<u8>>;

    /// Mark a key as touched (set was called with this bare key).
    fn touch(&self, key: &[u8]);

    /// Check whether a key has been touched.
    fn touched(&self, key: &[u8]) -> bool;

    /// Navigate to a child namespace. Returns the same child on
    /// repeated calls with the same key (shared state).
    fn ns(&self, key: &[u8]) -> Arc<dyn TreeStore>;

    /// Duplicate this handle (same underlying data).
    fn dup(&self) -> Arc<dyn TreeStore>;
}

/// Errors from store operations.
#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("store I/O error: {0}")]
    Io(String),

    #[error("type mismatch: expected {expected:?}, got {got:?}")]
    KindMismatch {
        expected: ObjectKind,
        got: ObjectKind,
    },
}

/// Content-addressed store trait.
///
/// Self-contained interface for content-addressed storage. Designed to be
/// object-safe for use behind `Arc<dyn ContentStore<K>>`.
pub trait ContentStore<K>: Send + Sync {
    /// Retrieve data by key.
    fn get(&self, key: &K) -> Option<Vec<u8>>;

    /// Store data under the given key.
    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError>;

    /// Hash and store data, returning the content key.
    fn insert(&self, data: &[u8]) -> Result<K, StoreError>;

    /// Check whether a key exists. Default checks via `get`.
    fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Number of entries in the store, if cheaply available.
    fn len(&self) -> Option<usize> {
        None
    }
}

// ---------------------------------------------------------------------------
// BlobStore<K> — Arc<dyn ContentStore<K>> wrapper
// ---------------------------------------------------------------------------

/// Content-addressed blob store.
///
/// Wraps any [`ContentStore<K>`] implementation behind an `Arc`,
/// making clone cheap and dispatch dynamic.
#[derive(Clone)]
pub struct BlobStore<K>(Arc<dyn ContentStore<K>>);

impl<K> BlobStore<K> {
    /// Wrap any `ContentStore<K>` implementation.
    pub fn new(store: impl ContentStore<K> + 'static) -> Self {
        Self(Arc::new(store))
    }
}

impl<K: Send + Sync> ContentStore<K> for BlobStore<K> {
    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get(key)
    }

    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        self.0.put(key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert(data)
    }

    fn contains(&self, key: &K) -> bool {
        self.0.contains(key)
    }

    fn len(&self) -> Option<usize> {
        self.0.len()
    }
}

// ---------------------------------------------------------------------------
// TaggedStore — content-addressed storage with keyed-hash tags
// ---------------------------------------------------------------------------

/// Tagged content store — extends content-addressed storage with keyed-hash tags.
///
/// Generic over key type `K` and tag type `T` (defaults to `K`).
/// Given `insert_tagged(tag, blob)`, the implementation computes a key from the
/// tag and blob data. The blob is stored once; a tag index maps computed keys
/// to `(tag, blob)` pairs.
///
/// The plain [`ContentStore::get`] returns data only for content-addressed keys
/// (inserted via [`ContentStore::insert`] / [`ContentStore::put`]), **not** for
/// tagged keys. Use [`get_repr`](TaggedStore::get_repr) to retrieve data
/// by either kind of key.
pub trait TaggedStore<K, T = K>: ContentStore<K> {
    /// Get blob data by any key (content hash or tagged key).
    fn get_repr(&self, key: &K) -> Option<Vec<u8>>;

    /// Get the tag for a tagged entry. Returns `None` for plain blobs.
    fn get_tag(&self, key: &K) -> Option<T>;

    /// Store a blob with a tag, returning the derived key.
    fn insert_tagged(&self, tag: T, data: &[u8]) -> Result<K, StoreError>;

    /// Get blob data given both tag and key (potentially more efficient).
    fn get_repr_with(&self, tag: &T, key: &K) -> Option<Vec<u8>> {
        let _ = tag;
        self.get_repr(key)
    }

    /// Get the tag given both tag and key (validates the tag matches).
    fn get_tag_with(&self, tag: &T, key: &K) -> Option<T> {
        let _ = tag;
        self.get_tag(key)
    }
}

// ---------------------------------------------------------------------------
// TaggedBlobStore — Arc<dyn TaggedStore> wrapper
// ---------------------------------------------------------------------------

/// Tagged blob store — wraps a [`TaggedStore`] behind an `Arc`.
///
/// Like [`BlobStore`], but also exposes tagged operations.
/// Converts to `BlobStore<K>` via [`From`].
#[derive(Clone)]
pub struct TaggedBlobStore<K, T = K>(Arc<dyn TaggedStore<K, T>>);

impl<K, T> TaggedBlobStore<K, T> {
    /// Wrap any `TaggedStore` implementation.
    pub fn new(store: impl TaggedStore<K, T> + 'static) -> Self {
        Self(Arc::new(store))
    }

    pub fn get_repr(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr(key)
    }

    pub fn get_tag(&self, key: &K) -> Option<T> {
        self.0.get_tag(key)
    }

    pub fn insert_tagged(&self, tag: T, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert_tagged(tag, data)
    }

    pub fn get_repr_with(&self, tag: &T, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr_with(tag, key)
    }

    pub fn get_tag_with(&self, tag: &T, key: &K) -> Option<T> {
        self.0.get_tag_with(tag, key)
    }
}

impl<K: Send + Sync, T: Send + Sync> ContentStore<K> for TaggedBlobStore<K, T> {
    fn get(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get(key)
    }

    fn put(&self, key: K, data: &[u8]) -> Result<(), StoreError> {
        self.0.put(key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert(data)
    }

    fn contains(&self, key: &K) -> bool {
        self.0.contains(key)
    }

    fn len(&self) -> Option<usize> {
        self.0.len()
    }
}

impl<K: Send + Sync, T: Send + Sync> TaggedStore<K, T> for TaggedBlobStore<K, T> {
    fn get_repr(&self, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr(key)
    }

    fn get_tag(&self, key: &K) -> Option<T> {
        self.0.get_tag(key)
    }

    fn insert_tagged(&self, tag: T, data: &[u8]) -> Result<K, StoreError> {
        self.0.insert_tagged(tag, data)
    }

    fn get_repr_with(&self, tag: &T, key: &K) -> Option<Vec<u8>> {
        self.0.get_repr_with(tag, key)
    }

    fn get_tag_with(&self, tag: &T, key: &K) -> Option<T> {
        self.0.get_tag_with(tag, key)
    }
}

impl<K: Send + Sync + 'static, T: Send + Sync + 'static> From<TaggedBlobStore<K, T>>
    for BlobStore<K>
{
    fn from(tagged: TaggedBlobStore<K, T>) -> Self {
        BlobStore::new(tagged)
    }
}

mod git;
pub use git::{GitObjectType, GitPrefixStore, GitTaggedObjectStore};

#[cfg(feature = "memory")]
mod memory;
#[cfg(feature = "memory")]
pub use memory::{MemoryStore, SharedMemoryStore};

#[cfg(feature = "memory")]
mod tree;
#[cfg(feature = "memory")]
pub use tree::MemoryTreeStore;

#[cfg(feature = "sqlite")]
mod sqlite;
#[cfg(feature = "sqlite")]
pub use sqlite::SqliteStore;
