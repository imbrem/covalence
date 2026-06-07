use covalence_hash::O256;

/// Errors from kernel operations.
#[derive(Debug, thiserror::Error)]
pub enum KernelError {
    #[error("store error: {0}")]
    Store(String),
    #[error("not found: {0}")]
    NotFound(String),
}

/// Information about a backend.
pub struct BackendInfo {
    /// "local" or "http"
    pub kind: String,
    /// Human-readable connection target (e.g. "in-memory" or URL)
    pub target: String,
}

/// Synchronous backend trait — dyn-compatible for use with `Box<dyn SyncBackend>`.
pub trait SyncBackend: Send {
    fn info(&self) -> BackendInfo;
    fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError>;
    fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError>;
    fn has_blob(&self, hash: &O256) -> Result<bool, KernelError>;
    fn blob_count(&self) -> Result<Option<usize>, KernelError>;

    /// Store tree data, returning a tree-tagged hash.
    fn store_tree(&self, data: &[u8]) -> Result<O256, KernelError> {
        self.store_blob(data)
    }

    /// Check whether a hash refers to a tree.
    fn is_tree(&self, hash: &O256) -> Result<bool, KernelError> {
        let _ = hash;
        Ok(false)
    }

    /// Register a `(tag, content_hash) → keyed_identity` mapping in
    /// the backend's tag registry, where the keyed identity is
    /// `O256::context(tag, content_hash)`. Later calls to
    /// [`Self::lookup_tag`] recover the tag string and the underlying
    /// content hash from this identity.
    ///
    /// The default impl computes the keyed identity without
    /// registering it — handy for stateless backends that defer the
    /// mapping to another layer (e.g. a server endpoint).
    fn register_tag(&self, tag: &str, content_hash: O256) -> Result<O256, KernelError> {
        Ok(O256::context(tag, content_hash.as_bytes()))
    }

    /// Look up the tag and content-hash for a keyed identity. Returns
    /// `Ok(None)` for any unknown or plain-blob hash.
    fn lookup_tag(&self, keyed: &O256) -> Result<Option<(String, O256)>, KernelError> {
        let _ = keyed;
        Ok(None)
    }
}

/// Asynchronous backend trait — NOT dyn-compatible (uses native async fn).
/// Used with concrete types in the server.
#[allow(async_fn_in_trait)]
pub trait AsyncBackend: Send + Sync {
    fn info(&self) -> BackendInfo;
    async fn store_blob(&self, data: &[u8]) -> Result<O256, KernelError>;
    async fn get_blob(&self, hash: &O256) -> Result<Option<Vec<u8>>, KernelError>;
    async fn has_blob(&self, hash: &O256) -> Result<bool, KernelError>;
    async fn blob_count(&self) -> Result<Option<usize>, KernelError>;

    /// Store tree data, returning a tree-tagged hash.
    async fn store_tree(&self, data: &[u8]) -> Result<O256, KernelError> {
        self.store_blob(data).await
    }

    /// Check whether a hash refers to a tree.
    async fn is_tree(&self, hash: &O256) -> Result<bool, KernelError> {
        let _ = hash;
        Ok(false)
    }

    async fn register_tag(&self, tag: &str, content_hash: O256) -> Result<O256, KernelError> {
        Ok(O256::context(tag, content_hash.as_bytes()))
    }

    async fn lookup_tag(&self, keyed: &O256) -> Result<Option<(String, O256)>, KernelError> {
        let _ = keyed;
        Ok(None)
    }
}
