//! ODB backend — reads and writes git objects via `gix-odb` (loose + packed).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use covalence_hash::gix_hash;
use covalence_store::StoreError;
use gix_object::Exists;
use gix_object::Find;
use gix_object::Write as GixWrite;

use super::backend::{GitBackend, GitObject, GitObjectKind};

/// A [`GitBackend`] backed by [`gix_odb::Store`], supporting both loose and
/// packed objects.
///
/// Internally holds an `Arc<gix_odb::Store>`. Each method creates a short-lived
/// `Cache` handle via `Store::to_cache_arc` — this is cheap (no I/O) and the
/// handle is dropped at the end of the call.
#[derive(Clone)]
pub struct OdbBackend {
    store: Arc<gix_odb::Store>,
    kind: gix_hash::Kind,
}

impl OdbBackend {
    /// Open an ODB at the given `objects` directory.
    ///
    /// `objects_dir` is typically `.git/objects` inside a repository.
    pub fn open(objects_dir: impl Into<PathBuf>, kind: gix_hash::Kind) -> Result<Self, StoreError> {
        let objects_dir = objects_dir.into();
        let store = gix_odb::Store::at_opts(
            objects_dir,
            &mut std::iter::empty(),
            gix_odb::store::init::Options {
                object_hash: kind,
                ..Default::default()
            },
        )
        .map_err(|e| StoreError::Io(format!("open odb: {e}")))?;
        Ok(Self {
            store: Arc::new(store),
            kind,
        })
    }

    /// Open an ODB for a repository at `repo_root`.
    ///
    /// Equivalent to `OdbBackend::open(repo_root.join(".git/objects"), kind)`.
    pub fn from_repo(
        repo_root: impl AsRef<Path>,
        kind: gix_hash::Kind,
    ) -> Result<Self, StoreError> {
        Self::open(repo_root.as_ref().join(".git").join("objects"), kind)
    }

    /// Open an ODB, auto-detecting the hash kind from the store.
    pub fn open_auto(objects_dir: impl Into<PathBuf>) -> Result<Self, StoreError> {
        let objects_dir = objects_dir.into();
        let store =
            gix_odb::Store::at_opts(objects_dir, &mut std::iter::empty(), Default::default())
                .map_err(|e| StoreError::Io(format!("open odb: {e}")))?;
        let kind = store.object_hash();
        Ok(Self {
            store: Arc::new(store),
            kind,
        })
    }

    /// Create a fresh `Cache` handle for this store.
    fn cache(&self) -> gix_odb::Cache<gix_odb::store::Handle<Arc<gix_odb::Store>>> {
        self.store.to_cache_arc()
    }

    /// Iterate every object ID known to the store: packed objects first, then
    /// loose objects. The same OID may appear more than once if it exists in
    /// multiple packs or both loose and packed; consumers should dedup as
    /// needed.
    pub fn iter_oids(
        &self,
    ) -> Result<impl Iterator<Item = Result<gix_hash::ObjectId, StoreError>>, StoreError> {
        let iter = self
            .store
            .iter()
            .map_err(|e| StoreError::Io(format!("odb iter: {e}")))?;
        Ok(iter.map(|r| r.map_err(|e| StoreError::Io(format!("odb iter: {e}")))))
    }
}

/// Convert our `GitObjectKind` to `gix_object::Kind`.
fn to_gix_kind(kind: GitObjectKind) -> gix_object::Kind {
    match kind {
        GitObjectKind::Blob => gix_object::Kind::Blob,
        GitObjectKind::Tree => gix_object::Kind::Tree,
        GitObjectKind::Commit => gix_object::Kind::Commit,
        GitObjectKind::Tag => gix_object::Kind::Tag,
    }
}

/// Convert `gix_object::Kind` to our `GitObjectKind`.
fn from_gix_kind(kind: gix_object::Kind) -> GitObjectKind {
    match kind {
        gix_object::Kind::Blob => GitObjectKind::Blob,
        gix_object::Kind::Tree => GitObjectKind::Tree,
        gix_object::Kind::Commit => GitObjectKind::Commit,
        gix_object::Kind::Tag => GitObjectKind::Tag,
    }
}

impl GitBackend for OdbBackend {
    fn read_object(&self, id: &gix_hash::ObjectId) -> Result<GitObject, StoreError> {
        let cache = self.cache();
        let mut buf = Vec::new();
        let data = cache
            .try_find(id, &mut buf)
            .map_err(|e| StoreError::Io(format!("odb read {id}: {e}")))?
            .ok_or_else(|| StoreError::Io(format!("object not found: {id}")))?;
        let kind = from_gix_kind(data.kind);
        let bytes = data.data.to_vec();
        Ok(GitObject { kind, data: bytes })
    }

    fn write_object(
        &self,
        kind: GitObjectKind,
        data: &[u8],
    ) -> Result<gix_hash::ObjectId, StoreError> {
        let cache = self.cache();
        cache
            .write_buf(to_gix_kind(kind), data)
            .map_err(|e| StoreError::Io(format!("odb write: {e}")))
    }

    fn contains_object(&self, id: &gix_hash::ObjectId) -> bool {
        let cache = self.cache();
        cache.exists(id)
    }

    fn hash_kind(&self) -> gix_hash::Kind {
        self.kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::{GitObjectStore, LooseBackend};
    use covalence_store::ContentStore;
    use std::fs;

    /// Create a fresh temp directory for a test, cleaning up any prior run.
    fn test_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("cov_odb_{name}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn write_loose_read_odb() {
        let dir = test_dir("cross");
        let loose = LooseBackend::new(&dir, gix_hash::Kind::Sha1);

        let data = b"cross-compat test";
        let id = loose.write_object(GitObjectKind::Blob, data).unwrap();

        let odb = OdbBackend::open(&dir, gix_hash::Kind::Sha1).unwrap();
        let obj = odb.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, data);
        assert!(odb.contains_object(&id));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn odb_round_trip() {
        let dir = test_dir("rt");
        // Need at least the objects dir structure for gix-odb to write loose objects.
        let odb = OdbBackend::open(&dir, gix_hash::Kind::Sha1).unwrap();

        let data = b"odb round trip";
        let id = odb.write_object(GitObjectKind::Blob, data).unwrap();
        assert_eq!(id, covalence_hash::git::blob_sha1("odb round trip"));

        let obj = odb.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, data);
        assert!(odb.contains_object(&id));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn odb_missing_object() {
        let dir = test_dir("missing");
        let odb = OdbBackend::open(&dir, gix_hash::Kind::Sha1).unwrap();

        let fake = covalence_hash::git::blob_sha1("nonexistent");
        assert!(!odb.contains_object(&fake));
        assert!(odb.read_object(&fake).is_err());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn odb_content_store_adapter() {
        let dir = test_dir("cs");
        let odb = OdbBackend::open(&dir, gix_hash::Kind::Sha1).unwrap();
        let store = GitObjectStore::new(odb);

        let data = b"content store via odb";
        let id = store.insert(data).unwrap();
        assert!(store.contains(&id));
        assert_eq!(store.get(&id).unwrap(), data);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn odb_tree_object() {
        let dir = test_dir("tree");
        let odb = OdbBackend::open(&dir, gix_hash::Kind::Sha1).unwrap();

        let tree_data =
            b"100644 hello.txt\0\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14";
        let id = odb.write_object(GitObjectKind::Tree, tree_data).unwrap();
        let obj = odb.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Tree);
        assert_eq!(obj.data, tree_data);

        let _ = fs::remove_dir_all(&dir);
    }
}
