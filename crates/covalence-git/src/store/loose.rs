//! Loose object backend — reads and writes individual zlib-compressed files.

use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use covalence_hash::gix_hash;
use covalence_store::StoreError;
use flate2::Compression;
use flate2::read::ZlibDecoder;
use flate2::write::ZlibEncoder;

use super::backend::{GitBackend, GitObject, GitObjectKind};

/// A [`GitBackend`] that reads and writes loose objects on disk.
///
/// Loose objects are stored as zlib-compressed files at
/// `{objects_dir}/{xx}/{rest}` where `xx` is the first two hex characters
/// of the object ID and `rest` is the remaining hex.
#[derive(Debug, Clone)]
pub struct LooseBackend {
    objects_dir: PathBuf,
    kind: gix_hash::Kind,
}

impl LooseBackend {
    /// Create a backend pointing at the given `objects` directory.
    ///
    /// `objects_dir` is typically `.git/objects` inside a repository.
    pub fn new(objects_dir: impl Into<PathBuf>, kind: gix_hash::Kind) -> Self {
        Self {
            objects_dir: objects_dir.into(),
            kind,
        }
    }

    /// Create a backend for a repository at `repo_root`.
    ///
    /// Equivalent to `LooseBackend::new(repo_root.join(".git/objects"), kind)`.
    pub fn from_repo(repo_root: impl AsRef<Path>, kind: gix_hash::Kind) -> Self {
        Self::new(repo_root.as_ref().join(".git").join("objects"), kind)
    }

    /// Return the path to the loose object file for `id`.
    fn object_path(&self, id: &gix_hash::ObjectId) -> PathBuf {
        let hex = id.to_string();
        self.objects_dir.join(&hex[..2]).join(&hex[2..])
    }

    /// Compute the object ID for the given type and data.
    fn hash_object(&self, kind: GitObjectKind, data: &[u8]) -> gix_hash::ObjectId {
        let mut hasher = gix_hash::hasher(self.kind);
        let header = format!("{} {}\0", kind.as_str(), data.len());
        hasher.update(header.as_bytes());
        hasher.update(data);
        hasher.try_finalize().expect("git hash finalize")
    }
}

impl GitBackend for LooseBackend {
    fn read_object(&self, id: &gix_hash::ObjectId) -> Result<GitObject, StoreError> {
        let path = self.object_path(id);
        let compressed =
            fs::read(&path).map_err(|e| StoreError::Io(format!("{}: {e}", path.display())))?;

        let mut decoder = ZlibDecoder::new(&compressed[..]);
        let mut raw = Vec::new();
        decoder
            .read_to_end(&mut raw)
            .map_err(|e| StoreError::Io(format!("decompress {id}: {e}")))?;

        // Parse header: "{type} {size}\0{data}"
        let null = raw
            .iter()
            .position(|&b| b == 0)
            .ok_or_else(|| StoreError::Io(format!("invalid object {id}: missing null")))?;

        let header = std::str::from_utf8(&raw[..null])
            .map_err(|e| StoreError::Io(format!("invalid object {id}: {e}")))?;

        let space = header
            .find(' ')
            .ok_or_else(|| StoreError::Io(format!("invalid object header: {header}")))?;

        let kind: GitObjectKind = header[..space]
            .parse()
            .map_err(|_| StoreError::Io(format!("unknown object type: {}", &header[..space])))?;

        let data = raw[null + 1..].to_vec();
        Ok(GitObject { kind, data })
    }

    fn write_object(
        &self,
        kind: GitObjectKind,
        data: &[u8],
    ) -> Result<gix_hash::ObjectId, StoreError> {
        let id = self.hash_object(kind, data);
        let path = self.object_path(&id);

        // Object already exists — nothing to do.
        if path.exists() {
            return Ok(id);
        }

        // Build the raw git object: "{type} {size}\0{data}"
        let header = format!("{} {}\0", kind.as_str(), data.len());
        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        encoder
            .write_all(header.as_bytes())
            .map_err(|e| StoreError::Io(format!("compress: {e}")))?;
        encoder
            .write_all(data)
            .map_err(|e| StoreError::Io(format!("compress: {e}")))?;
        let compressed = encoder
            .finish()
            .map_err(|e| StoreError::Io(format!("compress finish: {e}")))?;

        // Ensure the fan-out directory exists.
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| StoreError::Io(format!("mkdir {}: {e}", parent.display())))?;
        }

        // Atomic write: temp file in the objects dir, then rename into place.
        let tmp = self.objects_dir.join(format!("tmp_obj_{id}"));
        fs::write(&tmp, &compressed)
            .map_err(|e| StoreError::Io(format!("write {}: {e}", tmp.display())))?;
        fs::rename(&tmp, &path)
            .map_err(|e| StoreError::Io(format!("rename → {}: {e}", path.display())))?;

        Ok(id)
    }

    fn contains_object(&self, id: &gix_hash::ObjectId) -> bool {
        self.object_path(id).exists()
    }

    fn hash_kind(&self) -> gix_hash::Kind {
        self.kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Create a fresh temp directory for a test, cleaning up any prior run.
    fn test_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("cov_loose_{name}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn round_trip_blob() {
        let dir = test_dir("rt_blob");
        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha1);

        let data = b"hello world";
        let id = backend.write_object(GitObjectKind::Blob, data).unwrap();

        // Hash must match the covalence-hash reference implementation.
        assert_eq!(id, covalence_hash::git::blob_sha1("hello world"));

        let obj = backend.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, data);
        assert!(backend.contains_object(&id));

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn round_trip_tree() {
        let dir = test_dir("rt_tree");
        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha1);

        let tree_data =
            b"100644 hello.txt\0\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14";
        let id = backend
            .write_object(GitObjectKind::Tree, tree_data)
            .unwrap();

        let obj = backend.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Tree);
        assert_eq!(obj.data, tree_data);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn round_trip_sha256() {
        let dir = test_dir("rt_sha256");
        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha256);

        let data = b"sha256 test";
        let id = backend.write_object(GitObjectKind::Blob, data).unwrap();

        assert_eq!(id, covalence_hash::git::blob_sha256("sha256 test"));

        let obj = backend.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, data);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn write_is_idempotent() {
        let dir = test_dir("idempotent");
        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha1);

        let data = b"same content";
        let id1 = backend.write_object(GitObjectKind::Blob, data).unwrap();
        let id2 = backend.write_object(GitObjectKind::Blob, data).unwrap();
        assert_eq!(id1, id2);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn missing_object_returns_error() {
        let dir = test_dir("missing");
        let backend = LooseBackend::new(&dir, gix_hash::Kind::Sha1);

        let fake = covalence_hash::git::blob_sha1("nonexistent");
        assert!(!backend.contains_object(&fake));
        assert!(backend.read_object(&fake).is_err());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn object_kind_parse_round_trip() {
        for kind in [
            GitObjectKind::Blob,
            GitObjectKind::Tree,
            GitObjectKind::Commit,
            GitObjectKind::Tag,
        ] {
            let s = kind.as_str();
            assert_eq!(s.parse::<GitObjectKind>(), Ok(kind));
            assert_eq!(kind.to_string(), s);
        }
        assert!("invalid".parse::<GitObjectKind>().is_err());
    }
}
