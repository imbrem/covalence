//! Git LFS support — pointer files and a SHA-256 content store.
//!
//! [`LfsPointer`] parses and renders canonical LFS pointer files.
//! [`LfsStore`] implements [`ContentStore<O256>`] using SHA-256 hashing,
//! storing raw (uncompressed) files in a two-level fan-out directory.

use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_hash::O256;
use covalence_store::{ContentStore, StoreError};

/// A parsed Git LFS pointer file.
///
/// ```text
/// version https://git-lfs.github.com/spec/v1
/// oid sha256:abcdef...
/// size 1234
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LfsPointer {
    pub oid: O256,
    pub size: u64,
}

const LFS_VERSION_LINE: &str = "version https://git-lfs.github.com/spec/v1";

impl LfsPointer {
    /// Parse an LFS pointer from its text representation.
    pub fn parse(text: &str) -> Result<Self, StoreError> {
        let mut oid: Option<O256> = None;
        let mut size: Option<u64> = None;
        let mut saw_version = false;

        for line in text.lines() {
            if line == LFS_VERSION_LINE {
                saw_version = true;
            } else if let Some(rest) = line.strip_prefix("oid sha256:") {
                oid = Some(
                    O256::from_hex(rest)
                        .ok_or_else(|| StoreError::Io("invalid LFS oid hex".into()))?,
                );
            } else if let Some(rest) = line.strip_prefix("size ") {
                size = Some(
                    rest.parse()
                        .map_err(|e| StoreError::Io(format!("invalid LFS size: {e}")))?,
                );
            }
        }

        if !saw_version {
            return Err(StoreError::Io("missing LFS version line".into()));
        }
        let oid = oid.ok_or_else(|| StoreError::Io("missing LFS oid".into()))?;
        let size = size.ok_or_else(|| StoreError::Io("missing LFS size".into()))?;

        Ok(Self { oid, size })
    }

    /// Create a pointer by computing the SHA-256 hash and size of `data`.
    pub fn from_data(data: &[u8]) -> Self {
        Self {
            oid: O256::blob_sha256(data),
            size: data.len() as u64,
        }
    }
}

impl fmt::Display for LfsPointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{LFS_VERSION_LINE}")?;
        writeln!(f, "oid sha256:{}", self.oid)?;
        write!(f, "size {}", self.size)
    }
}

/// A Git LFS content store using SHA-256 hashing.
///
/// Objects are stored as raw files (no zlib, no git header) in a two-level
/// fan-out directory: `{lfs_objects_dir}/{sha256[0:2]}/{sha256[2:4]}/{full_sha256}`.
#[derive(Debug, Clone)]
pub struct LfsStore {
    lfs_objects_dir: PathBuf,
}

impl LfsStore {
    /// Create a store rooted at the given directory.
    ///
    /// Typically this is `.git/lfs/objects` inside a repository.
    pub fn new(lfs_objects_dir: impl Into<PathBuf>) -> Self {
        Self {
            lfs_objects_dir: lfs_objects_dir.into(),
        }
    }

    /// Create a store for a repository at `repo_root`.
    ///
    /// Uses the conventional `.git/lfs/objects` path.
    pub fn from_repo(repo_root: impl AsRef<Path>) -> Self {
        Self::new(repo_root.as_ref().join(".git").join("lfs").join("objects"))
    }

    /// The fan-out path for a given SHA-256 hash.
    fn object_path(&self, oid: &O256) -> PathBuf {
        let hex = oid.to_string();
        self.lfs_objects_dir
            .join(&hex[..2])
            .join(&hex[2..4])
            .join(&hex)
    }

    /// Write raw data to the fan-out path, atomically.
    fn write_raw(&self, oid: &O256, data: &[u8]) -> Result<(), StoreError> {
        let path = self.object_path(oid);

        // Already exists — nothing to do.
        if path.exists() {
            return Ok(());
        }

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| StoreError::Io(format!("mkdir {}: {e}", parent.display())))?;
        }

        // Atomic write: temp file with unique name, then rename into place.
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let tmp = self
            .lfs_objects_dir
            .join(format!("tmp_lfs_{}_{n}", std::process::id()));
        fs::write(&tmp, data)
            .map_err(|e| StoreError::Io(format!("write {}: {e}", tmp.display())))?;
        fs::rename(&tmp, &path)
            .map_err(|e| StoreError::Io(format!("rename → {}: {e}", path.display())))?;

        Ok(())
    }
}

impl ContentStore<O256> for LfsStore {
    fn get(&self, key: &O256) -> Option<Vec<u8>> {
        fs::read(self.object_path(key)).ok()
    }

    fn put(&self, key: O256, data: &[u8]) -> Result<(), StoreError> {
        let computed = O256::blob_sha256(data);
        if computed != key {
            return Err(StoreError::Io(format!(
                "LFS hash mismatch: expected {key}, computed {computed}",
            )));
        }
        self.write_raw(&key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<O256, StoreError> {
        let oid = O256::blob_sha256(data);
        self.write_raw(&oid, data)?;
        Ok(oid)
    }

    fn contains(&self, key: &O256) -> bool {
        self.object_path(key).exists()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("cov_lfs_{name}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn pointer_round_trip() {
        let ptr = LfsPointer::from_data(b"hello lfs");
        let text = ptr.to_string();
        let parsed = LfsPointer::parse(&text).unwrap();
        assert_eq!(parsed, ptr);
    }

    #[test]
    fn pointer_format() {
        let ptr = LfsPointer::from_data(b"hello lfs");
        let text = ptr.to_string();
        assert!(text.starts_with("version https://git-lfs.github.com/spec/v1\n"));
        assert!(text.contains("oid sha256:"));
        assert!(text.contains("size 9"));
    }

    #[test]
    fn pointer_parse_missing_version() {
        let text =
            "oid sha256:0000000000000000000000000000000000000000000000000000000000000000\nsize 0";
        assert!(LfsPointer::parse(text).is_err());
    }

    #[test]
    fn pointer_parse_missing_oid() {
        let text = "version https://git-lfs.github.com/spec/v1\nsize 0";
        assert!(LfsPointer::parse(text).is_err());
    }

    #[test]
    fn pointer_parse_missing_size() {
        let text = "version https://git-lfs.github.com/spec/v1\noid sha256:0000000000000000000000000000000000000000000000000000000000000000";
        assert!(LfsPointer::parse(text).is_err());
    }

    #[test]
    fn store_round_trip() {
        let dir = test_dir("rt");
        let store = LfsStore::new(&dir);

        let data = b"lfs content";
        let oid = store.insert(data).unwrap();
        assert_eq!(oid, O256::blob_sha256(data));
        assert!(store.contains(&oid));
        assert_eq!(store.get(&oid).unwrap(), data);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn store_fan_out_structure() {
        let dir = test_dir("fanout");
        let store = LfsStore::new(&dir);

        let data = b"fan-out test";
        let oid = store.insert(data).unwrap();
        let hex = oid.to_string();

        // Verify the file is at the expected fan-out path and contains raw data.
        let expected_path = dir.join(&hex[..2]).join(&hex[2..4]).join(&hex);
        assert!(expected_path.exists());
        assert_eq!(fs::read(&expected_path).unwrap(), data);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn store_hash_validation() {
        let dir = test_dir("validate");
        let store = LfsStore::new(&dir);

        let wrong_key = O256::blob_sha256(b"wrong");
        assert!(store.put(wrong_key, b"right").is_err());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn store_idempotent() {
        let dir = test_dir("idempotent");
        let store = LfsStore::new(&dir);

        let data = b"same content";
        let oid1 = store.insert(data).unwrap();
        let oid2 = store.insert(data).unwrap();
        assert_eq!(oid1, oid2);
        assert_eq!(store.get(&oid1).unwrap(), data);

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn store_put_matching_hash() {
        let dir = test_dir("put_ok");
        let store = LfsStore::new(&dir);

        let data = b"put test";
        let expected = O256::blob_sha256(data);
        store.put(expected, data).unwrap();
        assert_eq!(store.get(&expected).unwrap(), data);

        let _ = fs::remove_dir_all(&dir);
    }
}
