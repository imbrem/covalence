//! BLAKE3-keyed loose-object store.
//!
//! A content-addressed store of raw (uncompressed, unframed) files laid
//! out in a git-style fan-out directory: `{dir}/{hex[0:2]}/{hex[2:]}`,
//! keyed by the BLAKE3 hash of the content (`O256::blob`).
//!
//! Mirrors [`LfsStore`](crate::lfs::LfsStore) but keyed by BLAKE3 rather
//! than SHA-256, so a file's loose-store key equals its `O256` content
//! id everywhere else in covalence. Intended for *large* blobs that
//! would bloat the SQLite store; small blobs stay in SQLite (see
//! [`SizeRouter`](covalence_store::SizeRouter)).

use std::fs::{self, File};
use std::io::{Read, Seek, SeekFrom};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_hash::O256;
use covalence_store::{BlobInfo, ContentStore, StoreError, clip_slice};

/// A BLAKE3-keyed loose-object store rooted at a directory.
#[derive(Debug, Clone)]
pub struct Blake3LooseStore {
    dir: PathBuf,
}

impl Blake3LooseStore {
    /// Create a store rooted at `dir` (typically `.git/cog-<uuid>/objects`).
    pub fn new(dir: impl Into<PathBuf>) -> Self {
        Self { dir: dir.into() }
    }

    /// The git-style fan-out path for `key`: `{dir}/{hex[0:2]}/{hex[2:]}`.
    fn object_path(&self, key: &O256) -> PathBuf {
        let hex = key.to_string();
        self.dir.join(&hex[..2]).join(&hex[2..])
    }

    /// Write raw `data` to `key`'s path atomically (temp file + rename).
    /// Idempotent: an existing object is left untouched.
    fn write_raw(&self, key: &O256, data: &[u8]) -> Result<(), StoreError> {
        let path = self.object_path(key);
        if path.exists() {
            return Ok(());
        }
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| StoreError::Io(format!("mkdir {}: {e}", parent.display())))?;
        }
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let tmp = self.dir.join(format!("tmp_{}_{n}", std::process::id()));
        fs::write(&tmp, data).map_err(|e| StoreError::Io(format!("write {}: {e}", tmp.display())))?;
        fs::rename(&tmp, &path)
            .map_err(|e| StoreError::Io(format!("rename → {}: {e}", path.display())))?;
        Ok(())
    }
}

impl ContentStore<O256> for Blake3LooseStore {
    fn put(&self, key: O256, data: &[u8]) -> Result<(), StoreError> {
        let computed = O256::blob(data);
        if computed != key {
            return Err(StoreError::Io(format!(
                "loose-store hash mismatch: expected {key}, computed {computed}",
            )));
        }
        self.write_raw(&key, data)
    }

    fn insert(&self, data: &[u8]) -> Result<O256, StoreError> {
        let key = O256::blob(data);
        self.write_raw(&key, data)?;
        Ok(key)
    }

    fn get(&self, key: &O256) -> Option<Vec<u8>> {
        fs::read(self.object_path(key)).ok()
    }

    fn head(&self, key: &O256) -> Option<BlobInfo> {
        fs::metadata(self.object_path(key))
            .ok()
            .map(|m| BlobInfo { size: m.len() })
    }

    fn contains(&self, key: &O256) -> bool {
        self.object_path(key).exists()
    }

    /// Native partial read: stat for length, then seek + read the clipped
    /// range without pulling the whole blob into memory.
    fn get_slice(&self, key: &O256, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        let path = self.object_path(key);
        let mut file = match File::open(&path) {
            Ok(f) => f,
            Err(_) => return Err(StoreError::NotFound),
        };
        let total = file
            .metadata()
            .map_err(|e| StoreError::Io(format!("stat {}: {e}", path.display())))?
            .len();
        let Some(clipped) = clip_slice(total, range)? else {
            return Ok(Vec::new());
        };
        file.seek(SeekFrom::Start(clipped.start as u64))
            .map_err(|e| StoreError::Io(format!("seek {}: {e}", path.display())))?;
        let mut buf = vec![0u8; clipped.end - clipped.start];
        file.read_exact(&mut buf)
            .map_err(|e| StoreError::Io(format!("read {}: {e}", path.display())))?;
        Ok(buf)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("cov_cog_loose_{name}_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn round_trip_and_fanout() {
        let dir = test_dir("rt");
        let store = Blake3LooseStore::new(&dir);
        let data = b"loose blob content";
        let key = store.insert(data).unwrap();
        assert_eq!(key, O256::blob(data));
        assert!(store.contains(&key));
        assert_eq!(store.get(&key).unwrap(), data);

        let hex = key.to_string();
        assert!(dir.join(&hex[..2]).join(&hex[2..]).exists());
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn native_range_read() {
        let dir = test_dir("range");
        let store = Blake3LooseStore::new(&dir);
        let key = store.insert(b"0123456789").unwrap();
        assert_eq!(store.head(&key).unwrap().size, 10);
        assert_eq!(store.get_slice(&key, 2..5).unwrap(), b"234");
        // end past total clamps (POSIX read semantics).
        assert_eq!(store.get_slice(&key, 8..100).unwrap(), b"89");
        // start >= end is empty.
        assert_eq!(store.get_slice(&key, 5..5).unwrap(), b"");
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn missing_is_not_found() {
        let dir = test_dir("missing");
        let store = Blake3LooseStore::new(&dir);
        let absent = O256::blob(b"absent");
        assert!(store.get(&absent).is_none());
        assert!(!store.contains(&absent));
        assert!(matches!(
            store.get_slice(&absent, 0..1),
            Err(StoreError::NotFound)
        ));
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn put_rejects_mismatched_key() {
        let dir = test_dir("mismatch");
        let store = Blake3LooseStore::new(&dir);
        let wrong = O256::blob(b"wrong");
        assert!(store.put(wrong, b"right").is_err());
        let _ = fs::remove_dir_all(&dir);
    }
}
