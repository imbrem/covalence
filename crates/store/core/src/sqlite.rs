use std::sync::{Arc, Mutex};

use covalence_hash::O256;
use covalence_sqlite::Connection;

use crate::{BlobInfo, ContentStore, StoreError};

/// Content-addressed blob store backed by SQLite.
///
/// Clone is cheap (Arc internals). Thread-safe via internal Mutex.
#[derive(Clone)]
pub struct SqliteStore {
    conn: Arc<Mutex<Connection>>,
}

impl SqliteStore {
    /// Open a persistent store at the given path.
    /// Creates the database and table if they don't exist.
    pub fn open(path: impl AsRef<std::path::Path>) -> Result<Self, covalence_sqlite::Error> {
        let conn = covalence_sqlite::open(path)?;
        Self::init(conn)
    }

    /// Open an in-memory store (useful for testing).
    pub fn memory() -> Result<Self, covalence_sqlite::Error> {
        let conn = covalence_sqlite::open_memory()?;
        Self::init(conn)
    }

    fn init(conn: Connection) -> Result<Self, covalence_sqlite::Error> {
        conn.execute(
            "CREATE TABLE IF NOT EXISTS blobs (hash BLOB PRIMARY KEY, data BLOB NOT NULL) WITHOUT ROWID",
            [],
        )?;
        Ok(Self {
            conn: Arc::new(Mutex::new(conn)),
        })
    }

    /// Collect all hashes in the store.
    pub fn hashes(&self) -> Result<Vec<O256>, crate::StoreError> {
        let conn = self.conn.lock().unwrap();
        let mut stmt = conn
            .prepare("SELECT hash FROM blobs")
            .map_err(|e| crate::StoreError::Io(e.to_string()))?;
        let rows = stmt
            .query_map([], |row| {
                let bytes: Vec<u8> = row.get(0)?;
                Ok(bytes)
            })
            .map_err(|e| crate::StoreError::Io(e.to_string()))?;
        let mut hashes = Vec::new();
        for row in rows {
            let bytes = row.map_err(|e| crate::StoreError::Io(e.to_string()))?;
            let arr: [u8; 32] = bytes.try_into().map_err(|v: Vec<u8>| {
                crate::StoreError::Io(format!("hash has wrong length: {}", v.len()))
            })?;
            hashes.push(O256::from_bytes(arr));
        }
        Ok(hashes)
    }
}

impl ContentStore<O256> for SqliteStore {
    fn get(&self, key: &O256) -> Option<Vec<u8>> {
        let conn = self.conn.lock().unwrap();
        conn.query_row(
            "SELECT data FROM blobs WHERE hash = ?1",
            [key.as_bytes().as_slice()],
            |row| row.get(0),
        )
        .ok()
    }

    fn put(&self, key: O256, data: &[u8]) -> Result<(), crate::StoreError> {
        let conn = self.conn.lock().unwrap();
        conn.execute(
            "INSERT OR IGNORE INTO blobs (hash, data) VALUES (?1, ?2)",
            covalence_sqlite::params![key.as_bytes().as_slice(), data],
        )
        .map_err(|e| crate::StoreError::Io(e.to_string()))?;
        Ok(())
    }

    fn insert(&self, data: &[u8]) -> Result<O256, crate::StoreError> {
        let hash = O256::blob(data);
        self.put(hash, data)?;
        Ok(hash)
    }

    fn contains(&self, key: &O256) -> bool {
        let conn = self.conn.lock().unwrap();
        conn.query_row(
            "SELECT 1 FROM blobs WHERE hash = ?1",
            [key.as_bytes().as_slice()],
            |_| Ok(()),
        )
        .is_ok()
    }

    fn len(&self) -> Option<usize> {
        let conn = self.conn.lock().unwrap();
        conn.query_row("SELECT COUNT(*) FROM blobs", [], |row| {
            row.get::<_, i64>(0).map(|n| n as usize)
        })
        .ok()
    }

    /// One round trip via `SELECT length(data) ... WHERE hash = ?` —
    /// SQLite answers from the row header, without reading the BLOB body.
    fn head(&self, key: &O256) -> Option<BlobInfo> {
        let conn = self.conn.lock().unwrap();
        conn.query_row(
            "SELECT length(data) FROM blobs WHERE hash = ?1",
            [key.as_bytes().as_slice()],
            |row| row.get::<_, i64>(0).map(|n| BlobInfo { size: n as u64 }),
        )
        .ok()
    }

    /// Native partial read via SQLite `substr(data, start_1indexed, length)`.
    ///
    /// `substr` returns just the requested bytes — SQLite doesn't load
    /// the whole BLOB into memory for the slice. One query returns the
    /// row's true `length(data)` alongside the slice so we can validate
    /// the range without a second round trip.
    fn get_slice(&self, key: &O256, range: std::ops::Range<u64>) -> Result<Vec<u8>, StoreError> {
        let length_to_read = range.end.saturating_sub(range.start).min(i64::MAX as u64) as i64;
        let conn = self.conn.lock().unwrap();
        // substr is 1-indexed; passing 1 means the first byte. SQLite
        // clamps an over-long length silently.
        // `substr` can return NULL when the request slides off an
        // empty blob — read as `Option<Vec<u8>>` and treat None as "".
        let result = conn.query_row(
            "SELECT length(data), substr(data, ?1, ?2) FROM blobs WHERE hash = ?3",
            covalence_sqlite::params![
                (range.start as i64) + 1,
                length_to_read,
                key.as_bytes().as_slice()
            ],
            |row| Ok((row.get::<_, i64>(0)?, row.get::<_, Option<Vec<u8>>>(1)?)),
        );

        let (total_i64, bytes) = match result {
            Ok(v) => v,
            Err(covalence_sqlite::Error::QueryReturnedNoRows) => return Err(StoreError::NotFound),
            Err(e) => return Err(StoreError::Io(e.to_string())),
        };
        let total = total_i64 as u64;

        // Range validation. The query already ran (with possibly empty
        // bytes); now decide whether the request was satisfiable.
        if range.start >= range.end {
            return Ok(Vec::new());
        }
        if total == 0 {
            return if range.start == 0 {
                Ok(Vec::new())
            } else {
                Err(StoreError::RangeNotSatisfiable { total })
            };
        }
        if range.start >= total {
            return Err(StoreError::RangeNotSatisfiable { total });
        }
        Ok(bytes.unwrap_or_default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_and_get() {
        let store = SqliteStore::memory().unwrap();
        let hash = store.insert(b"hello").unwrap();
        assert_eq!(store.get(&hash), Some(b"hello".to_vec()));
    }

    #[test]
    fn content_addressed() {
        let store = SqliteStore::memory().unwrap();
        let h1 = store.insert(b"data").unwrap();
        let h2 = store.insert(b"data").unwrap();
        assert_eq!(h1, h2);
        assert_eq!(store.len(), Some(1));
    }

    #[test]
    fn unknown_hash() {
        let store = SqliteStore::memory().unwrap();
        let hash = O256::blob(b"missing");
        assert!(!store.contains(&hash));
        assert_eq!(store.get(&hash), None);
    }

    #[test]
    fn hashes_list() {
        let store = SqliteStore::memory().unwrap();
        let h1 = store.insert(b"a").unwrap();
        let h2 = store.insert(b"b").unwrap();
        let hashes = store.hashes().unwrap();
        assert_eq!(hashes.len(), 2);
        assert!(hashes.contains(&h1));
        assert!(hashes.contains(&h2));
    }

    #[test]
    fn head_returns_size_without_full_read() {
        let store = SqliteStore::memory().unwrap();
        let hash = store.insert(b"hello world").unwrap();
        assert_eq!(store.head(&hash), Some(BlobInfo { size: 11 }));
        assert_eq!(store.head(&O256::blob(b"missing")), None);
    }

    #[test]
    fn get_slice_native() {
        let store = SqliteStore::memory().unwrap();
        let hash = store.insert(b"0123456789").unwrap();
        assert_eq!(store.get_slice(&hash, 0..4).unwrap(), b"0123");
        assert_eq!(store.get_slice(&hash, 5..10).unwrap(), b"56789");
        // Over-long end clamps silently.
        assert_eq!(store.get_slice(&hash, 8..999).unwrap(), b"89");
    }

    #[test]
    fn get_slice_missing_is_not_found() {
        let store = SqliteStore::memory().unwrap();
        let missing = O256::blob(b"absent");
        assert!(matches!(
            store.get_slice(&missing, 0..5),
            Err(StoreError::NotFound)
        ));
    }

    #[test]
    fn get_slice_past_end_is_416() {
        let store = SqliteStore::memory().unwrap();
        let hash = store.insert(b"five!").unwrap();
        match store.get_slice(&hash, 10..20) {
            Err(StoreError::RangeNotSatisfiable { total }) => assert_eq!(total, 5),
            other => panic!("expected RangeNotSatisfiable, got {other:?}"),
        }
    }

    #[test]
    fn get_slice_empty_range_existence_check() {
        let store = SqliteStore::memory().unwrap();
        let hash = store.insert(b"data").unwrap();
        // Empty range on an existing key returns Ok(empty).
        assert_eq!(store.get_slice(&hash, 2..2).unwrap(), b"");
        // Empty range on a missing key returns NotFound.
        assert!(matches!(
            store.get_slice(&O256::blob(b"missing"), 0..0),
            Err(StoreError::NotFound)
        ));
    }

    #[test]
    fn get_slice_empty_blob() {
        let store = SqliteStore::memory().unwrap();
        let hash = store.insert(b"").unwrap();
        assert_eq!(store.get_slice(&hash, 0..10).unwrap(), b"");
        // Non-zero start on empty blob is unsatisfiable.
        assert!(matches!(
            store.get_slice(&hash, 5..10),
            Err(StoreError::RangeNotSatisfiable { total: 0 })
        ));
    }

    #[test]
    fn persistent_store() {
        let dir = std::env::temp_dir().join("covalence_sqlite_test");
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("test.db");
        let _ = std::fs::remove_file(&path);

        let hash = {
            let store = SqliteStore::open(&path).unwrap();
            store.insert(b"persistent").unwrap()
        };

        // Reopen and verify data persists
        let store = SqliteStore::open(&path).unwrap();
        assert_eq!(store.get(&hash), Some(b"persistent".to_vec()));

        let _ = std::fs::remove_file(&path);
    }
}
