use std::sync::{Arc, Mutex};

use covalence_hash::O256;
use covalence_sqlite::Connection;

use crate::ContentStore;

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
