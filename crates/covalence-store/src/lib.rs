use rusqlite::Connection;

/// A content-addressed store backed by SQLite, mapping Blake3 hashes to blobs.
pub struct ContentStore {
    conn: Connection,
}

impl ContentStore {
    /// Open (or create) a content store at the given path.
    pub fn open(path: &str) -> Result<Self, rusqlite::Error> {
        let conn = Connection::open(path)?;
        conn.execute_batch(
            "CREATE TABLE IF NOT EXISTS blobs (
                hash BLOB NOT NULL PRIMARY KEY,
                data BLOB NOT NULL
            );",
        )?;
        Ok(ContentStore { conn })
    }

    /// Store a blob and return its 32-byte Blake3 hash.
    pub fn store(&self, data: &[u8]) -> Result<[u8; 32], rusqlite::Error> {
        let hash: [u8; 32] = *blake3::hash(data).as_bytes();
        self.conn.execute(
            "INSERT OR IGNORE INTO blobs (hash, data) VALUES (?1, ?2)",
            rusqlite::params![&hash[..], data],
        )?;
        Ok(hash)
    }

    /// Look up a blob by its 32-byte Blake3 hash.
    pub fn lookup(&self, hash: &[u8; 32]) -> Result<Option<Vec<u8>>, rusqlite::Error> {
        let mut stmt = self
            .conn
            .prepare("SELECT data FROM blobs WHERE hash = ?1")?;
        let mut rows = stmt.query(rusqlite::params![&hash[..]])?;
        match rows.next()? {
            Some(row) => Ok(Some(row.get(0)?)),
            None => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn store_and_lookup() {
        let store = ContentStore::open(":memory:").unwrap();
        let data = b"hello world";
        let hash = store.store(data).unwrap();
        assert_eq!(hash, *blake3::hash(data).as_bytes());
        let result = store.lookup(&hash).unwrap();
        assert_eq!(result, Some(data.to_vec()));
    }

    #[test]
    fn lookup_missing() {
        let store = ContentStore::open(":memory:").unwrap();
        let hash = [0u8; 32];
        assert_eq!(store.lookup(&hash).unwrap(), None);
    }

    #[test]
    fn store_idempotent() {
        let store = ContentStore::open(":memory:").unwrap();
        let data = b"test data";
        let h1 = store.store(data).unwrap();
        let h2 = store.store(data).unwrap();
        assert_eq!(h1, h2);
    }
}
