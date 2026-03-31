use rusqlite::Connection;

/// Supported hash algorithms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HashKind {
    Blake3,
}

impl HashKind {
    /// Multicodec code for this hash algorithm.
    pub fn multicodec(self) -> u64 {
        match self {
            HashKind::Blake3 => 0x1e,
        }
    }

    /// Expected digest length in bytes.
    pub fn digest_len(self) -> usize {
        match self {
            HashKind::Blake3 => 32,
        }
    }

    /// Database identifier string.
    fn as_str(self) -> &'static str {
        match self {
            HashKind::Blake3 => "blake3",
        }
    }

    /// Parse from database identifier string.
    fn from_str(s: &str) -> Option<Self> {
        match s {
            "blake3" => Some(HashKind::Blake3),
            _ => None,
        }
    }

    /// Parse from multicodec code.
    fn from_multicodec(code: u64) -> Option<Self> {
        match code {
            0x1e => Some(HashKind::Blake3),
            _ => None,
        }
    }

    /// Compute the digest for the given data.
    fn hash(self, data: &[u8]) -> Vec<u8> {
        match self {
            HashKind::Blake3 => blake3::hash(data).as_bytes().to_vec(),
        }
    }

    /// All supported hash kinds.
    pub fn all() -> &'static [HashKind] {
        &[HashKind::Blake3]
    }
}

/// Storage strategy for blob data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageKind {
    Inline,
}

impl StorageKind {
    fn as_str(self) -> &'static str {
        match self {
            StorageKind::Inline => "inline",
        }
    }

    fn from_str(s: &str) -> Option<Self> {
        match s {
            "inline" => Some(StorageKind::Inline),
            _ => None,
        }
    }
}

/// A self-describing hash: multicodec varint + digest length varint + digest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Multihash {
    pub kind: HashKind,
    pub digest: Vec<u8>,
}

/// Encode an unsigned integer as an unsigned varint (LEB128).
fn encode_uvarint(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

/// Decode an unsigned varint from a byte slice, returning (value, bytes_consumed).
fn decode_uvarint(bytes: &[u8]) -> Option<(u64, usize)> {
    let mut value: u64 = 0;
    let mut shift = 0u32;
    for (i, &byte) in bytes.iter().enumerate() {
        if shift >= 70 {
            return None; // overflow
        }
        value |= ((byte & 0x7f) as u64) << shift;
        if byte & 0x80 == 0 {
            return Some((value, i + 1));
        }
        shift += 7;
    }
    None // incomplete
}

impl Multihash {
    /// Encode to binary multihash bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        encode_uvarint(self.kind.multicodec(), &mut buf);
        encode_uvarint(self.digest.len() as u64, &mut buf);
        buf.extend_from_slice(&self.digest);
        buf
    }

    /// Encode to hex string.
    pub fn to_hex(&self) -> String {
        self.to_bytes().iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Decode from binary multihash bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let (code, n1) = decode_uvarint(bytes)?;
        let kind = HashKind::from_multicodec(code)?;
        let (len, n2) = decode_uvarint(&bytes[n1..])?;
        let len = len as usize;
        let start = n1 + n2;
        if bytes.len() < start + len || len != kind.digest_len() {
            return None;
        }
        Some(Multihash {
            kind,
            digest: bytes[start..start + len].to_vec(),
        })
    }

    /// Decode from a hex string.
    pub fn from_hex(hex: &str) -> Option<Self> {
        if hex.len() % 2 != 0 {
            return None;
        }
        let bytes: Option<Vec<u8>> = (0..hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).ok())
            .collect();
        Self::from_bytes(&bytes?)
    }
}

/// Error type for content store operations.
#[derive(Debug)]
pub enum StoreError {
    Sqlite(rusqlite::Error),
    InvalidHashKind(String),
    InvalidStorageKind(String),
}

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::Sqlite(e) => write!(f, "sqlite error: {e}"),
            StoreError::InvalidHashKind(s) => write!(f, "invalid hash_kind in database: {s:?}"),
            StoreError::InvalidStorageKind(s) => {
                write!(f, "invalid storage_kind in database: {s:?}")
            }
        }
    }
}

impl From<rusqlite::Error> for StoreError {
    fn from(e: rusqlite::Error) -> Self {
        StoreError::Sqlite(e)
    }
}

/// A content-addressed store backed by SQLite, mapping hashes to blobs.
pub struct ContentStore {
    conn: Connection,
}

impl ContentStore {
    /// Open (or create) a content store at the given path.
    pub fn open(path: &str) -> Result<Self, StoreError> {
        let conn = Connection::open(path)?;
        conn.execute_batch(
            "CREATE TABLE IF NOT EXISTS blobs (
                hash BLOB NOT NULL,
                hash_kind TEXT NOT NULL,
                storage_kind TEXT NOT NULL,
                data BLOB NOT NULL,
                PRIMARY KEY (hash_kind, hash)
            );",
        )?;
        Ok(ContentStore { conn })
    }

    /// Store a blob with the given hash algorithm. Returns the multihash.
    pub fn store(&self, hash_kind: HashKind, data: &[u8]) -> Result<Multihash, StoreError> {
        let digest = hash_kind.hash(data);
        self.conn.execute(
            "INSERT OR IGNORE INTO blobs (hash, hash_kind, storage_kind, data) VALUES (?1, ?2, ?3, ?4)",
            rusqlite::params![&digest[..], hash_kind.as_str(), StorageKind::Inline.as_str(), data],
        )?;
        Ok(Multihash {
            kind: hash_kind,
            digest,
        })
    }

    /// Look up a blob by its multihash. Validates hash_kind and storage_kind.
    pub fn lookup(&self, multihash: &Multihash) -> Result<Option<Vec<u8>>, StoreError> {
        let mut stmt = self.conn.prepare(
            "SELECT hash_kind, storage_kind, data FROM blobs WHERE hash_kind = ?1 AND hash = ?2",
        )?;
        let mut rows = stmt.query(rusqlite::params![
            multihash.kind.as_str(),
            &multihash.digest[..]
        ])?;
        match rows.next()? {
            Some(row) => {
                let hash_kind_str: String = row.get(0)?;
                let storage_kind_str: String = row.get(1)?;
                if HashKind::from_str(&hash_kind_str).is_none() {
                    return Err(StoreError::InvalidHashKind(hash_kind_str));
                }
                if StorageKind::from_str(&storage_kind_str).is_none() {
                    return Err(StoreError::InvalidStorageKind(storage_kind_str));
                }
                Ok(Some(row.get(2)?))
            }
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
        let mh = store.store(HashKind::Blake3, data).unwrap();
        assert_eq!(mh.kind, HashKind::Blake3);
        assert_eq!(mh.digest, blake3::hash(data).as_bytes().to_vec());
        let result = store.lookup(&mh).unwrap();
        assert_eq!(result, Some(data.to_vec()));
    }

    #[test]
    fn lookup_missing() {
        let store = ContentStore::open(":memory:").unwrap();
        let mh = Multihash {
            kind: HashKind::Blake3,
            digest: vec![0u8; 32],
        };
        assert_eq!(store.lookup(&mh).unwrap(), None);
    }

    #[test]
    fn store_idempotent() {
        let store = ContentStore::open(":memory:").unwrap();
        let data = b"test data";
        let h1 = store.store(HashKind::Blake3, data).unwrap();
        let h2 = store.store(HashKind::Blake3, data).unwrap();
        assert_eq!(h1, h2);
    }

    #[test]
    fn multihash_roundtrip_bytes() {
        let mh = Multihash {
            kind: HashKind::Blake3,
            digest: blake3::hash(b"test").as_bytes().to_vec(),
        };
        let bytes = mh.to_bytes();
        assert_eq!(bytes[0], 0x1e); // BLAKE3 multicodec
        assert_eq!(bytes[1], 0x20); // 32 bytes
        assert_eq!(bytes.len(), 34);
        let decoded = Multihash::from_bytes(&bytes).unwrap();
        assert_eq!(mh, decoded);
    }

    #[test]
    fn multihash_roundtrip_hex() {
        let mh = Multihash {
            kind: HashKind::Blake3,
            digest: blake3::hash(b"test").as_bytes().to_vec(),
        };
        let hex = mh.to_hex();
        assert!(hex.starts_with("1e20")); // BLAKE3 0x1e, length 0x20
        assert_eq!(hex.len(), 68); // 2 + 2 + 64
        let decoded = Multihash::from_hex(&hex).unwrap();
        assert_eq!(mh, decoded);
    }

    #[test]
    fn multihash_from_hex_rejects_invalid() {
        assert!(Multihash::from_hex("").is_none());
        assert!(Multihash::from_hex("ff20" /* unknown code */).is_none());
        assert!(Multihash::from_hex("1e1f" /* wrong length */).is_none());
        assert!(Multihash::from_hex("zzzz").is_none());
    }

    #[test]
    fn validates_hash_kind_in_db() {
        let store = ContentStore::open(":memory:").unwrap();
        // Insert a row with an unknown hash_kind directly
        store
            .conn
            .execute(
                "INSERT INTO blobs (hash, hash_kind, storage_kind, data) VALUES (?1, ?2, ?3, ?4)",
                rusqlite::params![&[0u8; 32][..], "unknown_hash", "inline", b"data"],
            )
            .unwrap();
        // Lookup won't find it since we query by hash_kind
        let mh = Multihash {
            kind: HashKind::Blake3,
            digest: vec![0u8; 32],
        };
        assert_eq!(store.lookup(&mh).unwrap(), None);
    }

    #[test]
    fn validates_storage_kind_in_db() {
        let store = ContentStore::open(":memory:").unwrap();
        let digest = blake3::hash(b"data").as_bytes().to_vec();
        // Insert a row with an unknown storage_kind directly
        store
            .conn
            .execute(
                "INSERT INTO blobs (hash, hash_kind, storage_kind, data) VALUES (?1, ?2, ?3, ?4)",
                rusqlite::params![&digest[..], "blake3", "unknown_storage", b"data"],
            )
            .unwrap();
        let mh = Multihash {
            kind: HashKind::Blake3,
            digest,
        };
        match store.lookup(&mh) {
            Err(StoreError::InvalidStorageKind(s)) => assert_eq!(s, "unknown_storage"),
            other => panic!("expected InvalidStorageKind, got {other:?}"),
        }
    }
}
