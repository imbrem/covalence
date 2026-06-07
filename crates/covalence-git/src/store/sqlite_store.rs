//! SQLite-backed git object store.
//!
//! Stores git objects in two tables: `blobs` (O256-keyed content) and
//! `git_objects` (git OID → blob hash mapping). Supports shallow entries
//! (known OID, no data) for partial/lazy fetches.

use std::sync::{Arc, Mutex};

use covalence_hash::{O256, gix_hash};
use covalence_sqlite::Connection;
use covalence_store::StoreError;

use super::backend::{GitBackend, GitObject, GitObjectKind};

/// A [`GitBackend`] backed by SQLite.
///
/// Two tables in one database:
/// - `blobs`: content-addressed storage keyed by 32-byte O256 hash
/// - `git_objects`: maps git OIDs to blob hashes with object kind metadata
///
/// Clone is cheap (Arc internals). Thread-safe via internal Mutex.
#[derive(Clone)]
pub struct GitStore {
    conn: Arc<Mutex<Connection>>,
    kind: gix_hash::Kind,
}

impl GitStore {
    fn io_err<E: std::fmt::Display>(e: E) -> StoreError {
        StoreError::Io(e.to_string())
    }

    fn has_git_object(&self, id: &gix_hash::ObjectId, with_data: bool) -> bool {
        let conn = self.conn.lock().unwrap();
        let sql = if with_data {
            "SELECT 1 FROM git_objects WHERE git_oid = ?1 AND blob_hash IS NOT NULL"
        } else {
            "SELECT 1 FROM git_objects WHERE git_oid = ?1"
        };
        conn.query_row(sql, [id.as_bytes()], |_| Ok(())).is_ok()
    }

    fn all_data_by_tree_membership(&self, is_tree: bool) -> Result<Vec<Vec<u8>>, StoreError> {
        let conn = self.conn.lock().unwrap();
        let sql = if is_tree {
            "SELECT data FROM blobs WHERE hash IN (SELECT hash FROM cov_trees)"
        } else {
            "SELECT data FROM blobs WHERE hash NOT IN (SELECT hash FROM cov_trees)"
        };
        let mut stmt = conn.prepare(sql).map_err(Self::io_err)?;
        let rows = stmt
            .query_map([], |row| row.get::<_, Vec<u8>>(0))
            .map_err(Self::io_err)?;
        rows.collect::<Result<Vec<_>, _>>().map_err(Self::io_err)
    }

    /// Open a persistent store at the given path.
    pub fn open(
        path: impl AsRef<std::path::Path>,
        kind: gix_hash::Kind,
    ) -> Result<Self, covalence_sqlite::Error> {
        let conn = covalence_sqlite::open(path)?;
        Self::init(conn, kind)
    }

    /// Open an in-memory store (useful for testing).
    pub fn memory(kind: gix_hash::Kind) -> Result<Self, covalence_sqlite::Error> {
        let conn = covalence_sqlite::open_memory()?;
        Self::init(conn, kind)
    }

    fn init(conn: Connection, kind: gix_hash::Kind) -> Result<Self, covalence_sqlite::Error> {
        conn.execute_batch(
            "CREATE TABLE IF NOT EXISTS blobs (
                hash BLOB PRIMARY KEY, data BLOB NOT NULL
            ) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS git_objects (
                git_oid   BLOB PRIMARY KEY,
                blob_hash BLOB,
                kind      TEXT
            ) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS cov_trees (
                hash BLOB PRIMARY KEY
            ) WITHOUT ROWID;",
        )?;
        Ok(Self {
            conn: Arc::new(Mutex::new(conn)),
            kind,
        })
    }

    /// Compute the git object ID for the given type and data.
    fn hash_object(&self, kind: GitObjectKind, data: &[u8]) -> gix_hash::ObjectId {
        let mut hasher = gix_hash::hasher(self.kind);
        let header = format!("{} {}\0", kind.as_str(), data.len());
        hasher.update(header.as_bytes());
        hasher.update(data);
        hasher.try_finalize().expect("git hash finalize")
    }

    /// Register a git OID without data (shallow/unfetched entry).
    ///
    /// If the OID already exists (shallow or full), this is a no-op.
    pub fn insert_shallow(
        &self,
        id: &gix_hash::ObjectId,
        kind: Option<GitObjectKind>,
    ) -> Result<(), StoreError> {
        let conn = self.conn.lock().unwrap();
        conn.execute(
            "INSERT OR IGNORE INTO git_objects (git_oid, blob_hash, kind) VALUES (?1, NULL, ?2)",
            covalence_sqlite::params![id.as_bytes(), kind.map(|k| k.as_str())],
        )
        .map_err(Self::io_err)?;
        Ok(())
    }

    /// Check whether a git OID is registered at all (including shallow entries).
    pub fn contains_oid(&self, id: &gix_hash::ObjectId) -> bool {
        self.has_git_object(id, false)
    }

    /// Check whether a git OID has associated data (not shallow).
    pub fn has_data(&self, id: &gix_hash::ObjectId) -> bool {
        self.has_git_object(id, true)
    }

    /// Get the object kind for a registered OID.
    pub fn get_kind(&self, id: &gix_hash::ObjectId) -> Option<GitObjectKind> {
        let conn = self.conn.lock().unwrap();
        conn.query_row(
            "SELECT kind FROM git_objects WHERE git_oid = ?1",
            [id.as_bytes()],
            |row| row.get::<_, Option<String>>(0),
        )
        .ok()
        .flatten()
        .and_then(|s| s.parse().ok())
    }

    /// Number of registered git objects (including shallow entries).
    pub fn len(&self) -> usize {
        let conn = self.conn.lock().unwrap();
        conn.query_row("SELECT COUNT(*) FROM git_objects", [], |row| {
            row.get::<_, i64>(0).map(|n| n as usize)
        })
        .unwrap_or(0)
    }

    /// Whether the store has no registered git objects.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns data for all non-tree blob entries (plain content blobs).
    pub fn all_blob_data(&self) -> Result<Vec<Vec<u8>>, StoreError> {
        self.all_data_by_tree_membership(false)
    }

    /// Returns data for all covalence tree entries.
    pub fn all_tree_data(&self) -> Result<Vec<Vec<u8>>, StoreError> {
        self.all_data_by_tree_membership(true)
    }

    /// Find a git OID whose data hashes to `target`.
    ///
    /// Multiple git OIDs can in principle share the same `blob_hash`
    /// (e.g. a tree and a blob with byte-identical payloads); this returns the
    /// lexicographically-smallest OID for determinism. Shallow entries
    /// (`blob_hash IS NULL`) are skipped.
    pub fn git_oid_for_blob_hash(
        &self,
        target: &O256,
    ) -> Result<Option<gix_hash::ObjectId>, StoreError> {
        let conn = self.conn.lock().unwrap();
        let row: Option<Vec<u8>> = conn
            .query_row(
                "SELECT git_oid FROM git_objects
                 WHERE blob_hash = ?1
                 ORDER BY git_oid ASC LIMIT 1",
                [target.as_bytes().as_slice()],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .ok();
        Ok(row.map(|bytes| gix_hash::ObjectId::from_bytes_or_panic(&bytes)))
    }

    /// Retrieve all persisted covalence tree hashes.
    ///
    /// These are O256 keyed hashes stored in the `cov_trees` table,
    /// corresponding to covalence-format trees converted from git trees.
    pub fn cov_tree_hashes(&self) -> Vec<O256> {
        let conn = self.conn.lock().unwrap();
        let mut stmt = match conn.prepare("SELECT hash FROM cov_trees") {
            Ok(s) => s,
            Err(_) => return Vec::new(),
        };
        let rows = match stmt.query_map([], |row| {
            let bytes: Vec<u8> = row.get(0)?;
            Ok(bytes)
        }) {
            Ok(r) => r,
            Err(_) => return Vec::new(),
        };
        rows.filter_map(|r| {
            let bytes = r.ok()?;
            let arr: [u8; 32] = bytes.try_into().ok()?;
            Some(O256::from_bytes(arr))
        })
        .collect()
    }
}

#[cfg(feature = "clone")]
impl GitStore {
    /// Convert all git tree objects into covalence-format trees and store them.
    ///
    /// For each git tree, this:
    /// 1. Parses the git tree format (`mode name\0hash_bytes`)
    /// 2. Maps child git hashes to O256 (blob children → `O256::blob(data)`,
    ///    tree children → recursively converted keyed hash)
    /// 3. Builds a covalence `Table<Dir>` and stores it with the keyed tree hash
    /// 4. Records the hash in `cov_trees` for persistence across sessions
    ///
    /// Returns a map from git tree OID → covalence O256 tree hash.
    pub fn convert_trees(&self) -> Result<Vec<(gix_hash::ObjectId, O256)>, StoreError> {
        use std::collections::HashMap;

        // Collect all tree OIDs.
        let tree_oids: Vec<(gix_hash::ObjectId, Vec<u8>)> = {
            let conn = self.conn.lock().unwrap();
            let mut stmt = conn
                .prepare(
                    "SELECT g.git_oid, b.data FROM git_objects g
                     JOIN blobs b ON g.blob_hash = b.hash
                     WHERE g.kind = 'tree'",
                )
                .map_err(Self::io_err)?;
            stmt.query_map([], |row| {
                let oid_bytes: Vec<u8> = row.get(0)?;
                let data: Vec<u8> = row.get(1)?;
                Ok((oid_bytes, data))
            })
            .map_err(Self::io_err)?
            .filter_map(|r| {
                let (oid_bytes, data) = r.ok()?;
                let oid = gix_hash::ObjectId::from_bytes_or_panic(&oid_bytes);
                Some((oid, data))
            })
            .collect()
        };

        let hash_len = self.kind.len_in_bytes();

        // Memoize: git OID → covalence O256 tree hash.
        let mut tree_cache: HashMap<gix_hash::ObjectId, O256> = HashMap::new();
        // Also store tree data for building: git OID → raw git tree bytes.
        let mut tree_data: HashMap<gix_hash::ObjectId, Vec<u8>> = HashMap::new();
        for (oid, data) in &tree_oids {
            tree_data.insert(*oid, data.clone());
        }

        // Recursively convert trees (bottom-up via memoization).
        let mut results = Vec::new();
        for (oid, _) in &tree_oids {
            let cov_hash =
                self.convert_tree_recursive(*oid, &tree_data, &mut tree_cache, hash_len)?;
            results.push((*oid, cov_hash));
        }

        Ok(results)
    }

    /// Recursively convert a single git tree to covalence format.
    fn convert_tree_recursive(
        &self,
        oid: gix_hash::ObjectId,
        tree_data: &std::collections::HashMap<gix_hash::ObjectId, Vec<u8>>,
        cache: &mut std::collections::HashMap<gix_hash::ObjectId, O256>,
        hash_len: usize,
    ) -> Result<O256, StoreError> {
        if let Some(&cached) = cache.get(&oid) {
            return Ok(cached);
        }

        let data = tree_data
            .get(&oid)
            .ok_or_else(|| StoreError::Io(format!("tree {oid} not found")))?;

        let entries = covalence_object::parse_git_tree(data, hash_len)
            .map_err(|e| StoreError::Io(format!("parse git tree {oid}: {e}")))?;

        let mut dir_rows: Vec<covalence_object::DirRow<Vec<u8>>> =
            Vec::with_capacity(entries.len());

        for entry in entries {
            let mode = covalence_object::DirMode::from_git_mode(entry.mode)
                .map_err(|e| StoreError::Io(format!("bad mode in tree {oid}: {e}")))?;

            let child_git_oid = gix_hash::ObjectId::from_bytes_or_panic(entry.hash);
            let child_o256 = if mode.is_dir() {
                // Child is a subtree — recursively convert.
                self.convert_tree_recursive(child_git_oid, tree_data, cache, hash_len)?
            } else if mode == covalence_object::DirMode::SUBMODULE {
                // Submodules reference commits in external repos — hash the OID directly.
                O256::blob(child_git_oid.as_bytes())
            } else {
                // Child is a blob/symlink — use its O256::blob(data) hash.
                self.blob_hash_for_oid(&child_git_oid)?
            };

            dir_rows.push(covalence_object::DirRow {
                name: entry.name.to_vec(),
                mode,
                child: child_o256,
            });
        }

        // Build covalence table (sorts rows via Dir::prepare).
        let mut builder = covalence_object::TableBuilder::new(covalence_object::Dir);
        for row in dir_rows {
            builder.push_row(row);
        }
        let table = builder.build();
        let tree_hash = table.dir_hash();
        let table_bytes = table.as_bytes();

        // Store the covalence tree in the shared blobs table.
        let conn = self.conn.lock().unwrap();
        conn.execute(
            "INSERT OR IGNORE INTO blobs (hash, data) VALUES (?1, ?2)",
            covalence_sqlite::params![tree_hash.as_bytes().as_slice(), table_bytes],
        )
        .map_err(Self::io_err)?;

        // Persist the tree hash for cross-session discovery.
        conn.execute(
            "INSERT OR IGNORE INTO cov_trees (hash) VALUES (?1)",
            [tree_hash.as_bytes().as_slice()],
        )
        .map_err(Self::io_err)?;

        drop(conn);
        cache.insert(oid, tree_hash);
        Ok(tree_hash)
    }

    /// Look up the O256 blob hash for a git OID.
    fn blob_hash_for_oid(&self, oid: &gix_hash::ObjectId) -> Result<O256, StoreError> {
        let conn = self.conn.lock().unwrap();
        conn.query_row(
            "SELECT blob_hash FROM git_objects WHERE git_oid = ?1",
            [oid.as_bytes()],
            |row| {
                let bytes: Vec<u8> = row.get(0)?;
                Ok(bytes)
            },
        )
        .map_err(|_| StoreError::Io(format!("git OID not found: {oid}")))
        .and_then(|bytes| {
            let arr: [u8; 32] = bytes
                .try_into()
                .map_err(|_| StoreError::Io("invalid O256 in git_objects".to_string()))?;
            Ok(O256::from_bytes(arr))
        })
    }
}

impl GitBackend for GitStore {
    fn read_object(&self, id: &gix_hash::ObjectId) -> Result<GitObject, StoreError> {
        let conn = self.conn.lock().unwrap();
        conn.query_row(
            "SELECT g.kind, b.data FROM git_objects g
             JOIN blobs b ON g.blob_hash = b.hash
             WHERE g.git_oid = ?1",
            [id.as_bytes()],
            |row| {
                let kind_str: String = row.get(0)?;
                let data: Vec<u8> = row.get(1)?;
                Ok((kind_str, data))
            },
        )
        .map_err(|_| StoreError::Io(format!("object not found: {id}")))
        .and_then(|(kind_str, data)| {
            let kind: GitObjectKind = kind_str
                .parse()
                .map_err(|_| StoreError::Io(format!("unknown object kind: {kind_str}")))?;
            Ok(GitObject { kind, data })
        })
    }

    fn write_object(
        &self,
        kind: GitObjectKind,
        data: &[u8],
    ) -> Result<gix_hash::ObjectId, StoreError> {
        let git_oid = self.hash_object(kind, data);
        let blob_hash = O256::blob(data);

        let conn = self.conn.lock().unwrap();

        // Insert body into blobs (content-addressed, idempotent).
        conn.execute(
            "INSERT OR IGNORE INTO blobs (hash, data) VALUES (?1, ?2)",
            covalence_sqlite::params![blob_hash.as_bytes().as_slice(), data],
        )
        .map_err(Self::io_err)?;

        // Upsert git_objects — upgrades shallow entries to full.
        conn.execute(
            "INSERT OR REPLACE INTO git_objects (git_oid, blob_hash, kind) VALUES (?1, ?2, ?3)",
            covalence_sqlite::params![
                git_oid.as_bytes(),
                blob_hash.as_bytes().as_slice(),
                kind.as_str()
            ],
        )
        .map_err(Self::io_err)?;

        Ok(git_oid)
    }

    fn contains_object(&self, id: &gix_hash::ObjectId) -> bool {
        self.has_data(id)
    }

    fn hash_kind(&self) -> gix_hash::Kind {
        self.kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_store::ContentStore;

    use super::super::GitObjectStore;

    fn store() -> GitStore {
        GitStore::memory(gix_hash::Kind::Sha1).unwrap()
    }

    // --- 1. Round-trip per type (SHA-1) ---

    #[test]
    fn round_trip_blob() {
        let s = store();
        let data = b"hello blob";
        let id = s.write_object(GitObjectKind::Blob, data).unwrap();
        let obj = s.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, data);
    }

    #[test]
    fn round_trip_tree() {
        let s = store();
        let data = b"100644 file\0\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10\x11\x12\x13\x14";
        let id = s.write_object(GitObjectKind::Tree, data).unwrap();
        let obj = s.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Tree);
        assert_eq!(obj.data, data);
    }

    #[test]
    fn round_trip_commit() {
        let s = store();
        let data = b"tree 0000000000000000000000000000000000000000\nauthor A <a@b> 0 +0000\n\ntest";
        let id = s.write_object(GitObjectKind::Commit, data).unwrap();
        let obj = s.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Commit);
        assert_eq!(obj.data, data);
    }

    #[test]
    fn round_trip_tag() {
        let s = store();
        let data = b"object 0000000000000000000000000000000000000000\ntype commit\ntag v1\n\n";
        let id = s.write_object(GitObjectKind::Tag, data).unwrap();
        let obj = s.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Tag);
        assert_eq!(obj.data, data);
    }

    // --- 2. SHA-256 round-trip ---

    #[test]
    fn round_trip_sha256() {
        let s = GitStore::memory(gix_hash::Kind::Sha256).unwrap();
        let data = b"sha256 test";
        let id = s.write_object(GitObjectKind::Blob, data).unwrap();
        assert_eq!(id, covalence_hash::git::blob_sha256("sha256 test"));
        let obj = s.read_object(&id).unwrap();
        assert_eq!(obj.kind, GitObjectKind::Blob);
        assert_eq!(obj.data, data);
    }

    // --- 3. Idempotent writes ---

    #[test]
    fn idempotent_write() {
        let s = store();
        let data = b"same data";
        let id1 = s.write_object(GitObjectKind::Blob, data).unwrap();
        let id2 = s.write_object(GitObjectKind::Blob, data).unwrap();
        assert_eq!(id1, id2);
        assert_eq!(s.len(), 1);
    }

    // --- 4. Missing object → error ---

    #[test]
    fn missing_object_error() {
        let s = store();
        let fake =
            gix_hash::ObjectId::from_hex(b"0000000000000000000000000000000000000000").unwrap();
        assert!(!s.contains_object(&fake));
        assert!(s.read_object(&fake).is_err());
    }

    // --- 5. Shallow: contains_oid true, contains_object false, read fails ---

    #[test]
    fn shallow_entry() {
        let s = store();
        let fake =
            gix_hash::ObjectId::from_hex(b"abcdef0123456789abcdef0123456789abcdef01").unwrap();
        s.insert_shallow(&fake, Some(GitObjectKind::Commit))
            .unwrap();

        assert!(s.contains_oid(&fake));
        assert!(!s.contains_object(&fake)); // no data
        assert!(!s.has_data(&fake));
        assert_eq!(s.get_kind(&fake), Some(GitObjectKind::Commit));
        assert!(s.read_object(&fake).is_err());
    }

    // --- 6. Shallow then fill ---

    #[test]
    fn shallow_then_fill() {
        let s = store();
        let data = b"fill me";

        // Compute the real OID so we can register it as shallow first.
        let oid = {
            let mut hasher = gix_hash::hasher(gix_hash::Kind::Sha1);
            let header = format!("blob {}\0", data.len());
            hasher.update(header.as_bytes());
            hasher.update(data);
            hasher.try_finalize().unwrap()
        };

        s.insert_shallow(&oid, Some(GitObjectKind::Blob)).unwrap();
        assert!(s.contains_oid(&oid));
        assert!(!s.has_data(&oid));

        // Fill with write_object (upgrades shallow → full).
        let written = s.write_object(GitObjectKind::Blob, data).unwrap();
        assert_eq!(written, oid);
        assert!(s.has_data(&oid));
        assert!(s.contains_object(&oid));
        let obj = s.read_object(&oid).unwrap();
        assert_eq!(obj.data, data);
    }

    // --- 7. Shallow with unknown kind ---

    #[test]
    fn shallow_unknown_kind() {
        let s = store();
        let fake =
            gix_hash::ObjectId::from_hex(b"1111111111111111111111111111111111111111").unwrap();
        s.insert_shallow(&fake, None).unwrap();
        assert!(s.contains_oid(&fake));
        assert_eq!(s.get_kind(&fake), None);
    }

    // --- 8. Duplicate shallow inserts ignored ---

    #[test]
    fn duplicate_shallow_ignored() {
        let s = store();
        let fake =
            gix_hash::ObjectId::from_hex(b"2222222222222222222222222222222222222222").unwrap();
        s.insert_shallow(&fake, Some(GitObjectKind::Blob)).unwrap();
        // Second insert with different kind is ignored (INSERT OR IGNORE).
        s.insert_shallow(&fake, Some(GitObjectKind::Tree)).unwrap();
        assert_eq!(s.get_kind(&fake), Some(GitObjectKind::Blob));
        assert_eq!(s.len(), 1);
    }

    // --- 9. Body deduplication ---

    #[test]
    fn body_dedup() {
        let s = store();
        let data = b"shared body";

        let blob_id = s.write_object(GitObjectKind::Blob, data).unwrap();
        let tree_id = s.write_object(GitObjectKind::Tree, data).unwrap();
        // Different git OIDs (different type headers).
        assert_ne!(blob_id, tree_id);
        // But both reference the same O256 blob hash → only one blobs row.
        assert_eq!(s.len(), 2); // 2 git_objects

        // Verify both read back correctly.
        let obj1 = s.read_object(&blob_id).unwrap();
        assert_eq!(obj1.kind, GitObjectKind::Blob);
        assert_eq!(obj1.data, data);

        let obj2 = s.read_object(&tree_id).unwrap();
        assert_eq!(obj2.kind, GitObjectKind::Tree);
        assert_eq!(obj2.data, data);

        // Verify only 1 row in blobs.
        let conn = s.conn.lock().unwrap();
        let blob_count: i64 = conn
            .query_row("SELECT COUNT(*) FROM blobs", [], |row| row.get(0))
            .unwrap();
        assert_eq!(blob_count, 1);
    }

    // --- 10. len / is_empty ---

    #[test]
    fn len_and_is_empty() {
        let s = store();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);

        s.write_object(GitObjectKind::Blob, b"a").unwrap();
        assert!(!s.is_empty());
        assert_eq!(s.len(), 1);

        s.write_object(GitObjectKind::Blob, b"b").unwrap();
        assert_eq!(s.len(), 2);

        // Shallow entries count too.
        let fake =
            gix_hash::ObjectId::from_hex(b"3333333333333333333333333333333333333333").unwrap();
        s.insert_shallow(&fake, None).unwrap();
        assert_eq!(s.len(), 3);
    }

    // --- 11. GitObjectStore adapter integration ---

    #[test]
    fn git_object_store_adapter() {
        let backend = store();
        let adapter = GitObjectStore::new(backend);

        let data = b"adapter test";
        let id = ContentStore::insert(&adapter, data.as_slice()).unwrap();
        assert!(ContentStore::contains(&adapter, &id));
        assert_eq!(ContentStore::get(&adapter, &id).unwrap(), data);
    }
}
