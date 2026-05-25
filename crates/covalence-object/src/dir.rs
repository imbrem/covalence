use std::collections::BTreeMap;

use covalence_hash::O256;

use crate::table::{
    FieldSpec, RowCodec, RowSchema, Table, TableError, min_bytes, read_le, write_le,
};

/// The mode of a directory entry, stored as a u16 holding the git octal mode.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DirMode(pub u16);

impl DirMode {
    /// Regular file (git `100644`).
    pub const REGULAR: Self = Self(0o100644);
    /// Executable file (git `100755`).
    pub const EXECUTABLE: Self = Self(0o100755);
    /// Symbolic link (git `120000`).
    pub const SYMLINK: Self = Self(0o120000);
    /// Directory / tree (git `40000`).
    pub const DIR: Self = Self(0o40000);
    /// Git submodule (git `160000`).
    pub const SUBMODULE: Self = Self(0o160000);

    /// Whether this mode represents a tree/directory.
    pub fn is_dir(self) -> bool {
        self == Self::DIR
    }

    /// Compute the O256 mode ref for use in directory hashing.
    /// Key = O256::blob("GIT_MODE"), data = mode LE bytes.
    pub fn mode_ref(self) -> O256 {
        let key = O256::blob("GIT_MODE");
        let mut hasher = covalence_hash::blake3::Hasher::new_keyed(key.as_bytes());
        hasher.update(&self.0.to_le_bytes());
        O256::from_bytes(*hasher.finalize().as_bytes())
    }

    /// Parse a git tree mode string (e.g. `b"100644"`) into a `DirMode`.
    pub fn from_git_mode(mode: &[u8]) -> Result<Self, TableError> {
        match mode {
            b"100644" => Ok(Self::REGULAR),
            b"100755" => Ok(Self::EXECUTABLE),
            b"120000" => Ok(Self::SYMLINK),
            b"40000" => Ok(Self::DIR),
            b"160000" => Ok(Self::SUBMODULE),
            _ => Err(TableError::InvalidGitTree(format!(
                "unknown mode: {:?}",
                String::from_utf8_lossy(mode)
            ))),
        }
    }

    /// Git mode octal string for serialization.
    pub fn git_mode_str(self) -> &'static str {
        match self {
            Self::REGULAR => "100644",
            Self::EXECUTABLE => "100755",
            Self::SYMLINK => "120000",
            Self::DIR => "40000",
            Self::SUBMODULE => "160000",
            _ => panic!("no git mode string for DirMode({})", self.0),
        }
    }

    /// Human-readable name for the mode.
    pub fn name(self) -> &'static str {
        match self {
            Self::REGULAR => "regular",
            Self::EXECUTABLE => "executable",
            Self::SYMLINK => "symlink",
            Self::DIR => "dir",
            Self::SUBMODULE => "submodule",
            _ => "unknown",
        }
    }
}

/// A directory row, generic over the name type.
///
/// - `DirRow<Vec<u8>>` — owned, used for building tables.
/// - `DirRow<&[u8]>` — borrowed, returned by the parser.
/// - `DirRow<&str>` — convenient for building directories by name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DirRow<N> {
    pub name: N,
    pub mode: DirMode,
    pub child: O256,
}

/// Hash a sorted, unique directory listing into an [`O256`].
pub trait HashDir {
    fn hash_dir<N: AsRef<[u8]>>(&self, rows: &[DirRow<N>]) -> O256;
}

/// BLAKE3 keyed-hash implementation: domain-separated from blob hashes.
///
/// Each entry contributes `{mode_ref_32bytes}{name}\0{hash_32bytes}`.
/// The concatenated entries are hashed with BLAKE3 keyed mode using
/// `key = O256::blob("tree")`, ensuring disjointness from plain BLAKE3 hashes.
impl HashDir for () {
    fn hash_dir<N: AsRef<[u8]>>(&self, rows: &[DirRow<N>]) -> O256 {
        debug_assert!(
            rows.windows(2)
                .all(|w| w[0].name.as_ref() < w[1].name.as_ref()),
            "entries must be sorted and unique by name",
        );

        let key = O256::blob("tree");
        let mut hasher = covalence_hash::blake3::Hasher::new_keyed(key.as_bytes());
        for row in rows {
            hasher.update(row.mode.mode_ref().as_bytes());
            hasher.update(row.name.as_ref());
            hasher.update(&[0]);
            hasher.update(row.child.as_bytes());
        }
        O256::from_bytes(*hasher.finalize().as_bytes())
    }
}

/// Hash a sorted, unique directory listing using BLAKE3 keyed mode.
pub fn dir_hash<N: AsRef<[u8]>>(rows: &[DirRow<N>]) -> O256 {
    ().hash_dir(rows)
}

/// Collects directory entries, sorts by name, and deduplicates (last-wins).
///
/// Callers never need to worry about ordering or duplicate names:
///
/// ```
/// use covalence_object::{DirBuilder, DirMode, DirRow};
/// use covalence_hash::O256;
///
/// let mut b = DirBuilder::new();
/// b.entry("z.txt", DirMode::REGULAR, O256::blob("z"))
///  .entry("a.txt", DirMode::REGULAR, O256::blob("a"));
///
/// let entries = b.build();
/// assert_eq!(entries[0].name, "a.txt");
/// assert_eq!(entries[1].name, "z.txt");
/// ```
pub struct DirBuilder<'a> {
    entries: BTreeMap<&'a str, (DirMode, O256)>,
}

impl<'a> DirBuilder<'a> {
    /// Create an empty builder.
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::new(),
        }
    }

    /// Add or replace an entry. If `name` already exists, the new value wins.
    pub fn entry(&mut self, name: &'a str, mode: DirMode, child: O256) -> &mut Self {
        self.entries.insert(name, (mode, child));
        self
    }

    /// Build a sorted, deduplicated `Vec<DirRow<&str>>`.
    pub fn build(&self) -> Vec<DirRow<&'a str>> {
        self.iter().collect()
    }

    /// Iterate over entries in sorted order.
    pub fn iter(&self) -> impl Iterator<Item = DirRow<&'a str>> + '_ {
        self.entries
            .iter()
            .map(|(&name, &(mode, child))| DirRow { name, mode, child })
    }

    /// Returns `true` if the builder contains no entries.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns the number of unique entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Hash the directory with the default BLAKE3 keyed-hash.
    pub fn hash(&self) -> O256 {
        let entries = self.build();
        ().hash_dir(&entries)
    }

    /// Hash the directory with a custom [`HashDir`] implementation.
    pub fn hash_with(&self, ctx: &impl HashDir) -> O256 {
        let entries = self.build();
        ctx.hash_dir(&entries)
    }
}

impl Default for DirBuilder<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// Directory table schema: `(name: Blob, mode: Fixed(2), child: Dep)`.
///
/// - Mode is stored inline as a 2-byte LE u16.
/// - Each child `O256` is registered as a dep.
/// - `collect()` auto-pushes deps when rows are added.
pub struct Dir;

impl RowCodec for Dir {
    type Row = DirRow<Vec<u8>>;
    type RowRef<'a> = DirRow<&'a [u8]>;

    fn collect(&self, row: &DirRow<Vec<u8>>, _refs: &mut Vec<O256>, deps: &mut Vec<O256>) {
        deps.push(row.child);
    }

    fn row_schema(&self, _num_refs: usize, num_deps: usize) -> RowSchema {
        RowSchema::new(vec![
            FieldSpec::blob(),
            FieldSpec::fixed(2),
            FieldSpec::dep_index(min_bytes(num_deps)),
        ])
    }

    fn encode(
        &self,
        row: &DirRow<Vec<u8>>,
        _sorted_refs: &[O256],
        sorted_deps: &[O256],
        _ref_w: u8,
        dep_w: u8,
    ) -> Vec<Vec<u8>> {
        let dep_idx = sorted_deps
            .binary_search(&row.child)
            .expect("child dep missing from sorted deps");

        let mut dep_bytes = Vec::new();
        write_le(dep_idx as u64, dep_w as usize, &mut dep_bytes);

        vec![
            row.name.clone(),
            row.mode.0.to_le_bytes().to_vec(),
            dep_bytes,
        ]
    }

    fn decode<'a>(
        &self,
        fields: Vec<&'a [u8]>,
        _refs: &[O256],
        deps: &[O256],
    ) -> Result<DirRow<&'a [u8]>, TableError> {
        if fields.len() != 3 {
            return Err(TableError::SchemaMismatch {
                expected: 3,
                got: fields.len(),
            });
        }

        let name = fields[0];
        let mode_val = u16::from_le_bytes([fields[1][0], fields[1][1]]);
        let mode = DirMode(mode_val);
        let dep_idx = read_le(fields[2], fields[2].len()) as usize;
        let child = deps[dep_idx];

        Ok(DirRow { name, mode, child })
    }

    fn prepare(&self, rows: &mut [DirRow<Vec<u8>>]) {
        rows.sort_by(|a, b| a.name.cmp(&b.name));
        assert!(
            rows.windows(2).all(|w| w[0].name != w[1].name),
            "directory rows must have unique names",
        );
    }
}

impl Table<Dir> {
    /// Look up a directory entry by name (binary search, O(log n)).
    ///
    /// Relies on [`Dir::prepare`] having sorted rows by name.
    pub fn get(&self, name: &[u8]) -> Result<Option<DirRow<&[u8]>>, TableError> {
        let n = self.num_entries();
        let mut lo = 0usize;
        let mut hi = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let row = self.row(mid)?;
            match row.name.cmp(name) {
                std::cmp::Ordering::Equal => return Ok(Some(row)),
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
            }
        }
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// Git tree serialization (behind `git` feature)
// ---------------------------------------------------------------------------

/// Serialize directory rows in git tree format.
///
/// Each entry is `"{mode} {name}\0{hash_bytes}"` where mode is the octal
/// string (`"100644"` for blobs, `"40000"` for directories) and `hash_bytes`
/// is the raw hash truncated to `hash_len` bytes.
///
/// Rows must be sorted and unique by name (debug-asserted).
#[cfg(feature = "git")]
pub fn git_tree_bytes<N: AsRef<[u8]>>(rows: &[DirRow<N>], hash_len: usize) -> Vec<u8> {
    debug_assert!(
        rows.windows(2)
            .all(|w| w[0].name.as_ref() < w[1].name.as_ref()),
        "rows must be sorted and unique by name",
    );

    let mut buf = Vec::new();
    for row in rows {
        buf.extend_from_slice(row.mode.git_mode_str().as_bytes());
        buf.push(b' ');
        buf.extend_from_slice(row.name.as_ref());
        buf.push(0);
        buf.extend_from_slice(&row.child.as_bytes()[..hash_len]);
    }
    buf
}

/// Hash directory rows as a git tree using SHA-1.
///
/// Returns an `O256` with the 20-byte SHA-1 in the first 20 bytes and zeros
/// in the remaining 12.
#[cfg(feature = "git")]
pub fn git_tree_sha1<N: AsRef<[u8]>>(rows: &[DirRow<N>]) -> O256 {
    let buf = git_tree_bytes(rows, 20);
    let oid = covalence_hash::git::tree_sha1(&buf);
    let mut out = [0u8; 32];
    out[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());
    O256::from_bytes(out)
}

/// Hash directory rows as a git tree using SHA-256.
#[cfg(feature = "git")]
pub fn git_tree_sha256<N: AsRef<[u8]>>(rows: &[DirRow<N>]) -> O256 {
    let buf = git_tree_bytes(rows, 32);
    let oid = covalence_hash::git::tree_sha256(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(oid.as_bytes());
    O256::from_bytes(out)
}

/// A raw entry parsed from git tree bytes.
#[cfg(feature = "git")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitTreeEntry<'a> {
    pub mode: &'a [u8],
    pub name: &'a [u8],
    pub hash: &'a [u8],
}

/// Parse raw git tree body bytes into entries.
///
/// Each entry in a git tree is `"{mode} {name}\0{hash_bytes}"` where `hash_bytes`
/// is `hash_len` bytes (20 for SHA-1, 32 for SHA-256).
#[cfg(feature = "git")]
pub fn parse_git_tree(data: &[u8], hash_len: usize) -> Result<Vec<GitTreeEntry<'_>>, TableError> {
    let mut entries = Vec::new();
    let mut pos = 0;
    while pos < data.len() {
        // Find the space separating mode from name.
        let space = data[pos..]
            .iter()
            .position(|&b| b == b' ')
            .ok_or_else(|| TableError::InvalidGitTree("missing space after mode".to_string()))?;
        let mode = &data[pos..pos + space];
        pos += space + 1;

        // Find the null byte terminating the name.
        let null = data[pos..]
            .iter()
            .position(|&b| b == 0)
            .ok_or_else(|| TableError::InvalidGitTree("missing null after name".to_string()))?;
        let name = &data[pos..pos + null];
        pos += null + 1;

        // Read hash_len bytes.
        if pos + hash_len > data.len() {
            return Err(TableError::InvalidGitTree(format!(
                "truncated hash: need {} bytes at offset {}, got {}",
                hash_len,
                pos,
                data.len() - pos
            )));
        }
        let hash = &data[pos..pos + hash_len];
        pos += hash_len;

        entries.push(GitTreeEntry { mode, name, hash });
    }
    Ok(entries)
}

/// Parse a git tree and convert to `DirRow` entries.
///
/// `map_hash` converts raw git hash bytes (20 or 32) to `O256`.
#[cfg(feature = "git")]
pub fn git_tree_to_dir_rows(
    data: &[u8],
    hash_len: usize,
    mut map_hash: impl FnMut(&[u8]) -> O256,
) -> Result<Vec<DirRow<Vec<u8>>>, TableError> {
    let entries = parse_git_tree(data, hash_len)?;
    let mut rows = Vec::with_capacity(entries.len());
    for entry in entries {
        let mode = DirMode::from_git_mode(entry.mode)?;
        let child = map_hash(entry.hash);
        rows.push(DirRow {
            name: entry.name.to_vec(),
            mode,
            child,
        });
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table::TableBuilder;

    // --- HashDir / DirBuilder tests (moved from covalence-hash::dir) ---

    fn sample_rows() -> [DirRow<&'static str>; 2] {
        [
            DirRow {
                name: "bar.txt",
                mode: DirMode::REGULAR,
                child: O256::blob("bar content"),
            },
            DirRow {
                name: "foo.txt",
                mode: DirMode::REGULAR,
                child: O256::blob("foo content"),
            },
        ]
    }

    #[test]
    fn empty_dir_hash() {
        let h: O256 = ().hash_dir::<&str>(&[]);
        // Empty dir should produce a valid non-zero hash.
        assert_ne!(h, O256::default());
    }

    #[test]
    fn determinism() {
        let rows = sample_rows();
        let h1 = ().hash_dir(&rows);
        let h2 = ().hash_dir(&rows);
        assert_eq!(h1, h2);
    }

    #[test]
    fn domain_separation_dir_vs_blob() {
        let rows = sample_rows();
        let dh = ().hash_dir(&rows);

        // Manually serialize the same way the impl does.
        let mut raw = Vec::new();
        for row in &rows {
            raw.extend_from_slice(row.mode.mode_ref().as_bytes());
            raw.extend_from_slice(row.name.as_bytes());
            raw.push(0);
            raw.extend_from_slice(row.child.as_bytes());
        }
        let blob_hash = O256::blob(&raw);
        assert_ne!(dh, blob_hash);
    }

    #[test]
    fn mode_matters() {
        let blob_row = [DirRow {
            name: "x",
            mode: DirMode::REGULAR,
            child: O256::blob("data"),
        }];
        let dir_row = [DirRow {
            name: "x",
            mode: DirMode::DIR,
            child: O256::blob("data"),
        }];
        assert_ne!(().hash_dir(&blob_row), ().hash_dir(&dir_row));
    }

    #[test]
    fn sort_order() {
        let mut rows = [
            DirRow {
                name: "z",
                mode: DirMode::REGULAR,
                child: O256::blob("z"),
            },
            DirRow {
                name: "a",
                mode: DirMode::REGULAR,
                child: O256::blob("a"),
            },
        ];
        rows.sort();
        assert_eq!(rows[0].name, "a");
        assert_eq!(rows[1].name, "z");
    }

    #[test]
    #[should_panic(expected = "sorted and unique")]
    #[cfg(debug_assertions)]
    fn panics_on_unsorted() {
        let rows = [
            DirRow {
                name: "z",
                mode: DirMode::REGULAR,
                child: O256::blob("z"),
            },
            DirRow {
                name: "a",
                mode: DirMode::REGULAR,
                child: O256::blob("a"),
            },
        ];
        ().hash_dir(&rows);
    }

    #[test]
    #[should_panic(expected = "sorted and unique")]
    #[cfg(debug_assertions)]
    fn panics_on_duplicate_name() {
        let rows = [
            DirRow {
                name: "x",
                mode: DirMode::REGULAR,
                child: O256::blob("a"),
            },
            DirRow {
                name: "x",
                mode: DirMode::DIR,
                child: O256::blob("b"),
            },
        ];
        ().hash_dir(&rows);
    }

    #[test]
    fn dir_hash_convenience() {
        let rows = sample_rows();
        assert_eq!(dir_hash(&rows), ().hash_dir(&rows));
    }

    #[test]
    fn builder_sorts() {
        let mut b = DirBuilder::new();
        b.entry("z", DirMode::REGULAR, O256::blob("z"))
            .entry("a", DirMode::REGULAR, O256::blob("a"))
            .entry("m", DirMode::REGULAR, O256::blob("m"));
        let entries = b.build();
        assert_eq!(entries[0].name, "a");
        assert_eq!(entries[1].name, "m");
        assert_eq!(entries[2].name, "z");
    }

    #[test]
    fn builder_dedup_last_wins() {
        let mut b = DirBuilder::new();
        b.entry("x", DirMode::REGULAR, O256::blob("first")).entry(
            "x",
            DirMode::DIR,
            O256::blob("second"),
        );
        assert_eq!(b.len(), 1);
        let entries = b.build();
        assert_eq!(entries[0].mode, DirMode::DIR);
        assert_eq!(entries[0].child, O256::blob("second"));
    }

    #[test]
    fn builder_empty() {
        let b = DirBuilder::new();
        assert!(b.is_empty());
        assert_eq!(b.len(), 0);
        assert_eq!(b.build(), vec![]);
        // Empty builder hash matches empty raw hash.
        assert_eq!(b.hash(), ().hash_dir::<&str>(&[]));
    }

    #[test]
    fn builder_hash_matches_raw() {
        let mut b = DirBuilder::new();
        b.entry("bar.txt", DirMode::REGULAR, O256::blob("bar content"))
            .entry("foo.txt", DirMode::REGULAR, O256::blob("foo content"));
        let rows = sample_rows();
        assert_eq!(b.hash(), ().hash_dir(&rows));
    }

    // --- Table codec tests ---

    #[test]
    fn dir_roundtrip() {
        let child_a = O256::blob("a_content");
        let child_b = O256::blob("b_content");
        let child_src = O256::blob("src_content");

        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"b.txt".to_vec(),
            mode: DirMode::REGULAR,
            child: child_b,
        });
        builder.push_row(DirRow {
            name: b"a.txt".to_vec(),
            mode: DirMode::REGULAR,
            child: child_a,
        });
        builder.push_row(DirRow {
            name: b"src".to_vec(),
            mode: DirMode::DIR,
            child: child_src,
        });

        let table = builder.build();

        assert_eq!(table.num_entries(), 3);
        // Mode is stored inline — no refs needed.
        assert_eq!(table.num_refs(), 0);
        // 3 child deps.
        assert_eq!(table.num_deps(), 3);

        // Dir::prepare sorts by name, so rows are now in sorted order.
        let row0 = table.row(0).unwrap();
        assert_eq!(row0.name, b"a.txt");
        assert_eq!(row0.mode, DirMode::REGULAR);
        assert_eq!(row0.child, child_a);

        let row1 = table.row(1).unwrap();
        assert_eq!(row1.name, b"b.txt");
        assert_eq!(row1.mode, DirMode::REGULAR);
        assert_eq!(row1.child, child_b);

        let row2 = table.row(2).unwrap();
        assert_eq!(row2.name, b"src");
        assert_eq!(row2.mode, DirMode::DIR);
        assert_eq!(row2.child, child_src);
    }

    #[test]
    fn auto_collects_deps() {
        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"x".to_vec(),
            mode: DirMode::REGULAR,
            child: O256::blob("x"),
        });
        let table = builder.build();
        assert_eq!(table.num_refs(), 0); // mode is inline
        assert_eq!(table.num_deps(), 1); // child dep
    }

    #[test]
    fn multiple_entries_no_refs() {
        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"a".to_vec(),
            mode: DirMode::REGULAR,
            child: O256::blob("a"),
        });
        builder.push_row(DirRow {
            name: b"b".to_vec(),
            mode: DirMode::REGULAR,
            child: O256::blob("b"),
        });

        let table = builder.build();
        assert_eq!(table.num_refs(), 0); // mode stored inline
        assert_eq!(table.num_deps(), 2);
    }

    #[test]
    fn mode_ref_deterministic() {
        // Same mode always produces the same mode_ref hash.
        assert_eq!(DirMode::REGULAR.mode_ref(), DirMode::REGULAR.mode_ref());
        assert_eq!(DirMode::DIR.mode_ref(), DirMode::DIR.mode_ref());
        // Different modes produce different hashes.
        assert_ne!(DirMode::REGULAR.mode_ref(), DirMode::DIR.mode_ref());
    }

    #[test]
    fn empty_dir_table() {
        let table = TableBuilder::new(Dir).build();
        assert_eq!(table.num_entries(), 0);
        assert_eq!(table.num_refs(), 0);
        assert_eq!(table.num_deps(), 0);
    }

    #[test]
    fn prepare_sorts_rows() {
        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"z".to_vec(),
            mode: DirMode::REGULAR,
            child: O256::blob("z"),
        });
        builder.push_row(DirRow {
            name: b"a".to_vec(),
            mode: DirMode::REGULAR,
            child: O256::blob("a"),
        });
        builder.push_row(DirRow {
            name: b"m".to_vec(),
            mode: DirMode::DIR,
            child: O256::blob("m"),
        });
        let table = builder.build();
        assert_eq!(table.row(0).unwrap().name, b"a");
        assert_eq!(table.row(1).unwrap().name, b"m");
        assert_eq!(table.row(2).unwrap().name, b"z");
    }

    #[test]
    #[should_panic(expected = "unique names")]
    fn prepare_panics_on_duplicate_names() {
        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"x".to_vec(),
            mode: DirMode::REGULAR,
            child: O256::blob("a"),
        });
        builder.push_row(DirRow {
            name: b"x".to_vec(),
            mode: DirMode::DIR,
            child: O256::blob("b"),
        });
        let _ = builder.build();
    }

    #[test]
    fn table_get_finds_entry() {
        let child_a = O256::blob("a");
        let child_m = O256::blob("m");
        let child_z = O256::blob("z");

        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"z.txt".to_vec(),
            mode: DirMode::REGULAR,
            child: child_z,
        });
        builder.push_row(DirRow {
            name: b"a.txt".to_vec(),
            mode: DirMode::REGULAR,
            child: child_a,
        });
        builder.push_row(DirRow {
            name: b"m.txt".to_vec(),
            mode: DirMode::DIR,
            child: child_m,
        });
        let table = builder.build();

        let found = table.get(b"m.txt").unwrap().unwrap();
        assert_eq!(found.name, b"m.txt");
        assert_eq!(found.mode, DirMode::DIR);
        assert_eq!(found.child, child_m);

        let found = table.get(b"a.txt").unwrap().unwrap();
        assert_eq!(found.child, child_a);

        let found = table.get(b"z.txt").unwrap().unwrap();
        assert_eq!(found.child, child_z);

        assert!(table.get(b"missing").unwrap().is_none());
    }

    // --- Git tree tests ---

    #[cfg(feature = "git")]
    mod git_tests {
        use super::*;

        #[test]
        fn git_sha1_manual_format() {
            let hash = O256::blob("content");
            let rows = [DirRow {
                name: b"file.txt".as_slice(),
                mode: DirMode::REGULAR,
                child: hash,
            }];

            let mut expected_buf = Vec::new();
            expected_buf.extend_from_slice(b"100644 file.txt\0");
            expected_buf.extend_from_slice(&hash.as_bytes()[..20]);

            let oid = covalence_hash::git::tree_sha1(&expected_buf);
            let mut expected = [0u8; 32];
            expected[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());

            assert_eq!(git_tree_sha1(&rows), O256::from_bytes(expected));
        }

        #[test]
        fn git_sha256_manual_format() {
            let hash = O256::blob("content");
            let rows = [DirRow {
                name: b"file.txt".as_slice(),
                mode: DirMode::REGULAR,
                child: hash,
            }];

            let mut expected_buf = Vec::new();
            expected_buf.extend_from_slice(b"100644 file.txt\0");
            expected_buf.extend_from_slice(hash.as_bytes());

            let oid = covalence_hash::git::tree_sha256(&expected_buf);
            let mut expected = [0u8; 32];
            expected.copy_from_slice(oid.as_bytes());

            assert_eq!(git_tree_sha256(&rows), O256::from_bytes(expected));
        }

        #[test]
        fn git_dir_mode_format() {
            let hash = O256::blob("sub");
            let rows = [DirRow {
                name: b"subdir".as_slice(),
                mode: DirMode::DIR,
                child: hash,
            }];

            let mut expected_buf = Vec::new();
            expected_buf.extend_from_slice(b"40000 subdir\0");
            expected_buf.extend_from_slice(&hash.as_bytes()[..20]);

            let oid = covalence_hash::git::tree_sha1(&expected_buf);
            let mut expected = [0u8; 32];
            expected[..oid.as_bytes().len()].copy_from_slice(oid.as_bytes());

            assert_eq!(git_tree_sha1(&rows), O256::from_bytes(expected));
        }

        #[test]
        fn git_tree_owned_names() {
            let hash = O256::blob("data");
            // Works with owned Vec<u8> names too.
            let rows = [DirRow {
                name: b"owned.txt".to_vec(),
                mode: DirMode::REGULAR,
                child: hash,
            }];
            let borrowed_rows = [DirRow {
                name: b"owned.txt".as_slice(),
                mode: DirMode::REGULAR,
                child: hash,
            }];
            assert_eq!(git_tree_sha1(&rows), git_tree_sha1(&borrowed_rows));
            assert_eq!(git_tree_sha256(&rows), git_tree_sha256(&borrowed_rows));
        }

        // --- Git tree parser tests ---

        /// Build a lookup map from truncated hash (first `hash_len` bytes) → full O256.
        fn hash_lookup(
            hashes: &[O256],
            hash_len: usize,
        ) -> std::collections::HashMap<Vec<u8>, O256> {
            hashes
                .iter()
                .map(|h| (h.as_bytes()[..hash_len].to_vec(), *h))
                .collect()
        }

        #[test]
        fn full_roundtrip_sha256() {
            // With hash_len=32, the full O256 is preserved byte-for-byte.
            let h1 = O256::blob("alpha_content");
            let h2 = O256::blob("beta_content");
            let h3 = O256::blob("gamma_content");
            let rows = [
                DirRow {
                    name: b"alpha".as_slice(),
                    mode: DirMode::REGULAR,
                    child: h1,
                },
                DirRow {
                    name: b"beta".as_slice(),
                    mode: DirMode::DIR,
                    child: h2,
                },
                DirRow {
                    name: b"gamma".as_slice(),
                    mode: DirMode::EXECUTABLE,
                    child: h3,
                },
            ];

            let tree_data = git_tree_bytes(&rows, 32);
            let dir_rows = git_tree_to_dir_rows(&tree_data, 32, |raw| {
                O256::from_bytes(raw.try_into().unwrap())
            })
            .unwrap();

            assert_eq!(dir_rows.len(), 3);
            for (orig, parsed) in rows.iter().zip(&dir_rows) {
                assert_eq!(parsed.name, orig.name);
                assert_eq!(parsed.mode, orig.mode);
                assert_eq!(
                    parsed.child, orig.child,
                    "child hash must round-trip exactly"
                );
            }
        }

        #[test]
        fn full_roundtrip_sha1_with_lookup() {
            // With hash_len=20, we need a lookup map to recover full O256.
            let h1 = O256::blob("file_a");
            let h2 = O256::blob("file_b");
            let h3 = O256::blob("subdir");
            let rows = [
                DirRow {
                    name: b"a.txt".as_slice(),
                    mode: DirMode::REGULAR,
                    child: h1,
                },
                DirRow {
                    name: b"b.txt".as_slice(),
                    mode: DirMode::EXECUTABLE,
                    child: h2,
                },
                DirRow {
                    name: b"src".as_slice(),
                    mode: DirMode::DIR,
                    child: h3,
                },
            ];

            let lookup = hash_lookup(&[h1, h2, h3], 20);
            let tree_data = git_tree_bytes(&rows, 20);
            let dir_rows = git_tree_to_dir_rows(&tree_data, 20, |raw| {
                *lookup.get(raw).expect("hash must be in lookup")
            })
            .unwrap();

            assert_eq!(dir_rows.len(), 3);
            for (orig, parsed) in rows.iter().zip(&dir_rows) {
                assert_eq!(parsed.name, orig.name);
                assert_eq!(parsed.mode, orig.mode);
                assert_eq!(
                    parsed.child, orig.child,
                    "child hash must round-trip via lookup"
                );
            }
        }

        #[test]
        fn roundtrip_all_modes() {
            // Every mode survives the round-trip.
            let h = O256::blob("x");
            let rows = [
                DirRow {
                    name: b"a".as_slice(),
                    mode: DirMode::REGULAR,
                    child: h,
                },
                DirRow {
                    name: b"b".as_slice(),
                    mode: DirMode::DIR,
                    child: h,
                },
                DirRow {
                    name: b"c".as_slice(),
                    mode: DirMode::EXECUTABLE,
                    child: h,
                },
                DirRow {
                    name: b"d".as_slice(),
                    mode: DirMode::SYMLINK,
                    child: h,
                },
                DirRow {
                    name: b"e".as_slice(),
                    mode: DirMode::SUBMODULE,
                    child: h,
                },
            ];

            let tree_data = git_tree_bytes(&rows, 32);
            let dir_rows = git_tree_to_dir_rows(&tree_data, 32, |raw| {
                O256::from_bytes(raw.try_into().unwrap())
            })
            .unwrap();

            assert_eq!(dir_rows.len(), 5);
            for (orig, parsed) in rows.iter().zip(&dir_rows) {
                assert_eq!(parsed.name, orig.name);
                assert_eq!(parsed.mode, orig.mode);
                assert_eq!(parsed.child, orig.child);
            }
        }

        #[test]
        fn parse_raw_entries() {
            // Verify parse_git_tree returns correct raw fields.
            let hash = O256::blob("content");
            let rows = [DirRow {
                name: b"file.txt".as_slice(),
                mode: DirMode::REGULAR,
                child: hash,
            }];
            let tree_data = git_tree_bytes(&rows, 20);
            let entries = parse_git_tree(&tree_data, 20).unwrap();
            assert_eq!(entries.len(), 1);
            assert_eq!(entries[0].mode, b"100644");
            assert_eq!(entries[0].name, b"file.txt");
            assert_eq!(entries[0].hash, &hash.as_bytes()[..20]);
        }

        #[test]
        fn parse_empty_tree() {
            let entries = parse_git_tree(&[], 20).unwrap();
            assert!(entries.is_empty());
        }

        #[test]
        fn parse_truncated_hash() {
            let hash = O256::blob("x");
            let rows = [DirRow {
                name: b"f".as_slice(),
                mode: DirMode::REGULAR,
                child: hash,
            }];
            let mut data = git_tree_bytes(&rows, 20);
            data.truncate(data.len() - 5);
            let err = parse_git_tree(&data, 20).unwrap_err();
            assert!(err.to_string().contains("truncated hash"));
        }

        #[test]
        fn parse_missing_null() {
            let data = b"100644 file";
            let err = parse_git_tree(data, 20).unwrap_err();
            assert!(err.to_string().contains("missing null"));
        }

        #[test]
        fn parse_missing_space() {
            let data = b"100644file\x00";
            let err = parse_git_tree(data, 20).unwrap_err();
            assert!(err.to_string().contains("missing space"));
        }

        #[test]
        fn roundtrip_preserves_git_hash() {
            // Verify that serializing → parsing → re-serializing gives the same bytes.
            let h1 = O256::blob("a");
            let h2 = O256::blob("b");
            let rows = [
                DirRow {
                    name: b"foo".as_slice(),
                    mode: DirMode::REGULAR,
                    child: h1,
                },
                DirRow {
                    name: b"sub".as_slice(),
                    mode: DirMode::DIR,
                    child: h2,
                },
            ];

            // Serialize once.
            let tree_data = git_tree_bytes(&rows, 20);
            let sha1_orig = git_tree_sha1(&rows);

            // Parse back and re-serialize.
            let lookup = hash_lookup(&[h1, h2], 20);
            let parsed =
                git_tree_to_dir_rows(&tree_data, 20, |raw| *lookup.get(raw).unwrap()).unwrap();
            let tree_data_2 = git_tree_bytes(&parsed, 20);

            assert_eq!(tree_data, tree_data_2, "re-serialized bytes must match");
            assert_eq!(sha1_orig, git_tree_sha1(&parsed), "git SHA-1 must match");
        }

        #[test]
        fn hash_determinism() {
            let h = O256::blob("content");
            let rows = [
                DirRow {
                    name: b"a.txt".as_slice(),
                    mode: DirMode::REGULAR,
                    child: h,
                },
                DirRow {
                    name: b"src".as_slice(),
                    mode: DirMode::DIR,
                    child: h,
                },
            ];
            assert_eq!(dir_hash(&rows), dir_hash(&rows));
            assert_eq!(git_tree_sha1(&rows), git_tree_sha1(&rows));
        }
    }
}
