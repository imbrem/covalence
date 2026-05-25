use std::collections::BTreeMap;

use covalence_hash::O256;

use crate::table::{
    FieldSpec, RowCodec, RowSchema, Table, TableError, min_bytes, read_le, write_le,
};

/// The mode of a directory entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
#[repr(u8)]
pub enum DirMode {
    Blob = 0,
    Dir = 1,
}

/// Well-known ref hash for a directory mode variant.
fn mode_ref(mode: DirMode) -> O256 {
    O256::blob([mode as u8])
}

/// Recover `DirMode` from its ref hash.
fn mode_from_ref(hash: &O256) -> Result<DirMode, TableError> {
    for mode in [DirMode::Blob, DirMode::Dir] {
        if mode_ref(mode) == *hash {
            return Ok(mode);
        }
    }
    Err(TableError::UnknownDirMode)
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
/// Each entry is serialized as `{mode_u8}{name}\0{hash_32bytes}`.
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
            hasher.update(&[row.mode as u8]);
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
/// b.entry("z.txt", DirMode::Blob, O256::blob("z"))
///  .entry("a.txt", DirMode::Blob, O256::blob("a"));
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

/// Directory table schema: `(name: Blob, mode: Ref, child: Dep)`.
///
/// - Each `DirMode` variant maps to a deterministic ref hash.
/// - Each child `O256` is registered as a dep.
/// - `collect()` auto-pushes both when rows are added.
pub struct Dir;

impl RowCodec for Dir {
    type Row = DirRow<Vec<u8>>;
    type RowRef<'a> = DirRow<&'a [u8]>;

    fn collect(&self, row: &DirRow<Vec<u8>>, refs: &mut Vec<O256>, deps: &mut Vec<O256>) {
        refs.push(mode_ref(row.mode));
        deps.push(row.child);
    }

    fn row_schema(&self, num_refs: usize, num_deps: usize) -> RowSchema {
        RowSchema::new(vec![
            FieldSpec::blob(),
            FieldSpec::ref_index(min_bytes(num_refs)),
            FieldSpec::dep_index(min_bytes(num_deps)),
        ])
    }

    fn encode(
        &self,
        row: &DirRow<Vec<u8>>,
        sorted_refs: &[O256],
        sorted_deps: &[O256],
        ref_w: u8,
        dep_w: u8,
    ) -> Vec<Vec<u8>> {
        let ref_idx = sorted_refs
            .binary_search(&mode_ref(row.mode))
            .expect("mode ref missing from sorted refs");
        let dep_idx = sorted_deps
            .binary_search(&row.child)
            .expect("child dep missing from sorted deps");

        let mut ref_bytes = Vec::new();
        write_le(ref_idx as u64, ref_w as usize, &mut ref_bytes);
        let mut dep_bytes = Vec::new();
        write_le(dep_idx as u64, dep_w as usize, &mut dep_bytes);

        vec![row.name.clone(), ref_bytes, dep_bytes]
    }

    fn decode<'a>(
        &self,
        fields: Vec<&'a [u8]>,
        refs: &[O256],
        deps: &[O256],
    ) -> Result<DirRow<&'a [u8]>, TableError> {
        if fields.len() != 3 {
            return Err(TableError::SchemaMismatch {
                expected: 3,
                got: fields.len(),
            });
        }

        let name = fields[0];
        let ref_idx = read_le(fields[1], fields[1].len()) as usize;
        let dep_idx = read_le(fields[2], fields[2].len()) as usize;

        let mode = mode_from_ref(&refs[ref_idx])?;
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
        let mode_str = match row.mode {
            DirMode::Blob => "100644",
            DirMode::Dir => "40000",
        };
        buf.extend_from_slice(mode_str.as_bytes());
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table::TableBuilder;

    // --- HashDir / DirBuilder tests (moved from covalence-hash::dir) ---

    fn sample_rows() -> [DirRow<&'static str>; 2] {
        [
            DirRow {
                name: "bar.txt",
                mode: DirMode::Blob,
                child: O256::blob("bar content"),
            },
            DirRow {
                name: "foo.txt",
                mode: DirMode::Blob,
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
            raw.push(row.mode as u8);
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
            mode: DirMode::Blob,
            child: O256::blob("data"),
        }];
        let dir_row = [DirRow {
            name: "x",
            mode: DirMode::Dir,
            child: O256::blob("data"),
        }];
        assert_ne!(().hash_dir(&blob_row), ().hash_dir(&dir_row));
    }

    #[test]
    fn sort_order() {
        let mut rows = [
            DirRow {
                name: "z",
                mode: DirMode::Blob,
                child: O256::blob("z"),
            },
            DirRow {
                name: "a",
                mode: DirMode::Blob,
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
                mode: DirMode::Blob,
                child: O256::blob("z"),
            },
            DirRow {
                name: "a",
                mode: DirMode::Blob,
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
                mode: DirMode::Blob,
                child: O256::blob("a"),
            },
            DirRow {
                name: "x",
                mode: DirMode::Dir,
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
        b.entry("z", DirMode::Blob, O256::blob("z"))
            .entry("a", DirMode::Blob, O256::blob("a"))
            .entry("m", DirMode::Blob, O256::blob("m"));
        let entries = b.build();
        assert_eq!(entries[0].name, "a");
        assert_eq!(entries[1].name, "m");
        assert_eq!(entries[2].name, "z");
    }

    #[test]
    fn builder_dedup_last_wins() {
        let mut b = DirBuilder::new();
        b.entry("x", DirMode::Blob, O256::blob("first")).entry(
            "x",
            DirMode::Dir,
            O256::blob("second"),
        );
        assert_eq!(b.len(), 1);
        let entries = b.build();
        assert_eq!(entries[0].mode, DirMode::Dir);
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
        b.entry("bar.txt", DirMode::Blob, O256::blob("bar content"))
            .entry("foo.txt", DirMode::Blob, O256::blob("foo content"));
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
            mode: DirMode::Blob,
            child: child_b,
        });
        builder.push_row(DirRow {
            name: b"a.txt".to_vec(),
            mode: DirMode::Blob,
            child: child_a,
        });
        builder.push_row(DirRow {
            name: b"src".to_vec(),
            mode: DirMode::Dir,
            child: child_src,
        });

        let table = builder.build();

        assert_eq!(table.num_entries(), 3);
        // 2 mode refs (Blob, Dir) — sorted and deduped.
        assert_eq!(table.num_refs(), 2);
        // 3 child deps.
        assert_eq!(table.num_deps(), 3);

        // Dir::prepare sorts by name, so rows are now in sorted order.
        let row0 = table.row(0).unwrap();
        assert_eq!(row0.name, b"a.txt");
        assert_eq!(row0.mode, DirMode::Blob);
        assert_eq!(row0.child, child_a);

        let row1 = table.row(1).unwrap();
        assert_eq!(row1.name, b"b.txt");
        assert_eq!(row1.mode, DirMode::Blob);
        assert_eq!(row1.child, child_b);

        let row2 = table.row(2).unwrap();
        assert_eq!(row2.name, b"src");
        assert_eq!(row2.mode, DirMode::Dir);
        assert_eq!(row2.child, child_src);
    }

    #[test]
    fn auto_collects_refs_and_deps() {
        let mut builder = TableBuilder::new(Dir);
        builder.push_row(DirRow {
            name: b"x".to_vec(),
            mode: DirMode::Blob,
            child: O256::blob("x"),
        });
        let table = builder.build();
        assert_eq!(table.num_refs(), 1); // Blob mode ref
        assert_eq!(table.num_deps(), 1); // child dep
    }

    #[test]
    fn dedup_same_mode() {
        let mut builder = TableBuilder::new(Dir);
        // Two Blob entries — should deduplicate the mode ref.
        builder.push_row(DirRow {
            name: b"a".to_vec(),
            mode: DirMode::Blob,
            child: O256::blob("a"),
        });
        builder.push_row(DirRow {
            name: b"b".to_vec(),
            mode: DirMode::Blob,
            child: O256::blob("b"),
        });

        let table = builder.build();
        assert_eq!(table.num_refs(), 1); // same Blob mode deduped
        assert_eq!(table.num_deps(), 2);
    }

    #[test]
    fn mode_ref_deterministic() {
        // Same mode always produces the same ref hash.
        assert_eq!(mode_ref(DirMode::Blob), mode_ref(DirMode::Blob));
        assert_eq!(mode_ref(DirMode::Dir), mode_ref(DirMode::Dir));
        // Different modes produce different hashes.
        assert_ne!(mode_ref(DirMode::Blob), mode_ref(DirMode::Dir));
    }

    #[test]
    fn mode_ref_roundtrip() {
        for mode in [DirMode::Blob, DirMode::Dir] {
            assert_eq!(mode_from_ref(&mode_ref(mode)).unwrap(), mode);
        }
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
            mode: DirMode::Blob,
            child: O256::blob("z"),
        });
        builder.push_row(DirRow {
            name: b"a".to_vec(),
            mode: DirMode::Blob,
            child: O256::blob("a"),
        });
        builder.push_row(DirRow {
            name: b"m".to_vec(),
            mode: DirMode::Dir,
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
            mode: DirMode::Blob,
            child: O256::blob("a"),
        });
        builder.push_row(DirRow {
            name: b"x".to_vec(),
            mode: DirMode::Dir,
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
            mode: DirMode::Blob,
            child: child_z,
        });
        builder.push_row(DirRow {
            name: b"a.txt".to_vec(),
            mode: DirMode::Blob,
            child: child_a,
        });
        builder.push_row(DirRow {
            name: b"m.txt".to_vec(),
            mode: DirMode::Dir,
            child: child_m,
        });
        let table = builder.build();

        let found = table.get(b"m.txt").unwrap().unwrap();
        assert_eq!(found.name, b"m.txt");
        assert_eq!(found.mode, DirMode::Dir);
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
                mode: DirMode::Blob,
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
                mode: DirMode::Blob,
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
                mode: DirMode::Dir,
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
                mode: DirMode::Blob,
                child: hash,
            }];
            let borrowed_rows = [DirRow {
                name: b"owned.txt".as_slice(),
                mode: DirMode::Blob,
                child: hash,
            }];
            assert_eq!(git_tree_sha1(&rows), git_tree_sha1(&borrowed_rows));
            assert_eq!(git_tree_sha256(&rows), git_tree_sha256(&borrowed_rows));
        }
    }
}
