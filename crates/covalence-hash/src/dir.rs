use std::collections::BTreeMap;

use crate::O256;

/// The mode of a directory entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
#[repr(u8)]
pub enum DirMode {
    Blob = 0,
    Dir = 1,
}

/// A single entry in a directory listing.
///
/// Sort a slice of `DirEntry` with `.sort()` before passing to [`HashDir::hash_dir`],
/// or use [`DirBuilder`] which handles sorting and deduplication automatically.
/// Entries sort by `(name, mode, hash)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DirEntry<'a> {
    pub name: &'a str,
    pub mode: DirMode,
    pub hash: O256,
}

/// Hash a sorted, unique directory listing into an [`O256`].
pub trait HashDir {
    fn hash_dir(&self, entries: &[DirEntry<'_>]) -> O256;
}

/// BLAKE3 keyed-hash implementation: domain-separated from blob hashes.
///
/// Each entry is serialized as `{mode_u8}{name}\0{hash_32bytes}`.
/// The concatenated entries are hashed with BLAKE3 keyed mode using
/// `key = O256::blob("tree")`, ensuring disjointness from plain BLAKE3 hashes.
impl HashDir for () {
    fn hash_dir(&self, entries: &[DirEntry<'_>]) -> O256 {
        debug_assert!(
            entries.windows(2).all(|w| w[0].name < w[1].name),
            "entries must be sorted and unique by name",
        );

        let key = O256::blob("tree");
        let mut hasher = blake3::Hasher::new_keyed(key.as_bytes());
        for entry in entries {
            hasher.update(&[entry.mode as u8]);
            hasher.update(entry.name.as_bytes());
            hasher.update(&[0]);
            hasher.update(entry.hash.as_bytes());
        }
        O256::from_bytes(*hasher.finalize().as_bytes())
    }
}

/// Collects directory entries, sorts by name, and deduplicates (last-wins).
///
/// Callers never need to worry about ordering or duplicate names:
///
/// ```
/// use covalence_hash::{DirBuilder, DirMode, O256};
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
    pub fn entry(&mut self, name: &'a str, mode: DirMode, hash: O256) -> &mut Self {
        self.entries.insert(name, (mode, hash));
        self
    }

    /// Build a sorted, deduplicated `Vec<DirEntry>`.
    pub fn build(&self) -> Vec<DirEntry<'a>> {
        self.iter().collect()
    }

    /// Iterate over entries in sorted order.
    pub fn iter(&self) -> impl Iterator<Item = DirEntry<'a>> + '_ {
        self.entries
            .iter()
            .map(|(&name, &(mode, hash))| DirEntry { name, mode, hash })
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

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_entries() -> [DirEntry<'static>; 2] {
        [
            DirEntry {
                name: "bar.txt",
                mode: DirMode::Blob,
                hash: O256::blob("bar content"),
            },
            DirEntry {
                name: "foo.txt",
                mode: DirMode::Blob,
                hash: O256::blob("foo content"),
            },
        ]
    }

    #[test]
    fn empty_dir() {
        let h = ().hash_dir(&[]);
        // Empty dir should produce a valid non-zero hash.
        assert_ne!(h, O256::default());
    }

    #[test]
    fn determinism() {
        let entries = sample_entries();
        let h1 = ().hash_dir(&entries);
        let h2 = ().hash_dir(&entries);
        assert_eq!(h1, h2);
    }

    #[test]
    fn domain_separation_dir_vs_blob() {
        // A dir hash must differ from hashing the same serialized bytes as a blob.
        let entries = sample_entries();
        let dir_hash = ().hash_dir(&entries);

        // Manually serialize the same way the impl does.
        let mut raw = Vec::new();
        for entry in &entries {
            raw.push(entry.mode as u8);
            raw.extend_from_slice(entry.name.as_bytes());
            raw.push(0);
            raw.extend_from_slice(entry.hash.as_bytes());
        }
        let blob_hash = O256::blob(&raw);
        assert_ne!(dir_hash, blob_hash);
    }

    #[test]
    fn mode_matters() {
        let blob_entry = [DirEntry {
            name: "x",
            mode: DirMode::Blob,
            hash: O256::blob("data"),
        }];
        let dir_entry = [DirEntry {
            name: "x",
            mode: DirMode::Dir,
            hash: O256::blob("data"),
        }];
        assert_ne!(().hash_dir(&blob_entry), ().hash_dir(&dir_entry));
    }

    #[test]
    fn sort_order() {
        let mut entries = [
            DirEntry {
                name: "z",
                mode: DirMode::Blob,
                hash: O256::blob("z"),
            },
            DirEntry {
                name: "a",
                mode: DirMode::Blob,
                hash: O256::blob("a"),
            },
        ];
        entries.sort();
        assert_eq!(entries[0].name, "a");
        assert_eq!(entries[1].name, "z");
    }

    #[test]
    #[should_panic(expected = "sorted and unique")]
    #[cfg(debug_assertions)]
    fn panics_on_unsorted() {
        let entries = [
            DirEntry {
                name: "z",
                mode: DirMode::Blob,
                hash: O256::blob("z"),
            },
            DirEntry {
                name: "a",
                mode: DirMode::Blob,
                hash: O256::blob("a"),
            },
        ];
        ().hash_dir(&entries);
    }

    #[test]
    #[should_panic(expected = "sorted and unique")]
    #[cfg(debug_assertions)]
    fn panics_on_duplicate_name() {
        let entries = [
            DirEntry {
                name: "x",
                mode: DirMode::Blob,
                hash: O256::blob("a"),
            },
            DirEntry {
                name: "x",
                mode: DirMode::Dir,
                hash: O256::blob("b"),
            },
        ];
        ().hash_dir(&entries);
    }

    #[test]
    fn convenience_method() {
        let entries = sample_entries();
        assert_eq!(O256::dir(&entries), ().hash_dir(&entries));
    }

    // --- DirBuilder tests ---

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
        assert_eq!(entries[0].hash, O256::blob("second"));
    }

    #[test]
    fn builder_empty() {
        let b = DirBuilder::new();
        assert!(b.is_empty());
        assert_eq!(b.len(), 0);
        assert_eq!(b.build(), vec![]);
        // Empty builder hash matches empty raw hash.
        assert_eq!(b.hash(), ().hash_dir(&[]));
    }

    #[test]
    fn builder_hash_matches_raw() {
        let mut b = DirBuilder::new();
        b.entry("bar.txt", DirMode::Blob, O256::blob("bar content"))
            .entry("foo.txt", DirMode::Blob, O256::blob("foo content"));
        let entries = sample_entries();
        assert_eq!(b.hash(), ().hash_dir(&entries));
    }
}
