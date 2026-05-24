use covalence_hash::DirMode;
use covalence_hash::O256;

use crate::table::{FieldSpec, RowSchema, TableError, min_bytes, read_le, write_le};

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

/// Owned directory row for building.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirRow {
    pub name: Vec<u8>,
    pub mode: DirMode,
    pub child: O256,
}

/// Borrowed directory row returned by the parser.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirRowRef<'a> {
    pub name: &'a [u8],
    pub mode: DirMode,
    pub child: O256,
}

/// Directory table schema: `(name: Blob, mode: Ref, child: Dep)`.
///
/// - Each `DirMode` variant maps to a deterministic ref hash.
/// - Each child `O256` is registered as a dep.
/// - `collect()` auto-pushes both when rows are added.
pub struct Dir;

impl RowSchema for Dir {
    type Row = DirRow;
    type RowRef<'a> = DirRowRef<'a>;

    fn collect(&self, row: &DirRow, refs: &mut Vec<O256>, deps: &mut Vec<O256>) {
        refs.push(mode_ref(row.mode));
        deps.push(row.child);
    }

    fn field_specs(&self, num_refs: usize, num_deps: usize) -> Vec<FieldSpec> {
        vec![
            FieldSpec::blob(),
            FieldSpec::ref_index(min_bytes(num_refs)),
            FieldSpec::dep_index(min_bytes(num_deps)),
        ]
    }

    fn encode(
        &self,
        row: &DirRow,
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
    ) -> Result<DirRowRef<'a>, TableError> {
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

        Ok(DirRowRef { name, mode, child })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table::{TableBuilder, TableParser};

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

        let blob = builder.build();
        let parser = TableParser::new(&blob, Dir).unwrap();

        assert_eq!(parser.num_entries(), 3);
        // 2 mode refs (Blob, Dir) — sorted and deduped.
        assert_eq!(parser.num_refs(), 2);
        // 3 child deps.
        assert_eq!(parser.num_deps(), 3);

        let row0 = parser.row(0).unwrap();
        assert_eq!(row0.name, b"b.txt");
        assert_eq!(row0.mode, DirMode::Blob);
        assert_eq!(row0.child, child_b);

        let row1 = parser.row(1).unwrap();
        assert_eq!(row1.name, b"a.txt");
        assert_eq!(row1.mode, DirMode::Blob);
        assert_eq!(row1.child, child_a);

        let row2 = parser.row(2).unwrap();
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
        // No manual push_ref/push_dep needed.
        let blob = builder.build();
        let parser = TableParser::new(&blob, Dir).unwrap();
        assert_eq!(parser.num_refs(), 1); // Blob mode ref
        assert_eq!(parser.num_deps(), 1); // child dep
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

        let blob = builder.build();
        let parser = TableParser::new(&blob, Dir).unwrap();
        assert_eq!(parser.num_refs(), 1); // same Blob mode deduped
        assert_eq!(parser.num_deps(), 2);
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
    fn empty_dir() {
        let builder = TableBuilder::new(Dir);
        let blob = builder.build();
        let parser = TableParser::new(&blob, Dir).unwrap();
        assert_eq!(parser.num_entries(), 0);
        assert_eq!(parser.num_refs(), 0);
        assert_eq!(parser.num_deps(), 0);
    }
}
