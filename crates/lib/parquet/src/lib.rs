//! Wrapper around the Apache Parquet Rust implementation.
//!
//! Re-exports [`parquet`] for callers; adds [`parse_file`] which returns a
//! [`ParquetInfo`] summary, plus helpers for treating a directory as
//! *hive-partitioned* Parquet (`key=value/` path components, leaf `.parquet`
//! files).
//!
//! The hive scanner is decoupled from any storage backend: callers provide
//! the directory listing and a closure that loads bytes by name. This keeps
//! the crate usable from the REPL (where blobs live in a [`SyncBackend`])
//! and from any future file-system or remote backend.
//!
//! [`SyncBackend`]: covalence_shell::SyncBackend

use std::collections::BTreeSet;
use std::fmt;

pub use parquet;

use bytes::Bytes;
use parquet::errors::ParquetError as RawParquetError;
use parquet::file::reader::{FileReader, SerializedFileReader};

/// Errors from Parquet parsing.
#[derive(Debug, thiserror::Error)]
pub enum ParquetError {
    #[error("parquet error: {0}")]
    Parquet(#[from] RawParquetError),
    #[error("hive scan: {0}")]
    HiveScan(String),
}

/// One column entry in a Parquet schema summary.
#[derive(Debug, Clone)]
pub struct ColumnInfo {
    pub name: String,
    pub physical_type: String,
    pub logical_type: Option<String>,
}

/// Summary statistics for a Parquet payload (single file or merged hive scan).
#[derive(Debug, Clone, Default)]
pub struct ParquetInfo {
    /// Number of files contributing to this summary (1 for a single file).
    pub num_files: usize,
    /// Total logical rows across all files.
    pub num_rows: i64,
    /// Total row groups across all files.
    pub num_row_groups: usize,
    /// Sum of compressed sizes (bytes).
    pub total_compressed_size: i64,
    /// Sum of uncompressed sizes (bytes).
    pub total_uncompressed_size: i64,
    /// Columns from the first file's schema (hive scans assume a shared schema).
    pub columns: Vec<ColumnInfo>,
    /// Partition keys discovered when scanning a hive layout (e.g. `["year", "month"]`).
    pub partition_keys: Vec<String>,
}

impl fmt::Display for ParquetInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "parquet: {} file(s), {} row group(s), {} rows",
            self.num_files, self.num_row_groups, self.num_rows
        )?;
        writeln!(
            f,
            "  size: {} compressed / {} uncompressed bytes",
            self.total_compressed_size, self.total_uncompressed_size
        )?;
        if !self.partition_keys.is_empty() {
            writeln!(f, "  partitions: {}", self.partition_keys.join(", "))?;
        }
        writeln!(f, "  columns ({}):", self.columns.len())?;
        for col in &self.columns {
            match &col.logical_type {
                Some(lt) => writeln!(f, "    {}: {} ({})", col.name, col.physical_type, lt)?,
                None => writeln!(f, "    {}: {}", col.name, col.physical_type)?,
            }
        }
        Ok(())
    }
}

/// Parse a single Parquet file blob.
pub fn parse_file(bytes: &[u8]) -> Result<ParquetInfo, ParquetError> {
    let reader = SerializedFileReader::new(Bytes::copy_from_slice(bytes))?;
    let metadata = reader.metadata();
    let file_meta = metadata.file_metadata();
    let schema = file_meta.schema_descr();

    let columns = (0..schema.num_columns())
        .map(|i| {
            let col = schema.column(i);
            ColumnInfo {
                name: col.name().to_string(),
                physical_type: format!("{:?}", col.physical_type()),
                logical_type: col.logical_type_ref().map(|lt| format!("{lt:?}")),
            }
        })
        .collect();

    let num_row_groups = metadata.num_row_groups();
    let (total_compressed_size, total_uncompressed_size) =
        (0..num_row_groups).fold((0i64, 0i64), |(c, u), i| {
            let rg = metadata.row_group(i);
            (c + rg.compressed_size(), u + rg.total_byte_size())
        });

    Ok(ParquetInfo {
        num_files: 1,
        num_rows: file_meta.num_rows(),
        num_row_groups,
        total_compressed_size,
        total_uncompressed_size,
        columns,
        partition_keys: Vec::new(),
    })
}

/// One entry in a directory listing supplied to [`scan_hive`].
///
/// Naming follows the [`covalence_object`] vocabulary: `name` is the entry
/// label and `is_dir` distinguishes children that should be recursed into
/// from leaf blobs.
///
/// [`covalence_object`]: https://docs.rs/covalence-object
#[derive(Debug, Clone)]
pub struct HiveEntry {
    pub name: String,
    pub is_dir: bool,
}

/// Callbacks the hive scanner uses to walk a tree without depending on any
/// particular storage backend.
pub trait HiveSource {
    /// List the children of the directory at the given path. Paths use `/`
    /// as a separator; the root is `""`.
    fn list(&mut self, path: &str) -> Result<Vec<HiveEntry>, ParquetError>;

    /// Load the bytes of a leaf entry at the given path.
    fn read(&mut self, path: &str) -> Result<Vec<u8>, ParquetError>;
}

/// Scan a hive-partitioned directory rooted at `""`, accumulating stats over
/// every `*.parquet` leaf reachable through `key=value/` partition directories
/// (or any nested directory, which is treated transparently).
///
/// Partition keys are collected in encounter order; the schema is taken from
/// the first file and assumed shared.
pub fn scan_hive(source: &mut impl HiveSource) -> Result<ParquetInfo, ParquetError> {
    let mut acc = ParquetInfo::default();
    let mut partition_keys: Vec<String> = Vec::new();
    let mut seen_keys: BTreeSet<String> = BTreeSet::new();
    walk(source, "", &mut acc, &mut partition_keys, &mut seen_keys)?;
    acc.partition_keys = partition_keys;
    if acc.num_files == 0 {
        return Err(ParquetError::HiveScan(
            "no .parquet files found in tree".into(),
        ));
    }
    Ok(acc)
}

fn walk(
    source: &mut impl HiveSource,
    path: &str,
    acc: &mut ParquetInfo,
    partition_keys: &mut Vec<String>,
    seen_keys: &mut BTreeSet<String>,
) -> Result<(), ParquetError> {
    let entries = source.list(path)?;
    for entry in entries {
        let child_path = if path.is_empty() {
            entry.name.clone()
        } else {
            format!("{path}/{}", entry.name)
        };

        if entry.is_dir {
            if let Some(key) = entry.name.split_once('=').map(|(k, _)| k.to_string())
                && seen_keys.insert(key.clone())
            {
                partition_keys.push(key);
            }
            walk(source, &child_path, acc, partition_keys, seen_keys)?;
        } else if entry.name.ends_with(".parquet") {
            let bytes = source.read(&child_path)?;
            let info = parse_file(&bytes)?;
            merge_into(acc, info);
        }
    }
    Ok(())
}

fn merge_into(acc: &mut ParquetInfo, info: ParquetInfo) {
    if acc.num_files == 0 {
        acc.columns = info.columns;
    }
    acc.num_files += info.num_files;
    acc.num_rows += info.num_rows;
    acc.num_row_groups += info.num_row_groups;
    acc.total_compressed_size += info.total_compressed_size;
    acc.total_uncompressed_size += info.total_uncompressed_size;
}

#[cfg(test)]
mod tests {
    use super::*;
    use parquet::arrow::ArrowWriter;
    use parquet::file::properties::WriterProperties;
    use std::collections::HashMap;
    use std::sync::Arc;

    use covalence_arrow::arrow::array::Int32Array;
    use covalence_arrow::arrow::datatypes::{DataType, Field, Schema};
    use covalence_arrow::arrow::record_batch::RecordBatch;

    fn sample_parquet(rows: &[i32]) -> Vec<u8> {
        let schema = Arc::new(Schema::new(vec![Field::new("v", DataType::Int32, false)]));
        let batch = RecordBatch::try_new(
            schema.clone(),
            vec![Arc::new(Int32Array::from(rows.to_vec()))],
        )
        .unwrap();
        let mut buf = Vec::new();
        {
            let mut w =
                ArrowWriter::try_new(&mut buf, schema, Some(WriterProperties::new())).unwrap();
            w.write(&batch).unwrap();
            w.close().unwrap();
        }
        buf
    }

    #[test]
    fn parses_single_file() {
        let bytes = sample_parquet(&[1, 2, 3, 4]);
        let info = parse_file(&bytes).unwrap();
        assert_eq!(info.num_files, 1);
        assert_eq!(info.num_rows, 4);
        assert!(info.num_row_groups >= 1);
        assert_eq!(info.columns.len(), 1);
        assert_eq!(info.columns[0].name, "v");
    }

    /// In-memory `HiveSource` backed by a `HashMap<path, bytes>` plus dir markers.
    struct MapSource {
        // dirs[path] = list of children
        dirs: HashMap<String, Vec<HiveEntry>>,
        files: HashMap<String, Vec<u8>>,
    }

    impl HiveSource for MapSource {
        fn list(&mut self, path: &str) -> Result<Vec<HiveEntry>, ParquetError> {
            self.dirs
                .get(path)
                .cloned()
                .ok_or_else(|| ParquetError::HiveScan(format!("no dir: {path}")))
        }
        fn read(&mut self, path: &str) -> Result<Vec<u8>, ParquetError> {
            self.files
                .get(path)
                .cloned()
                .ok_or_else(|| ParquetError::HiveScan(format!("no file: {path}")))
        }
    }

    #[test]
    fn scans_hive_layout() {
        // Tree:
        //   year=2024/
        //     month=01/data.parquet (rows = [1,2])
        //     month=02/data.parquet (rows = [3,4,5])
        let mut dirs: HashMap<String, Vec<HiveEntry>> = HashMap::new();
        dirs.insert(
            "".into(),
            vec![HiveEntry {
                name: "year=2024".into(),
                is_dir: true,
            }],
        );
        dirs.insert(
            "year=2024".into(),
            vec![
                HiveEntry {
                    name: "month=01".into(),
                    is_dir: true,
                },
                HiveEntry {
                    name: "month=02".into(),
                    is_dir: true,
                },
            ],
        );
        dirs.insert(
            "year=2024/month=01".into(),
            vec![HiveEntry {
                name: "data.parquet".into(),
                is_dir: false,
            }],
        );
        dirs.insert(
            "year=2024/month=02".into(),
            vec![HiveEntry {
                name: "data.parquet".into(),
                is_dir: false,
            }],
        );

        let mut files: HashMap<String, Vec<u8>> = HashMap::new();
        files.insert(
            "year=2024/month=01/data.parquet".into(),
            sample_parquet(&[1, 2]),
        );
        files.insert(
            "year=2024/month=02/data.parquet".into(),
            sample_parquet(&[3, 4, 5]),
        );

        let mut src = MapSource { dirs, files };
        let info = scan_hive(&mut src).unwrap();
        assert_eq!(info.num_files, 2);
        assert_eq!(info.num_rows, 5);
        assert_eq!(info.partition_keys, vec!["year", "month"]);
    }

    #[test]
    fn errors_on_empty_tree() {
        let mut dirs = HashMap::new();
        dirs.insert("".into(), vec![]);
        let mut src = MapSource {
            dirs,
            files: HashMap::new(),
        };
        let err = scan_hive(&mut src).unwrap_err();
        assert!(matches!(err, ParquetError::HiveScan(_)));
    }
}
