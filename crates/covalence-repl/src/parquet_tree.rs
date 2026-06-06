//! Adapter between [`covalence_parquet::HiveSource`] and a [`SyncBackend`]
//! holding tree blobs in the [`covalence_object::Dir`] table format.
//!
//! Each [`HiveSource::list`] call walks the parent tree blob (caching its
//! hash → entry mapping), so subsequent [`HiveSource::read`] calls for leaf
//! files can resolve their hashes without re-parsing the parent tree.

use std::collections::HashMap;

use covalence_hash::O256;
use covalence_object::{Dir, DirMode, Table};
use covalence_parquet::{HiveEntry, HiveSource, ParquetError};
use covalence_shell::SyncBackend;

pub(crate) struct BackendHiveSource<'a> {
    backend: &'a dyn SyncBackend,
    /// Path → tree hash.
    dirs: HashMap<String, O256>,
    /// Path → file blob hash.
    files: HashMap<String, O256>,
}

impl<'a> BackendHiveSource<'a> {
    pub(crate) fn new(backend: &'a dyn SyncBackend, root: O256) -> Self {
        let mut dirs = HashMap::new();
        dirs.insert(String::new(), root);
        Self {
            backend,
            dirs,
            files: HashMap::new(),
        }
    }
}

fn err(msg: impl Into<String>) -> ParquetError {
    ParquetError::HiveScan(msg.into())
}

fn join(parent: &str, name: &str) -> String {
    if parent.is_empty() {
        name.to_string()
    } else {
        format!("{parent}/{name}")
    }
}

impl HiveSource for BackendHiveSource<'_> {
    fn list(&mut self, path: &str) -> Result<Vec<HiveEntry>, ParquetError> {
        let hash = *self
            .dirs
            .get(path)
            .ok_or_else(|| err(format!("no cached directory hash for {path:?}")))?;
        let bytes = self
            .backend
            .get_blob(&hash)
            .map_err(|e| err(e.to_string()))?
            .ok_or_else(|| err(format!("tree blob not found: {hash}")))?;
        let table = Table::parse(bytes, Dir).map_err(|e| err(format!("not a tree blob: {e}")))?;

        let n = table.num_entries();
        let mut entries = Vec::with_capacity(n);
        for i in 0..n {
            let row = table.row(i).map_err(|e| err(e.to_string()))?;
            let name = std::str::from_utf8(row.name)
                .map_err(|_| err(format!("non-UTF-8 entry name in tree {hash}")))?
                .to_string();
            let child_path = join(path, &name);
            let is_dir = row.mode == DirMode::DIR;
            if is_dir {
                self.dirs.insert(child_path, row.child);
            } else {
                self.files.insert(child_path, row.child);
            }
            entries.push(HiveEntry { name, is_dir });
        }
        Ok(entries)
    }

    fn read(&mut self, path: &str) -> Result<Vec<u8>, ParquetError> {
        let hash = *self
            .files
            .get(path)
            .ok_or_else(|| err(format!("no cached file hash for {path:?}")))?;
        self.backend
            .get_blob(&hash)
            .map_err(|e| err(e.to_string()))?
            .ok_or_else(|| err(format!("file blob not found: {hash} ({path})")))
    }
}
