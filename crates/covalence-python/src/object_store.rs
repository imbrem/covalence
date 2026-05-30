use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList};

use covalence_object::{
    Dir, DirMode, DirRow, Sha256Identity, Table, TableBuilder, git_tree_bytes_mapped,
    git_tree_to_dir_rows_mapped,
};
use covalence_store::{
    AnyObject, Blob, GitObjectType, GitPrefixStore, GitTaggedObjectStore, KeyedObjectStore, Object,
    ObjectKind, ObjectStore, StoreError, TaggedBlobStore, Tree,
};

use crate::backend::parse_hash;
use crate::hash::O256;
use crate::tagged_store::PyTaggedStore;

// ---------------------------------------------------------------------------
// Inner enum — git-tagged or keyed
// ---------------------------------------------------------------------------

enum Inner {
    GitTagged(GitTaggedObjectStore<TaggedBlobStore<covalence_hash::O256, GitObjectType>>),
    Keyed(KeyedObjectStore<TaggedBlobStore<covalence_hash::O256>>),
}

// ---------------------------------------------------------------------------
// PyObjectStore
// ---------------------------------------------------------------------------

/// Typed object store for blobs and trees.
///
/// Two modes:
/// - `git_tagged` — all objects use git-style `"{type} {len}\0"` headers.
///   Supports blob, tree, commit, and tag.
/// - `keyed` — blobs are untagged (BLAKE3), trees are tagged with
///   `O256::blob("tree")` (BLAKE3 keyed hash).  Only blob and tree.
#[pyclass(name = "ObjectStore")]
pub struct PyObjectStore {
    inner: Inner,
}

#[pymethods]
impl PyObjectStore {
    /// Create a git-tagged object store from an existing `TaggedStore`.
    #[staticmethod]
    fn git_tagged(store: &PyTaggedStore) -> Self {
        Self {
            inner: Inner::GitTagged(GitTaggedObjectStore::new(store.tagged_store())),
        }
    }

    /// Create an in-memory git-tagged object store.
    #[staticmethod]
    fn git_tagged_memory() -> Self {
        let tagged = TaggedBlobStore::new(GitPrefixStore::new(
            covalence_store::SharedMemoryStore::new(),
        ));
        Self {
            inner: Inner::GitTagged(GitTaggedObjectStore::new(tagged)),
        }
    }

    /// Create an in-memory keyed object store (covalence-native).
    #[staticmethod]
    fn keyed_memory() -> Self {
        let tagged = TaggedBlobStore::new(covalence_store::SharedMemoryStore::new());
        Self {
            inner: Inner::Keyed(KeyedObjectStore::new(tagged)),
        }
    }

    // -- Blob operations ------------------------------------------------------

    /// Hash and store a blob, returning its O256 key.
    fn insert_blob(&self, data: &[u8]) -> PyResult<O256> {
        let blob = Blob(data.to_vec());
        match &self.inner {
            Inner::GitTagged(s) => ObjectStore::insert(s, &blob),
            Inner::Keyed(s) => ObjectStore::insert(s, &blob),
        }
        .map(O256)
        .map_err(store_err)
    }

    /// Retrieve a blob by key. Returns bytes, None (not found), or raises
    /// on type mismatch.
    fn get_blob<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let h = parse_hash(key)?;
        let result: Result<Option<Blob>, StoreError> = match &self.inner {
            Inner::GitTagged(s) => ObjectStore::get(s, &h),
            Inner::Keyed(s) => ObjectStore::get(s, &h),
        };
        match result {
            Ok(Some(blob)) => Ok(Some(PyBytes::new(py, blob.data()))),
            Ok(None) => Ok(None),
            Err(e) => Err(store_err(e)),
        }
    }

    // -- Tree operations ------------------------------------------------------

    /// Hash and store a tree, returning its O256 key.
    fn insert_tree(&self, data: &[u8]) -> PyResult<O256> {
        let tree = Tree(data.to_vec());
        match &self.inner {
            Inner::GitTagged(s) => ObjectStore::insert(s, &tree),
            Inner::Keyed(s) => ObjectStore::insert(s, &tree),
        }
        .map(O256)
        .map_err(store_err)
    }

    /// Retrieve a tree by key. Returns bytes, None (not found), or raises
    /// on type mismatch.
    fn get_tree<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let h = parse_hash(key)?;
        let result: Result<Option<Tree>, StoreError> = match &self.inner {
            Inner::GitTagged(s) => ObjectStore::get(s, &h),
            Inner::Keyed(s) => ObjectStore::get(s, &h),
        };
        match result {
            Ok(Some(tree)) => Ok(Some(PyBytes::new(py, tree.data()))),
            Ok(None) => Ok(None),
            Err(e) => Err(store_err(e)),
        }
    }

    // -- Tree API operations --------------------------------------------------

    /// List entries of a stored tree. Returns list of dicts with
    /// `name` (bytes), `mode` (str), `hash` (O256).
    fn list_tree<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Vec<Bound<'py, PyDict>>> {
        let data = self.get_tree_data(key)?;
        let table = Table::parse(data, Dir)
            .map_err(|e| PyValueError::new_err(format!("parse error: {e}")))?;

        let mut entries = Vec::with_capacity(table.num_entries());
        for i in 0..table.num_entries() {
            let row = table
                .row(i)
                .map_err(|e| PyValueError::new_err(format!("row error: {e}")))?;
            let dict = PyDict::new(py);
            dict.set_item("name", PyBytes::new(py, row.name))?;
            dict.set_item("mode", row.mode.name())?;
            dict.set_item("hash", O256(row.child).into_pyobject(py)?)?;
            entries.push(dict);
        }
        Ok(entries)
    }

    /// Get a tree entry by path (e.g. "src/lib.rs"). Traverses nested trees.
    /// Returns dict with `name`, `mode`, `hash` or None if not found.
    fn get_path<'py>(
        &self,
        py: Python<'py>,
        root_key: &Bound<'py, PyAny>,
        path: &str,
    ) -> PyResult<Option<Bound<'py, PyDict>>> {
        let segments: Vec<&str> = path.split('/').filter(|s| !s.is_empty()).collect();
        if segments.is_empty() {
            return Err(PyValueError::new_err("empty path"));
        }

        let mut current_hash = parse_hash(root_key)?;
        for (i, seg) in segments.iter().enumerate() {
            let data = self.get_tree_data_raw(&current_hash)?;
            let table = Table::parse(data, Dir)
                .map_err(|e| PyValueError::new_err(format!("parse error: {e}")))?;

            let row = table
                .get(seg.as_bytes())
                .map_err(|e| PyValueError::new_err(format!("lookup error: {e}")))?;

            match row {
                Some(row) => {
                    if i + 1 < segments.len() {
                        if !row.mode.is_dir() {
                            return Err(PyValueError::new_err(format!("{seg} is not a directory")));
                        }
                        current_hash = row.child;
                    } else {
                        let dict = PyDict::new(py);
                        dict.set_item("name", PyBytes::new(py, row.name))?;
                        dict.set_item("mode", row.mode.name())?;
                        dict.set_item("hash", O256(row.child).into_pyobject(py)?)?;
                        return Ok(Some(dict));
                    }
                }
                None => return Ok(None),
            }
        }
        Ok(None)
    }

    /// Build a tree from a list of entry dicts and store it.
    /// Each dict must have `name` (str or bytes), `mode` (str), `hash` (O256 or hex).
    fn insert_tree_json(&self, entries: &Bound<'_, PyList>) -> PyResult<O256> {
        let mut builder = TableBuilder::new(Dir);
        for item in entries.iter() {
            let dict = item
                .cast::<PyDict>()
                .map_err(|_| PyValueError::new_err("each entry must be a dict"))?;
            let name: Vec<u8> = if let Ok(s) = dict
                .get_item("name")?
                .ok_or_else(|| PyValueError::new_err("missing 'name'"))?
                .extract::<String>()
            {
                s.into_bytes()
            } else {
                dict.get_item("name")?
                    .ok_or_else(|| PyValueError::new_err("missing 'name'"))?
                    .extract::<Vec<u8>>()?
            };
            let mode_str: String = dict
                .get_item("mode")?
                .ok_or_else(|| PyValueError::new_err("missing 'mode'"))?
                .extract()?;
            let mode = parse_dir_mode(&mode_str)?;
            let hash_obj = dict
                .get_item("hash")?
                .ok_or_else(|| PyValueError::new_err("missing 'hash'"))?;
            let child = parse_hash(&hash_obj)?;
            builder.push_row(DirRow { name, mode, child });
        }
        let table = builder.build();
        let tree = Tree(table.into_bytes());
        match &self.inner {
            Inner::GitTagged(s) => ObjectStore::insert(s, &tree),
            Inner::Keyed(s) => ObjectStore::insert(s, &tree),
        }
        .map(O256)
        .map_err(store_err)
    }

    /// Get tree as git tree format bytes (using O256 identity mapping).
    fn get_tree_git<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let data = self.get_tree_data(key)?;
        let table = Table::parse(data, Dir)
            .map_err(|e| PyValueError::new_err(format!("parse error: {e}")))?;

        let mut rows = Vec::with_capacity(table.num_entries());
        for i in 0..table.num_entries() {
            let row = table
                .row(i)
                .map_err(|e| PyValueError::new_err(format!("row error: {e}")))?;
            rows.push(DirRow {
                name: row.name.to_vec(),
                mode: row.mode,
                child: row.child,
            });
        }

        let git_bytes = git_tree_bytes_mapped(&rows, &Sha256Identity)
            .map_err(|e| PyValueError::new_err(format!("git error: {e}")))?;
        Ok(PyBytes::new(py, &git_bytes))
    }

    /// Parse git tree format bytes and store as a tree (using O256 identity mapping).
    fn insert_tree_git(&self, data: &[u8]) -> PyResult<O256> {
        let rows = git_tree_to_dir_rows_mapped(data, &Sha256Identity)
            .map_err(|e| PyValueError::new_err(format!("parse error: {e}")))?;

        let mut builder = TableBuilder::new(Dir);
        for row in rows {
            builder.push_row(row);
        }
        let table = builder.build();
        let tree = Tree(table.into_bytes());
        match &self.inner {
            Inner::GitTagged(s) => ObjectStore::insert(s, &tree),
            Inner::Keyed(s) => ObjectStore::insert(s, &tree),
        }
        .map(O256)
        .map_err(store_err)
    }

    // -- Dynamic-typed operations --------------------------------------------

    /// Store an object by kind string ("blob", "tree", etc.), returning its key.
    fn insert_any(&self, kind: &str, data: &[u8]) -> PyResult<O256> {
        let obj_kind = parse_kind(kind)?;
        let obj = AnyObject {
            kind: obj_kind,
            data: data.to_vec(),
        };
        match &self.inner {
            Inner::GitTagged(s) => s.insert_any(&obj),
            Inner::Keyed(s) => s.insert_any(&obj),
        }
        .map(O256)
        .map_err(store_err)
    }

    /// Retrieve an object by key, returning `(kind_str, data)` or None.
    fn get_any<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<(String, Bound<'py, PyBytes>)>> {
        let h = parse_hash(key)?;
        let result = match &self.inner {
            Inner::GitTagged(s) => s.get_any(&h),
            Inner::Keyed(s) => s.get_any(&h),
        };
        match result {
            Ok(Some(obj)) => {
                let kind_str = kind_to_str(obj.kind);
                Ok(Some((kind_str.to_owned(), PyBytes::new(py, &obj.data))))
            }
            Ok(None) => Ok(None),
            Err(e) => Err(store_err(e)),
        }
    }

    // -- Contains -------------------------------------------------------------

    /// Check whether a key exists (any type).
    fn contains(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        let h = parse_hash(key)?;
        Ok(match &self.inner {
            Inner::GitTagged(s) => ObjectStore::<_, Blob>::contains(s, &h),
            Inner::Keyed(s) => ObjectStore::<_, Blob>::contains(s, &h),
        })
    }

    fn __contains__(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        self.contains(key)
    }

    fn __repr__(&self) -> String {
        match &self.inner {
            Inner::GitTagged(_) => "ObjectStore(git_tagged)".to_string(),
            Inner::Keyed(_) => "ObjectStore(keyed)".to_string(),
        }
    }
}

// ---------------------------------------------------------------------------
// Internal helpers on PyObjectStore
// ---------------------------------------------------------------------------

impl PyObjectStore {
    /// Retrieve tree bytes by key (parsed from a Python O256/hex argument).
    fn get_tree_data(&self, key: &Bound<'_, PyAny>) -> PyResult<Vec<u8>> {
        let h = parse_hash(key)?;
        self.get_tree_data_raw(&h)
    }

    /// Retrieve tree bytes by raw O256 hash.
    fn get_tree_data_raw(&self, h: &covalence_hash::O256) -> PyResult<Vec<u8>> {
        let result: Result<Option<Tree>, StoreError> = match &self.inner {
            Inner::GitTagged(s) => ObjectStore::get(s, h),
            Inner::Keyed(s) => ObjectStore::get(s, h),
        };
        match result {
            Ok(Some(tree)) => Ok(tree.0),
            Ok(None) => Err(PyValueError::new_err("tree not found")),
            Err(e) => Err(store_err(e)),
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn store_err(e: StoreError) -> PyErr {
    PyRuntimeError::new_err(e.to_string())
}

fn parse_kind(s: &str) -> PyResult<ObjectKind> {
    match s {
        "blob" => Ok(ObjectKind::Blob),
        "tree" => Ok(ObjectKind::Tree),
        "commit" => Ok(ObjectKind::Commit),
        "tag" => Ok(ObjectKind::Tag),
        other => Err(PyRuntimeError::new_err(format!(
            "unknown object kind: {other:?}"
        ))),
    }
}

fn kind_to_str(kind: ObjectKind) -> &'static str {
    match kind {
        ObjectKind::Blob => "blob",
        ObjectKind::Tree => "tree",
        ObjectKind::Commit => "commit",
        ObjectKind::Tag => "tag",
    }
}

fn parse_dir_mode(s: &str) -> PyResult<DirMode> {
    match s {
        "blob" | "regular" => Ok(DirMode::REGULAR),
        "executable" => Ok(DirMode::EXECUTABLE),
        "symlink" => Ok(DirMode::SYMLINK),
        "dir" => Ok(DirMode::DIR),
        "submodule" => Ok(DirMode::SUBMODULE),
        _ => Err(PyValueError::new_err(format!("unknown mode: {s}"))),
    }
}
