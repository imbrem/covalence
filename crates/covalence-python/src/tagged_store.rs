use pyo3::exceptions::{PyRuntimeError, PyTypeError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_store::{
    ContentStore, GitObjectType, GitPrefixStore, StoreError, TaggedBlobStore, TaggedStore,
};

use crate::backend::parse_hash;
use crate::hash::O256;
use crate::store::Store;

// ---------------------------------------------------------------------------
// PyTaggedStoreProtocol — bridges a Python object to TaggedStore<O256, GitObjectType>
// ---------------------------------------------------------------------------

/// Wraps a Python object implementing the tagged store protocol as a Rust TaggedStore.
///
/// Required methods: get, put, get_repr, get_tag, insert_tagged
/// Optional methods: insert, contains, __len__, get_repr_with, get_tag_with
struct PyTaggedStoreProtocol {
    obj: Py<PyAny>,
    has_insert: bool,
    has_contains: bool,
    has_len: bool,
}

impl ContentStore<covalence_hash::O256> for PyTaggedStoreProtocol {
    fn get(&self, key: &covalence_hash::O256) -> Option<Vec<u8>> {
        Python::attach(|py| {
            let py_key = O256(*key).into_pyobject(py).ok()?;
            let result = self.obj.call_method1(py, "get", (py_key,)).ok()?;
            if result.is_none(py) {
                return None;
            }
            result.extract::<Vec<u8>>(py).ok()
        })
    }

    fn put(&self, key: covalence_hash::O256, data: &[u8]) -> Result<(), StoreError> {
        Python::attach(|py| {
            let py_key = O256(key)
                .into_pyobject(py)
                .map_err(|e| StoreError::Io(e.to_string()))?;
            let py_data = PyBytes::new(py, data);
            self.obj
                .call_method1(py, "put", (py_key, py_data))
                .map_err(|e| StoreError::Io(e.to_string()))?;
            Ok(())
        })
    }

    fn insert(&self, data: &[u8]) -> Result<covalence_hash::O256, StoreError> {
        if self.has_insert {
            return Python::attach(|py| {
                let py_data = PyBytes::new(py, data);
                let result = self
                    .obj
                    .call_method1(py, "insert", (py_data,))
                    .map_err(|e| StoreError::Io(e.to_string()))?;
                let bound = result.into_bound(py);
                let hash = bound
                    .cast::<O256>()
                    .map_err(|e| StoreError::Io(e.to_string()))?
                    .borrow();
                Ok(hash.0)
            });
        }
        let hash = covalence_hash::O256::blob(data);
        self.put(hash, data)?;
        Ok(hash)
    }

    fn contains(&self, key: &covalence_hash::O256) -> bool {
        if self.has_contains {
            return Python::attach(|py| {
                let py_key = match O256(*key).into_pyobject(py) {
                    Ok(k) => k,
                    Err(_) => return false,
                };
                self.obj
                    .call_method1(py, "contains", (py_key,))
                    .and_then(|r| r.extract::<bool>(py))
                    .unwrap_or(false)
            });
        }
        self.get(key).is_some()
    }

    fn len(&self) -> Option<usize> {
        if self.has_len {
            return Python::attach(|py| {
                self.obj
                    .call_method0(py, "__len__")
                    .and_then(|r| r.extract::<usize>(py))
                    .ok()
            });
        }
        None
    }
}

impl TaggedStore<covalence_hash::O256, GitObjectType> for PyTaggedStoreProtocol {
    fn get_repr(&self, key: &covalence_hash::O256) -> Option<Vec<u8>> {
        Python::attach(|py| {
            let py_key = O256(*key).into_pyobject(py).ok()?;
            let result = self.obj.call_method1(py, "get_repr", (py_key,)).ok()?;
            if result.is_none(py) {
                return None;
            }
            result.extract::<Vec<u8>>(py).ok()
        })
    }

    fn get_tag(&self, key: &covalence_hash::O256) -> Option<GitObjectType> {
        Python::attach(|py| {
            let py_key = O256(*key).into_pyobject(py).ok()?;
            let result = self.obj.call_method1(py, "get_tag", (py_key,)).ok()?;
            if result.is_none(py) {
                return None;
            }
            let tag_str: String = result.extract(py).ok()?;
            Some(GitObjectType::new(tag_str))
        })
    }

    fn insert_tagged(
        &self,
        tag: GitObjectType,
        data: &[u8],
    ) -> Result<covalence_hash::O256, StoreError> {
        Python::attach(|py| {
            let py_data = PyBytes::new(py, data);
            let tag_str = tag.as_str();
            let result = self
                .obj
                .call_method1(py, "insert_tagged", (tag_str, py_data))
                .map_err(|e| StoreError::Io(e.to_string()))?;
            let bound = result.into_bound(py);
            let hash = bound
                .cast::<O256>()
                .map_err(|e| StoreError::Io(e.to_string()))?
                .borrow();
            Ok(hash.0)
        })
    }

    fn get_repr_with(&self, tag: &GitObjectType, key: &covalence_hash::O256) -> Option<Vec<u8>> {
        // Check tag matches, then return repr
        let actual = self.get_tag(key)?;
        if actual.as_str() == tag.as_str() {
            self.get_repr(key)
        } else {
            None
        }
    }

    fn get_tag_with(
        &self,
        tag: &GitObjectType,
        key: &covalence_hash::O256,
    ) -> Option<GitObjectType> {
        let actual = self.get_tag(key)?;
        if actual.as_str() == tag.as_str() {
            Some(actual)
        } else {
            None
        }
    }
}

/// Tagged content-addressed store with git-style object type tags.
///
/// Wraps any `Store` in a `GitPrefixStore`, prepending a
/// `"{type} {len}\0"` header to every stored value.
///
/// - `insert` / `get` / `put` operate as blobs (like `Store`).
/// - `insert_tagged` / `get_repr` / `get_tag` are type-aware.
/// - `get` returns `None` for non-blob objects; `get_repr` returns data
///   for any type.
#[pyclass(name = "TaggedStore")]
pub struct PyTaggedStore {
    inner: TaggedBlobStore<covalence_hash::O256, GitObjectType>,
}

#[pymethods]
impl PyTaggedStore {
    /// Wrap a Python object implementing the tagged store protocol.
    ///
    /// Required methods: get, put, get_repr, get_tag, insert_tagged.
    /// Optional: insert, contains, __len__.
    #[new]
    fn new(obj: &Bound<'_, PyAny>) -> PyResult<Self> {
        for method in &["get", "put", "get_repr", "get_tag", "insert_tagged"] {
            if !obj.hasattr(*method)? {
                return Err(PyTypeError::new_err(format!(
                    "tagged store object must have a '{method}' method"
                )));
            }
        }
        let has_insert = obj.hasattr("insert")?;
        let has_contains = obj.hasattr("contains")?;
        let has_len = obj.hasattr("__len__")?;
        let protocol = PyTaggedStoreProtocol {
            obj: obj.clone().unbind(),
            has_insert,
            has_contains,
            has_len,
        };
        Ok(Self {
            inner: TaggedBlobStore::new(protocol),
        })
    }

    /// Wrap an existing `Store` in a git-prefix tagged store.
    #[staticmethod]
    fn git_prefix(store: &Store) -> Self {
        Self {
            inner: TaggedBlobStore::new(GitPrefixStore::new(store.blob_store())),
        }
    }

    /// Create an in-memory git-prefix tagged store.
    #[staticmethod]
    fn memory() -> Self {
        Self {
            inner: TaggedBlobStore::new(GitPrefixStore::new(
                covalence_store::SharedMemoryStore::new(),
            )),
        }
    }

    // -- ContentStore (blob-only) ---------------------------------------------

    /// Hash and store data as a blob, returning its O256 key.
    fn insert(&self, data: &[u8]) -> PyResult<O256> {
        ContentStore::insert(&self.inner, data)
            .map(O256)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Retrieve blob data by key. Returns `None` for non-blob objects.
    fn get<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let h = parse_hash(key)?;
        Ok(ContentStore::get(&self.inner, &h).map(|data| PyBytes::new(py, &data)))
    }

    /// Store data as a blob under the given key.
    fn put(&self, key: &Bound<'_, PyAny>, data: &[u8]) -> PyResult<()> {
        let h = parse_hash(key)?;
        ContentStore::put(&self.inner, h, data).map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Check whether a key exists (any object type).
    fn contains(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        let h = parse_hash(key)?;
        Ok(ContentStore::contains(&self.inner, &h))
    }

    fn __contains__(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        self.contains(key)
    }

    fn __len__(&self) -> PyResult<usize> {
        self.inner
            .len()
            .ok_or_else(|| PyRuntimeError::new_err("store does not support len"))
    }

    // -- TaggedStore (type-aware) ----------------------------------------------

    /// Store data with a type tag (e.g. "blob", "tree", "commit", "tag"),
    /// returning its O256 key.
    fn insert_tagged(&self, kind: &str, data: &[u8]) -> PyResult<O256> {
        self.inner
            .insert_tagged(GitObjectType::new(kind), data)
            .map(O256)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Get data by key, stripping the type header. Works for any object type.
    fn get_repr<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let h = parse_hash(key)?;
        Ok(self.inner.get_repr(&h).map(|data| PyBytes::new(py, &data)))
    }

    /// Get the type tag for a key. Returns a string or `None`.
    fn get_tag(&self, key: &Bound<'_, PyAny>) -> PyResult<Option<String>> {
        let h = parse_hash(key)?;
        Ok(self.inner.get_tag(&h).map(|t| t.as_str().to_owned()))
    }

    /// Get data by key, but only if the stored type matches `kind`.
    fn get_repr_with<'py>(
        &self,
        py: Python<'py>,
        kind: &str,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let h = parse_hash(key)?;
        let tag = GitObjectType::new(kind);
        Ok(self
            .inner
            .get_repr_with(&tag, &h)
            .map(|data| PyBytes::new(py, &data)))
    }

    /// Get the type tag, but only if it matches `kind`.
    fn get_tag_with(&self, kind: &str, key: &Bound<'_, PyAny>) -> PyResult<Option<String>> {
        let h = parse_hash(key)?;
        let tag = GitObjectType::new(kind);
        Ok(self
            .inner
            .get_tag_with(&tag, &h)
            .map(|t| t.as_str().to_owned()))
    }

    fn __repr__(&self) -> String {
        match self.inner.len() {
            Some(n) => format!("TaggedStore({n} objects)"),
            None => "TaggedStore(?)".to_string(),
        }
    }
}

impl PyTaggedStore {
    pub(crate) fn tagged_store(&self) -> TaggedBlobStore<covalence_hash::O256, GitObjectType> {
        self.inner.clone()
    }
}
