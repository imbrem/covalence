use pyo3::exceptions::{PyRuntimeError, PyTypeError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_store::{BlobStore, ContentStore, StoreError};

use crate::backend::parse_hash;
use crate::hash::O256;

// ---------------------------------------------------------------------------
// PyContentStore — bridges a Python object to ContentStore<covalence_hash::O256>
// ---------------------------------------------------------------------------

/// Wraps a Python object implementing the store protocol (get + put)
/// as a Rust `ContentStore<O256>`.
struct PyContentStore {
    obj: Py<PyAny>,
    has_insert: bool,
    has_contains: bool,
    has_len: bool,
}

impl ContentStore<covalence_hash::O256> for PyContentStore {
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
        // Default: hash + put
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

// ---------------------------------------------------------------------------
// Store pyclass
// ---------------------------------------------------------------------------

/// Content-addressed blob store.
///
/// Construct from a Python store object, or use the `memory()` / `sqlite()`
/// static methods for Rust-backed stores.
#[pyclass]
pub struct Store {
    inner: BlobStore<covalence_hash::O256>,
}

#[pymethods]
impl Store {
    /// Wrap a Python object implementing the store protocol (get + put required).
    #[new]
    fn new(obj: &Bound<'_, PyAny>) -> PyResult<Self> {
        if !obj.hasattr("get")? {
            return Err(PyTypeError::new_err(
                "store object must have a 'get' method",
            ));
        }
        if !obj.hasattr("put")? {
            return Err(PyTypeError::new_err(
                "store object must have a 'put' method",
            ));
        }
        let has_insert = obj.hasattr("insert")?;
        let has_contains = obj.hasattr("contains")?;
        let has_len = obj.hasattr("__len__")?;
        let py_store = PyContentStore {
            obj: obj.clone().unbind(),
            has_insert,
            has_contains,
            has_len,
        };
        Ok(Self {
            inner: BlobStore::new(py_store),
        })
    }

    /// Create an in-memory store backed by Rust.
    #[staticmethod]
    fn memory() -> Self {
        Self {
            inner: BlobStore::new(covalence_store::SharedMemoryStore::new()),
        }
    }

    /// Create a SQLite-backed store at the given path.
    #[staticmethod]
    fn sqlite(path: &str) -> PyResult<Self> {
        let store = covalence_store::SqliteStore::open(path)
            .map_err(|e| PyRuntimeError::new_err(format!("sqlite open: {e}")))?;
        Ok(Self {
            inner: BlobStore::new(store),
        })
    }

    /// Hash and store data, returning its O256 key.
    fn insert(&self, data: &[u8]) -> PyResult<O256> {
        self.inner
            .insert(data)
            .map(O256)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Retrieve data by key. Returns bytes or None.
    fn get<'py>(
        &self,
        py: Python<'py>,
        key: &Bound<'py, PyAny>,
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        let h = parse_hash(key)?;
        Ok(self.inner.get(&h).map(|data| PyBytes::new(py, &data)))
    }

    /// Store data under the given key.
    fn put(&self, key: &Bound<'_, PyAny>, data: &[u8]) -> PyResult<()> {
        let h = parse_hash(key)?;
        self.inner
            .put(h, data)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Check whether a key exists in the store.
    fn contains(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        let h = parse_hash(key)?;
        Ok(self.inner.contains(&h))
    }

    fn __contains__(&self, key: &Bound<'_, PyAny>) -> PyResult<bool> {
        self.contains(key)
    }

    fn __len__(&self) -> PyResult<usize> {
        self.inner
            .len()
            .ok_or_else(|| PyRuntimeError::new_err("store does not support len"))
    }

    fn __repr__(&self) -> String {
        match self.inner.len() {
            Some(n) => format!("Store({n} blobs)"),
            None => "Store(?)".to_string(),
        }
    }
}

impl Store {
    pub(crate) fn blob_store(&self) -> BlobStore<covalence_hash::O256> {
        self.inner.clone()
    }
}
