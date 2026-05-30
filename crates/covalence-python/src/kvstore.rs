use std::sync::Arc;

use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_store::KvStore as KvStoreTrait;

// ---------------------------------------------------------------------------
// PyKvStore — bridges a Python object to KvStore trait
// ---------------------------------------------------------------------------

/// Wraps a Python object implementing the KV store protocol as a Rust `KvStore`.
struct PyKvStore {
    obj: Py<PyAny>,
    has_touch: bool,
    has_touched: bool,
}

impl KvStoreTrait for PyKvStore {
    fn set(&self, key: &[u8], value: &[u8]) {
        Python::attach(|py| {
            let py_key = PyBytes::new(py, key);
            let py_value = PyBytes::new(py, value);
            let _ = self.obj.call_method1(py, "set", (py_key, py_value));
        });
    }

    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        Python::attach(|py| {
            let py_key = PyBytes::new(py, key);
            let result = self.obj.call_method1(py, "get", (py_key,)).ok()?;
            if result.is_none(py) {
                return None;
            }
            result.extract::<Vec<u8>>(py).ok()
        })
    }

    fn touch(&self, key: &[u8]) {
        if self.has_touch {
            Python::attach(|py| {
                let py_key = PyBytes::new(py, key);
                let _ = self.obj.call_method1(py, "touch", (py_key,));
            });
        }
    }

    fn touched(&self, key: &[u8]) -> bool {
        if self.has_touched {
            return Python::attach(|py| {
                let py_key = PyBytes::new(py, key);
                self.obj
                    .call_method1(py, "touched", (py_key,))
                    .and_then(|r| r.extract::<bool>(py))
                    .unwrap_or(false)
            });
        }
        false
    }

    fn ns(&self, key: &[u8]) -> Arc<dyn KvStoreTrait> {
        Python::attach(|py| {
            let py_key = PyBytes::new(py, key);
            let result = self.obj.call_method1(py, "ns", (py_key,)).unwrap();
            let bound = result.into_bound(py);

            // If the result is already a KvStore pyclass, extract the inner Arc
            if let Ok(kv) = bound.cast::<KvStore>() {
                return kv.borrow().inner.clone();
            }

            // Otherwise, wrap the Python object
            let has_touch = bound.hasattr("touch").unwrap_or(false);
            let has_touched = bound.hasattr("touched").unwrap_or(false);
            Arc::new(PyKvStore {
                obj: bound.unbind(),
                has_touch,
                has_touched,
            })
        })
    }

    fn dup(&self) -> Arc<dyn KvStoreTrait> {
        Python::attach(|py| {
            let result = self.obj.call_method0(py, "dup").unwrap();
            let bound = result.into_bound(py);

            if let Ok(kv) = bound.cast::<KvStore>() {
                return kv.borrow().inner.clone();
            }

            let has_touch = bound.hasattr("touch").unwrap_or(false);
            let has_touched = bound.hasattr("touched").unwrap_or(false);
            Arc::new(PyKvStore {
                obj: bound.unbind(),
                has_touch,
                has_touched,
            })
        })
    }
}

// Safety: PyKvStore holds a Py<PyAny> which is Send + Sync
unsafe impl Send for PyKvStore {}
unsafe impl Sync for PyKvStore {}

// ---------------------------------------------------------------------------
// KvStore pyclass
// ---------------------------------------------------------------------------

/// Hierarchical key-value store.
///
/// Construct from a Python KV store object, or use `KvStore.memory()` for
/// a Rust-backed in-memory store.
#[pyclass]
pub struct KvStore {
    inner: Arc<dyn KvStoreTrait>,
}

#[pymethods]
impl KvStore {
    /// Wrap a Python object implementing the KV store protocol.
    ///
    /// Required methods: `set(key, value)`, `get(key)`, `ns(key)`, `dup()`.
    /// Optional methods: `touch(key)`, `touched(key)`.
    #[new]
    fn new(obj: &Bound<'_, PyAny>) -> PyResult<Self> {
        for method in &["set", "get", "ns", "dup"] {
            if !obj.hasattr(*method)? {
                return Err(PyTypeError::new_err(format!(
                    "KV store object must have a '{method}' method"
                )));
            }
        }
        let has_touch = obj.hasattr("touch")?;
        let has_touched = obj.hasattr("touched")?;
        let py_store = PyKvStore {
            obj: obj.clone().unbind(),
            has_touch,
            has_touched,
        };
        Ok(Self {
            inner: Arc::new(py_store),
        })
    }

    /// Create an in-memory KV store backed by Rust.
    #[staticmethod]
    fn memory() -> Self {
        Self {
            inner: Arc::new(covalence_store::MemoryKvStore::new()),
        }
    }

    /// Insert or overwrite a value.
    fn set(&self, key: &[u8], value: &[u8]) {
        self.inner.set(key, value);
    }

    /// Look up a value by key. Returns bytes or None.
    fn get<'py>(&self, py: Python<'py>, key: &[u8]) -> Option<Bound<'py, PyBytes>> {
        self.inner.get(key).map(|data| PyBytes::new(py, &data))
    }

    /// Mark a key as touched.
    fn touch(&self, key: &[u8]) {
        self.inner.touch(key);
    }

    /// Check whether a key has been touched.
    fn touched(&self, key: &[u8]) -> bool {
        self.inner.touched(key)
    }

    /// Navigate to a child namespace.
    fn ns(&self, key: &[u8]) -> Self {
        Self {
            inner: self.inner.ns(key),
        }
    }

    /// Duplicate this handle (same underlying data).
    fn dup(&self) -> Self {
        Self {
            inner: self.inner.dup(),
        }
    }

    fn __repr__(&self) -> String {
        "KvStore(...)".to_string()
    }
}
