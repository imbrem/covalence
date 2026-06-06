//! Python bindings for `covalence-wasm-store`.
//!
//! Minimum surface to drive the s3_path / merge / single_blob
//! examples from Python: build a component, wrap a wasmtime
//! instance, call `get` / `contains` / `head`. Synchronous — the
//! sync helpers on `WasmStore` do all the work, no runtime needed.
//!
//! Usage sketch:
//!
//! ```python
//! from covalence import wasm_store as ws
//!
//! # A leaf store that knows exactly one (path, blob) pair.
//! path = b"blobs/" + b"abcdef12"
//! leaf_bytes = ws.build_single_blob(path, b"the stored blob")
//! leaf = ws.WasmStore.from_bytes(leaf_bytes)
//!
//! # An s3_path composer that constructs prefix + hex(key) on each call.
//! composer_bytes = ws.build_s3_path_composer("blobs/")
//! composed = ws.WasmStore.compose(composer_bytes, [leaf])
//!
//! assert composed.get(bytes.fromhex("abcdef12")) == b"the stored blob"
//! ```

use std::sync::Arc;

use pyo3::exceptions::{PyKeyError, PyRuntimeError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyList};

use covalence_kv::{BlockingKv, Error as KvError};
use covalence_store::{BlobInfo, StoreError};
use covalence_wasm_store::{
    BlobSource, WasmStore as InnerStore, merge, s3_path, single_blob,
};

use crate::kvstore::KvStore as PyKvStore;

// ---------------------------------------------------------------------------
// Component builders — return WASM component bytes
// ---------------------------------------------------------------------------

/// Build a single-blob leaf component knowing exactly one
/// (key → blob) pair. Other keys return None.
///
/// `key` is the literal byte string the store matches against —
/// for the s3_path test, that's the UTF-8 encoding of
/// `prefix + hex(actual_hash)`.
#[pyfunction]
#[pyo3(signature = (key, blob))]
fn build_single_blob<'py>(
    py: Python<'py>,
    key: &[u8],
    blob: &[u8],
) -> PyResult<Bound<'py, PyBytes>> {
    let bytes = single_blob::build_component(key, blob, None)
        .map_err(|e| PyRuntimeError::new_err(format!("build single_blob: {e}")))?;
    Ok(PyBytes::new(py, &bytes))
}

/// Build a `merge` composer component. On `get` / `head` it returns
/// the first backing's `Some`; on `contains` it ORs across all
/// backings.
#[pyfunction]
fn build_merge_composer(py: Python<'_>) -> PyResult<Bound<'_, PyBytes>> {
    let bytes = merge::build_component()
        .map_err(|e| PyRuntimeError::new_err(format!("build merge composer: {e}")))?;
    Ok(PyBytes::new(py, &bytes))
}

/// Build an `s3_path` composer. On every call it constructs
/// `prefix + hex(key)` and routes through the upstream stores. The
/// prefix is embedded as a data segment — change the prefix, get a
/// different component hash.
#[pyfunction]
fn build_s3_path_composer<'py>(py: Python<'py>, prefix: &str) -> PyResult<Bound<'py, PyBytes>> {
    let bytes = s3_path::build_component(prefix)
        .map_err(|e| PyRuntimeError::new_err(format!("build s3_path composer: {e}")))?;
    Ok(PyBytes::new(py, &bytes))
}

/// Hex-encode bytes (lowercase, no separators). Convenience —
/// matches what the s3_path composer does internally.
#[pyfunction]
fn hex_encode(data: &[u8]) -> String {
    s3_path::hex_encode(data)
}

// ---------------------------------------------------------------------------
// WasmStore — wraps covalence_wasm_store::WasmStore
// ---------------------------------------------------------------------------

/// A live store backing.
///
/// Holds an `Arc<dyn BlobSource>` so the Python type can wrap
/// either a wasmtime component (`from_bytes` / `compose`) or a
/// kv-shaped backing (`from_kv`) interchangeably. The composer
/// linker shims see them the same way.
#[pyclass(name = "WasmStore", from_py_object)]
#[derive(Clone)]
pub struct PyWasmStore {
    inner: Arc<dyn BlobSource>,
}

#[pymethods]
impl PyWasmStore {
    /// Instantiate a leaf store from raw component bytes.
    #[staticmethod]
    fn from_bytes(bytes: &[u8]) -> PyResult<Self> {
        let inner = InnerStore::from_component_bytes(bytes)
            .map_err(|e| PyRuntimeError::new_err(format!("instantiate: {e}")))?;
        Ok(Self {
            inner: Arc::new(inner),
        })
    }

    /// Wrap an existing `KvStore` (memory, AWS, S3-compatible R2 /
    /// B2 / Wasabi / MinIO …) as a store backing.
    ///
    /// The composer's lowered `list<u8>` key is decoded as UTF-8
    /// and used as the kv path. The `s3_path` composer pairs with
    /// this naturally: it turns a raw hash into `prefix + hex(hash)`
    /// at the WASM layer, then hands the resulting bytes to this
    /// adapter — which interprets them as the kv key.
    #[staticmethod]
    fn from_kv(kv: &PyKvStore) -> PyResult<Self> {
        Ok(Self {
            inner: Arc::new(KvBacked {
                kv: kv.inner.clone(),
            }),
        })
    }

    /// Instantiate a composer over N backings. `backings` is a list
    /// of `WasmStore` instances; each becomes one upstream handle
    /// the composer can call into.
    #[staticmethod]
    fn compose(bytes: &[u8], backings: &Bound<'_, PyList>) -> PyResult<Self> {
        let mut owned: Vec<Arc<dyn BlobSource>> = Vec::with_capacity(backings.len());
        for item in backings.iter() {
            let st: PyWasmStore = item.extract()?;
            owned.push(st.inner);
        }
        let inner = InnerStore::compose(bytes, owned)
            .map_err(|e| PyRuntimeError::new_err(format!("compose: {e}")))?;
        Ok(Self {
            inner: Arc::new(inner),
        })
    }

    /// Fetch the value for `key`. Raises `KeyError` if absent.
    fn get<'py>(&self, py: Python<'py>, key: &[u8]) -> PyResult<Bound<'py, PyBytes>> {
        match self.inner.blob_get(key) {
            Ok(Some(v)) => Ok(PyBytes::new(py, &v)),
            Ok(None) => Err(PyKeyError::new_err(hex_or_repr(key))),
            Err(e) => Err(map_store_error(e, key)),
        }
    }

    /// Fetch the value for `key`, or `None` if absent. No exception
    /// for a miss — useful when absence is part of normal control
    /// flow.
    fn try_get<'py>(
        &self,
        py: Python<'py>,
        key: &[u8],
    ) -> PyResult<Option<Bound<'py, PyBytes>>> {
        match self.inner.blob_get(key) {
            Ok(Some(v)) => Ok(Some(PyBytes::new(py, &v))),
            Ok(None) => Ok(None),
            Err(e) => Err(map_store_error(e, key)),
        }
    }

    /// True iff `key` is present.
    fn contains(&self, key: &[u8]) -> PyResult<bool> {
        self.inner
            .blob_contains(key)
            .map_err(|e| map_store_error(e, key))
    }

    /// Size of the value at `key` in bytes, or `None` if absent.
    fn head(&self, key: &[u8]) -> PyResult<Option<u64>> {
        self.inner
            .blob_head(key)
            .map(|opt| opt.map(|info| info.size))
            .map_err(|e| map_store_error(e, key))
    }
}

// ---------------------------------------------------------------------------
// KvBacked — adapt covalence_kv::KvStore (sync via BlockingKv) as BlobSource
// ---------------------------------------------------------------------------

/// Adapter from a blocking [`covalence_kv::KvStore`] handle to the
/// [`BlobSource`] trait the composer linker calls into.
///
/// The lowered key bytes are interpreted as a UTF-8 path. Bytes
/// that aren't valid UTF-8 propagate as an `Io` error rather than
/// silently failing — they'd almost certainly indicate the wrong
/// composer / backing pairing.
struct KvBacked {
    kv: BlockingKv,
}

impl BlobSource for KvBacked {
    fn blob_get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, StoreError> {
        let path = std::str::from_utf8(key)
            .map_err(|e| StoreError::Io(format!("kv key not utf-8: {e}")))?;
        match self.kv.get(path) {
            Ok(bytes) => Ok(Some(bytes.to_vec())),
            Err(KvError::NotFound { .. }) => Ok(None),
            Err(e) => Err(StoreError::Io(format!("kv get: {e}"))),
        }
    }

    fn blob_contains(&self, key: &[u8]) -> Result<bool, StoreError> {
        match self.blob_head(key) {
            Ok(Some(_)) => Ok(true),
            Ok(None) => Ok(false),
            Err(e) => Err(e),
        }
    }

    fn blob_head(&self, key: &[u8]) -> Result<Option<BlobInfo>, StoreError> {
        let path = std::str::from_utf8(key)
            .map_err(|e| StoreError::Io(format!("kv key not utf-8: {e}")))?;
        match self.kv.head(path) {
            Ok(meta) => Ok(Some(BlobInfo { size: meta.size })),
            Err(KvError::NotFound { .. }) => Ok(None),
            Err(e) => Err(StoreError::Io(format!("kv head: {e}"))),
        }
    }
}


fn map_store_error(e: StoreError, key: &[u8]) -> PyErr {
    match e {
        StoreError::NotFound => PyKeyError::new_err(hex_or_repr(key)),
        other => PyRuntimeError::new_err(other.to_string()),
    }
}

fn hex_or_repr(key: &[u8]) -> String {
    // Show short keys as hex; longer ones get truncated. Helps
    // diagnose path-shaped key misses without spamming output.
    if key.len() <= 64 {
        s3_path::hex_encode(key)
    } else {
        format!("{}…({} bytes total)", s3_path::hex_encode(&key[..32]), key.len())
    }
}

// ---------------------------------------------------------------------------
// Module registration
// ---------------------------------------------------------------------------

pub fn register(parent: &Bound<'_, PyModule>) -> PyResult<()> {
    let m = PyModule::new(parent.py(), "wasm_store")?;
    m.add_class::<PyWasmStore>()?;
    m.add_function(wrap_pyfunction!(build_single_blob, &m)?)?;
    m.add_function(wrap_pyfunction!(build_merge_composer, &m)?)?;
    m.add_function(wrap_pyfunction!(build_s3_path_composer, &m)?)?;
    m.add_function(wrap_pyfunction!(hex_encode, &m)?)?;
    parent.add_submodule(&m)?;
    Ok(())
}
