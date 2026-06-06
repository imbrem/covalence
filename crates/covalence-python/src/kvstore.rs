//! Python bindings for `covalence_kv::KvStore`, exposed as a blocking API.
//!
//! Base class `KvStore` is abstract — Python users construct one of the
//! subclasses (`MemoryKvStore`, `AwsKvStore`, `S3KvStore`). Each subclass
//! constructs a backend and stores it as a `BlockingKv` on the base.

use std::sync::{Arc, OnceLock};

use bytes::Bytes;
use pyo3::exceptions::{PyIOError, PyKeyError, PyPermissionError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use tokio::runtime::{Handle, Runtime};

use covalence_kv::{BlockingKv, Error as KvError, MemoryKv, aws};

/// Shared tokio runtime for all blocking-KV operations.
fn rt_handle() -> Handle {
    static RT: OnceLock<Runtime> = OnceLock::new();
    RT.get_or_init(|| {
        tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .thread_name("covalence-kv")
            .build()
            .expect("tokio runtime")
    })
    .handle()
    .clone()
}

fn map_err(e: KvError) -> PyErr {
    match e {
        KvError::NotFound { key } => PyKeyError::new_err(key),
        KvError::InvalidKey { key, reason } => {
            PyValueError::new_err(format!("invalid key {key:?}: {reason}"))
        }
        KvError::RangeOutOfBounds { .. } => PyValueError::new_err(e.to_string()),
        KvError::Auth(msg) => PyPermissionError::new_err(msg),
        KvError::Backend(msg) => PyIOError::new_err(msg),
    }
}

// ---------------------------------------------------------------------------
// Base class
// ---------------------------------------------------------------------------

/// Async key-value store driven from Python as a blocking API.
///
/// Abstract: construct one of the subclasses (`MemoryKvStore`,
/// `AwsKvStore`, `S3KvStore`). The methods on this class operate on
/// any backend transparently.
#[pyclass(subclass)]
pub struct KvStore {
    inner: BlockingKv,
}

#[pymethods]
impl KvStore {
    /// `KvStore` is abstract — instantiate a subclass instead.
    #[new]
    fn new() -> PyResult<Self> {
        Err(PyTypeError::new_err(
            "KvStore is abstract; instantiate a subclass \
             (MemoryKvStore, AwsKvStore, S3KvStore)",
        ))
    }

    /// Fetch the full value at `key`. Raises `KeyError` on miss.
    fn get<'py>(&self, py: Python<'py>, key: &str) -> PyResult<Bound<'py, PyBytes>> {
        let kv = self.inner.clone();
        let key = key.to_string();
        let bytes = py.detach(move || kv.get(&key)).map_err(map_err)?;
        Ok(PyBytes::new(py, &bytes))
    }

    /// Fetch a byte range `[start, end)` of the value at `key`.
    fn get_range<'py>(
        &self,
        py: Python<'py>,
        key: &str,
        start: u64,
        end: u64,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let kv = self.inner.clone();
        let key = key.to_string();
        let bytes = py
            .detach(move || kv.get_range(&key, start..end))
            .map_err(map_err)?;
        Ok(PyBytes::new(py, &bytes))
    }

    /// Store `value` at `key`, overwriting any existing value.
    fn put(&self, py: Python<'_>, key: &str, value: &[u8]) -> PyResult<()> {
        let kv = self.inner.clone();
        let key = key.to_string();
        let value = Bytes::copy_from_slice(value);
        py.detach(move || kv.put(&key, value)).map_err(map_err)
    }

    /// Delete `key`. Idempotent.
    fn delete(&self, py: Python<'_>, key: &str) -> PyResult<()> {
        let kv = self.inner.clone();
        let key = key.to_string();
        py.detach(move || kv.delete(&key)).map_err(map_err)
    }

    /// Return metadata for `key` as a dict with `size`, `etag` (or None).
    fn head<'py>(&self, py: Python<'py>, key: &str) -> PyResult<Bound<'py, PyAny>> {
        let kv = self.inner.clone();
        let key_owned = key.to_string();
        let meta = py
            .detach(move || kv.head(&key_owned))
            .map_err(map_err)?;
        let d = pyo3::types::PyDict::new(py);
        d.set_item("size", meta.size)?;
        d.set_item("etag", meta.etag)?;
        Ok(d.into_any())
    }

    fn __repr__(&self) -> String {
        "KvStore(...)".to_string()
    }
}

// ---------------------------------------------------------------------------
// Subclasses
// ---------------------------------------------------------------------------

/// In-memory KV store backed by Rust. Useful for tests.
#[pyclass(extends = KvStore)]
pub struct MemoryKvStore;

#[pymethods]
impl MemoryKvStore {
    #[new]
    fn new() -> (Self, KvStore) {
        let blocking = BlockingKv::new(Arc::new(MemoryKv::new()), rt_handle());
        (Self, KvStore { inner: blocking })
    }
}

/// AWS S3 using the default credential chain (env vars, `~/.aws/credentials`, IMDS).
#[pyclass(extends = KvStore)]
pub struct AwsKvStore;

#[pymethods]
impl AwsKvStore {
    #[new]
    fn new(bucket: String, region: String) -> PyResult<(Self, KvStore)> {
        let s3 = aws::Config::aws(bucket, region)
            .build()
            .map_err(|e| PyIOError::new_err(e.to_string()))?;
        let blocking = BlockingKv::new(Arc::new(aws::S3Kv::new(s3)), rt_handle());
        Ok((Self, KvStore { inner: blocking }))
    }
}

/// S3-compatible endpoint with explicit credentials (Wasabi, Backblaze B2,
/// Cloudflare R2, MinIO, etc.). Defaults to path-style addressing.
#[pyclass(extends = KvStore)]
pub struct S3KvStore;

#[pymethods]
impl S3KvStore {
    #[new]
    #[pyo3(signature = (
        endpoint,
        region,
        bucket,
        access_key_id,
        secret_access_key,
        *,
        allow_http = false,
        virtual_hosted_style = false,
    ))]
    fn new(
        endpoint: String,
        region: String,
        bucket: String,
        access_key_id: String,
        secret_access_key: String,
        allow_http: bool,
        virtual_hosted_style: bool,
    ) -> PyResult<(Self, KvStore)> {
        let s3 = aws::Config::custom(endpoint, region, bucket, access_key_id, secret_access_key)
            .with_virtual_hosted_style(virtual_hosted_style)
            .with_allow_http(allow_http)
            .build()
            .map_err(|e| PyIOError::new_err(e.to_string()))?;
        let blocking = BlockingKv::new(Arc::new(aws::S3Kv::new(s3)), rt_handle());
        Ok((Self, KvStore { inner: blocking }))
    }
}
