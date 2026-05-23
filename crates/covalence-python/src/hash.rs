use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_hash::{Blake3Ctx, HashCtx, Sha256};

/// 256-bit hash value. Also acts as a BLAKE3 keyed-hash key.
#[pyclass(from_py_object)]
#[derive(Clone)]
pub struct O256(pub covalence_hash::O256);

#[pymethods]
impl O256 {
    /// Parse from 64-char hex string.
    #[staticmethod]
    fn from_hex(hex: &str) -> PyResult<Self> {
        covalence_hash::O256::from_hex(hex)
            .map(O256)
            .ok_or_else(|| PyValueError::new_err("expected 64 hex characters"))
    }

    /// Create from raw 32-byte buffer.
    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        let arr: [u8; 32] = data
            .try_into()
            .map_err(|_| PyValueError::new_err("expected exactly 32 bytes"))?;
        Ok(O256(covalence_hash::O256::from_bytes(arr)))
    }

    /// BLAKE3 hash of data (plain, no key).
    #[staticmethod]
    fn blob(data: &[u8]) -> Self {
        O256(covalence_hash::O256::blob(data))
    }

    /// 64-char hex string.
    #[getter]
    fn hex(&self) -> String {
        self.0.to_string()
    }

    /// BLAKE3 keyed hash with self as key.
    fn hash(&self, data: &[u8]) -> O256 {
        O256(self.0.tag(data))
    }

    /// Read file, then BLAKE3 keyed hash with self as key.
    fn hash_file(&self, path: &str) -> PyResult<O256> {
        let data = std::fs::read(path).map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        Ok(O256(self.0.tag(&data)))
    }

    fn __str__(&self) -> String {
        self.0.to_string()
    }

    fn __repr__(&self) -> String {
        format!("O256({})", self.0)
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, self.0.as_bytes())
    }

    fn __eq__(&self, other: &O256) -> bool {
        self.0 == other.0
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.0.hash(&mut h);
        h.finish()
    }
}

enum HasherInner {
    Blake3,
    Blake3Keyed(covalence_hash::O256),
    Blake3Kdf(Blake3Ctx),
    Sha256,
}

/// Hashing strategy that produces O256 values.
#[pyclass]
pub struct Hasher {
    inner: HasherInner,
}

#[pymethods]
impl Hasher {
    fn hash(&self, data: &[u8]) -> O256 {
        let h = match &self.inner {
            HasherInner::Blake3 => ().tag(data),
            HasherInner::Blake3Keyed(key) => key.tag(data),
            HasherInner::Blake3Kdf(ctx) => ctx.tag(data),
            HasherInner::Sha256 => Sha256.tag(data),
        };
        O256(h)
    }

    fn hash_file(&self, path: &str) -> PyResult<O256> {
        let data = std::fs::read(path).map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        Ok(self.hash(&data))
    }
}

/// Plain BLAKE3 hasher.
#[pyfunction]
pub fn blake3() -> Hasher {
    Hasher {
        inner: HasherInner::Blake3,
    }
}

/// BLAKE3 keyed hasher.
#[pyfunction]
pub fn blake3_keyed(key: &O256) -> Hasher {
    Hasher {
        inner: HasherInner::Blake3Keyed(key.0),
    }
}

/// BLAKE3 key-derivation hasher.
#[pyfunction]
pub fn blake3_kdf(ctx: &str) -> Hasher {
    Hasher {
        inner: HasherInner::Blake3Kdf(Blake3Ctx::new(ctx)),
    }
}

/// SHA-256 hasher.
#[pyfunction]
pub fn sha256() -> Hasher {
    Hasher {
        inner: HasherInner::Sha256,
    }
}

/// Get a hasher by name.
#[pyfunction]
pub fn hasher(name: &str) -> PyResult<Hasher> {
    match name {
        "blake3" => Ok(blake3()),
        "sha256" => Ok(sha256()),
        _ => Err(PyValueError::new_err(format!("unknown hasher: {name}"))),
    }
}
