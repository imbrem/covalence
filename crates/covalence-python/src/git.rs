use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use crate::hash::O256;

/// Git object hash (SHA-1 or SHA-256).
#[pyclass(from_py_object)]
#[derive(Clone)]
pub struct GitObject {
    hex: String,
    kind: &'static str,
    raw: Vec<u8>,
}

#[pymethods]
impl GitObject {
    #[getter]
    fn hex(&self) -> &str {
        &self.hex
    }

    #[getter]
    fn kind(&self) -> &str {
        self.kind
    }

    /// Convert to O256 (SHA-256 only, raises on SHA-1).
    fn to_o256(&self) -> PyResult<O256> {
        if self.kind != "sha256" {
            return Err(pyo3::exceptions::PyValueError::new_err(
                "cannot convert SHA-1 git object to O256 (20 bytes, not 32)",
            ));
        }
        let arr: [u8; 32] = self.raw[..32]
            .try_into()
            .map_err(|_| PyRuntimeError::new_err("unexpected length"))?;
        Ok(O256(covalence_hash::O256::from_bytes(arr)))
    }

    fn __str__(&self) -> &str {
        &self.hex
    }

    fn __repr__(&self) -> String {
        format!("GitObject({}, {})", self.kind, self.hex)
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.raw)
    }

    fn __eq__(&self, other: &GitObject) -> bool {
        self.raw == other.raw
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.raw.hash(&mut h);
        h.finish()
    }
}

fn oid_to_git_object(oid: covalence_hash::gix_hash::ObjectId) -> GitObject {
    let kind = match oid.kind() {
        covalence_hash::gix_hash::Kind::Sha1 => "sha1",
        covalence_hash::gix_hash::Kind::Sha256 => "sha256",
        _ => "unknown",
    };
    GitObject {
        hex: oid.to_string(),
        kind,
        raw: oid.as_bytes().to_vec(),
    }
}

/// Git hashing strategy that produces GitObject values.
#[pyclass]
pub struct GitHasher {
    kind: covalence_hash::gix_hash::Kind,
}

#[pymethods]
impl GitHasher {
    fn hash_blob(&self, data: &[u8]) -> GitObject {
        let oid = match self.kind {
            covalence_hash::gix_hash::Kind::Sha1 => covalence_hash::git::blob_sha1(data),
            covalence_hash::gix_hash::Kind::Sha256 => covalence_hash::git::blob_sha256(data),
            _ => unreachable!("only sha1 and sha256 are supported"),
        };
        oid_to_git_object(oid)
    }

    fn hash_blob_file(&self, path: &str) -> PyResult<GitObject> {
        let data = std::fs::read(path).map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        Ok(self.hash_blob(&data))
    }

    fn hash_tree(&self, data: &[u8]) -> GitObject {
        let oid = match self.kind {
            covalence_hash::gix_hash::Kind::Sha1 => covalence_hash::git::tree_sha1(data),
            covalence_hash::gix_hash::Kind::Sha256 => covalence_hash::git::tree_sha256(data),
            _ => unreachable!("only sha1 and sha256 are supported"),
        };
        oid_to_git_object(oid)
    }
}

/// Git SHA-1 blob/tree hasher.
#[pyfunction]
pub fn git_sha1() -> GitHasher {
    GitHasher {
        kind: covalence_hash::gix_hash::Kind::Sha1,
    }
}

/// Git SHA-256 blob/tree hasher.
#[pyfunction]
pub fn git_sha256() -> GitHasher {
    GitHasher {
        kind: covalence_hash::gix_hash::Kind::Sha256,
    }
}
