use std::sync::OnceLock;

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use crate::component::Component;
use crate::hash::O256;

/// Returns true if bytes represent a WASM component (not a core module).
fn is_component_bytes(bytes: &[u8]) -> bool {
    bytes.len() >= 8 && bytes[0..4] == *b"\0asm" && bytes[4] == 0x0d
}

/// Validated WASM container: a component whose imports all conform to the
/// kernel's expected format, ready for proving.
#[pyclass(from_py_object)]
#[derive(Clone)]
pub struct Container {
    wasm: Vec<u8>,
    imports: Vec<String>,
    exports: Vec<String>,
    hash_cache: OnceLock<covalence_hash::O256>,
}

impl Container {
    /// Parse as component + validate kernel imports.
    fn from_wasm_bytes(wasm: Vec<u8>) -> PyResult<Self> {
        if !is_component_bytes(&wasm) {
            return Err(PyValueError::new_err(
                "expected a WASM component, got a core module or invalid bytes",
            ));
        }
        let info = covalence_wasm::parse_component(&wasm)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(Container {
            wasm,
            imports: info.imports,
            exports: info.exports,
            hash_cache: OnceLock::new(),
        })
    }

    /// Get the raw WASM bytes.
    pub fn wasm_bytes(&self) -> &[u8] {
        &self.wasm
    }

    /// Get the content hash, computing it lazily.
    pub fn content_hash(&self) -> covalence_hash::O256 {
        *self
            .hash_cache
            .get_or_init(|| covalence_hash::O256::blob(&self.wasm))
    }
}

#[pymethods]
impl Container {
    /// Create a Container from raw WASM bytes. Must be a valid component with
    /// recognized kernel imports.
    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        Self::from_wasm_bytes(data.to_vec())
    }

    /// Create a Container from WAT text.
    #[staticmethod]
    pub(crate) fn from_wat(text: &str) -> PyResult<Self> {
        let wasm =
            covalence_wasm::compile_wat(text).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Self::from_wasm_bytes(wasm)
    }

    /// Create a Container from an existing Component by validating its imports.
    #[staticmethod]
    fn from_component(c: &Component) -> PyResult<Self> {
        Self::from_wasm_bytes(c.wasm_bytes().to_vec())
    }

    /// Raw WASM bytes.
    #[getter]
    fn bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.wasm)
    }

    /// Content hash (BLAKE3, lazy).
    #[getter]
    fn hash(&self) -> O256 {
        O256(self.content_hash())
    }

    /// Import names.
    #[getter]
    fn imports(&self) -> Vec<String> {
        self.imports.clone()
    }

    /// Export names.
    #[getter]
    fn exports(&self) -> Vec<String> {
        self.exports.clone()
    }

    fn __repr__(&self) -> String {
        let hash = self.content_hash();
        let hex = &hash.to_string()[..8];
        format!(
            "Container({hex}, {} bytes, {} imports, {} exports)",
            self.wasm.len(),
            self.imports.len(),
            self.exports.len()
        )
    }

    fn __len__(&self) -> usize {
        self.wasm.len()
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.wasm)
    }

    fn __eq__(&self, other: &Container) -> bool {
        self.content_hash() == other.content_hash()
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.content_hash().hash(&mut h);
        h.finish()
    }
}
