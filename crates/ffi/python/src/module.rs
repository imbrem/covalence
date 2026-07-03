use std::sync::OnceLock;

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use crate::hash::O256;

/// Validated WASM core module with cached metadata.
#[pyclass(from_py_object)]
#[derive(Clone)]
pub struct Module {
    wasm: Vec<u8>,
    imports: Vec<(String, String)>,
    exports: Vec<String>,
    hash_cache: OnceLock<covalence_hash::O256>,
}

impl Module {
    /// Parse and validate WASM bytes as a core module. Internal entry
    /// point shared between `from_bytes` and the byte-stream path used
    /// by `ModuleBuilder.build`.
    pub(crate) fn from_bytes_internal(wasm: Vec<u8>) -> PyResult<Self> {
        Self::from_wasm_bytes(wasm)
    }

    fn from_wasm_bytes(wasm: Vec<u8>) -> PyResult<Self> {
        if !covalence_wasm::is_module(&wasm) {
            return Err(PyValueError::new_err(
                "expected a WASM core module, got a component or invalid bytes",
            ));
        }
        let info = covalence_wasm::parse_module(&wasm)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(Module {
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
impl Module {
    /// Create a Module from raw WASM bytes. Must be a valid core module.
    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        Self::from_wasm_bytes(data.to_vec())
    }

    /// Create a Module from WAT text. The WAT must describe a module, not a component.
    #[staticmethod]
    pub(crate) fn from_wat(text: &str) -> PyResult<Self> {
        let wasm =
            covalence_wasm::compile_wat(text).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Self::from_wasm_bytes(wasm)
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

    /// Import pairs as list of (module, name) tuples.
    #[getter]
    fn imports(&self) -> Vec<(String, String)> {
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
            "Module({hex}, {} bytes, {} imports, {} exports)",
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

    fn __eq__(&self, other: &Module) -> bool {
        self.content_hash() == other.content_hash()
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.content_hash().hash(&mut h);
        h.finish()
    }
}
