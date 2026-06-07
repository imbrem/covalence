use std::sync::OnceLock;

use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use crate::container::Container;
use crate::hash::O256;
use crate::module::Module;

/// Validated WASM component with cached metadata.
#[pyclass(from_py_object)]
#[derive(Clone)]
pub struct Component {
    wasm: Vec<u8>,
    imports: Vec<String>,
    exports: Vec<String>,
    hash_cache: OnceLock<covalence_hash::O256>,
}

impl Component {
    /// Parse and validate WASM bytes as a component.
    fn from_wasm_bytes(wasm: Vec<u8>) -> PyResult<Self> {
        if !covalence_wasm::is_component(&wasm) {
            return Err(PyValueError::new_err(
                "expected a WASM component, got a core module or invalid bytes",
            ));
        }
        let info = covalence_wasm::parse_component(&wasm)
            .map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(Component {
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
impl Component {
    /// Create a Component from WAT text. The WAT must describe a component, not a module.
    #[staticmethod]
    pub fn from_wat(text: &str) -> PyResult<Self> {
        let wasm =
            covalence_wasm::compile_wat(text).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Self::from_wasm_bytes(wasm)
    }

    /// Create a Component from raw WASM bytes. Must be a valid component.
    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Self> {
        Self::from_wasm_bytes(data.to_vec())
    }

    /// Raw WASM bytes.
    #[getter]
    fn bytes<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.wasm)
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

    /// Decompiled WAT text (not cached — can be expensive).
    #[getter]
    fn wat(&self) -> PyResult<String> {
        covalence_wasm::wasm_to_wat(&self.wasm).map_err(|e| PyValueError::new_err(e.to_string()))
    }

    /// Content hash (BLAKE3, lazy).
    #[getter]
    fn hash(&self) -> O256 {
        O256(self.content_hash())
    }

    fn __len__(&self) -> usize {
        self.wasm.len()
    }

    fn __repr__(&self) -> String {
        let hash = self.content_hash();
        let hex = &hash.to_string()[..8];
        format!(
            "Component({hex}, {} bytes, {} imports, {} exports)",
            self.wasm.len(),
            self.imports.len(),
            self.exports.len()
        )
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.wasm)
    }

    fn __eq__(&self, other: &Component) -> bool {
        self.content_hash() == other.content_hash()
    }

    fn __hash__(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.content_hash().hash(&mut h);
        h.finish()
    }
}

/// Extract bytes from a Python object: bytes | str | Component | Module | Container -> Vec<u8>.
pub fn extract_bytes(obj: &Bound<'_, PyAny>) -> PyResult<Vec<u8>> {
    if let Ok(data) = obj.extract::<Vec<u8>>() {
        return Ok(data);
    }
    if let Ok(text) = obj.extract::<String>() {
        return Ok(text.into_bytes());
    }
    if let Ok(comp) = obj.extract::<PyRef<Component>>() {
        return Ok(comp.wasm_bytes().to_vec());
    }
    if let Ok(m) = obj.extract::<PyRef<Module>>() {
        return Ok(m.wasm_bytes().to_vec());
    }
    if let Ok(c) = obj.extract::<PyRef<Container>>() {
        return Ok(c.wasm_bytes().to_vec());
    }
    Err(PyTypeError::new_err(
        "expected bytes, str, Component, Module, or Container",
    ))
}
