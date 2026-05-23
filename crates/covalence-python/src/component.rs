use std::sync::OnceLock;

use pyo3::exceptions::{PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use crate::hash::O256;

/// Returns true if bytes represent a WASM component (not a core module).
/// Components have encoding byte 0x0d at offset 4; modules have 0x01.
fn is_component_bytes(bytes: &[u8]) -> bool {
    bytes.len() >= 8 && bytes[0..4] == *b"\0asm" && bytes[4] == 0x0d
}

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
        if !is_component_bytes(&wasm) {
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
    fn from_wat(text: &str) -> PyResult<Self> {
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

/// Extract bytes from a Python object: bytes | str | Component -> Vec<u8>.
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
    Err(PyTypeError::new_err("expected bytes, str, or Component"))
}

/// Hash-or-component for polymorphic `decide()`.
pub enum HashOrComponent {
    Hash(covalence_hash::O256),
    Component(Vec<u8>),
}

/// Parse a Python object into either a hash (O256/hex string) or Component.
pub fn parse_hash_or_component(obj: &Bound<'_, PyAny>) -> PyResult<HashOrComponent> {
    if let Ok(o) = obj.extract::<PyRef<O256>>() {
        return Ok(HashOrComponent::Hash(o.0));
    }
    if let Ok(hex) = obj.extract::<String>() {
        let h = covalence_hash::O256::from_hex(&hex)
            .ok_or_else(|| PyValueError::new_err("invalid hex hash (expected 64 hex chars)"))?;
        return Ok(HashOrComponent::Hash(h));
    }
    if let Ok(comp) = obj.extract::<PyRef<Component>>() {
        return Ok(HashOrComponent::Component(comp.wasm_bytes().to_vec()));
    }
    Err(PyTypeError::new_err(
        "expected O256, hex string, or Component",
    ))
}
