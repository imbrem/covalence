use std::sync::OnceLock;
use std::sync::mpsc::Sender;

use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_shell::{Kernel, SyncBackend};

use crate::backend::parse_hash;
use crate::component::extract_bytes;
use crate::hash::O256;
use crate::worker::{KernelTask, kernel_call, spawn_kernel_worker};

static DEFAULT: OnceLock<Sender<KernelTask>> = OnceLock::new();

fn default_tx() -> PyResult<&'static Sender<KernelTask>> {
    if let Some(tx) = DEFAULT.get() {
        return Ok(tx);
    }
    let kernel = Kernel::new();
    let tx = spawn_kernel_worker(kernel);
    // Another thread may have raced us; that's fine — use whichever won.
    let _ = DEFAULT.set(tx);
    Ok(DEFAULT.get().unwrap())
}

/// Store data and return its hash. Accepts bytes, str, or Component.
#[pyfunction]
pub fn store(py: Python<'_>, data: &Bound<'_, PyAny>) -> PyResult<O256> {
    let tx = default_tx()?;
    let bytes = extract_bytes(data)?;
    kernel_call(py, tx, move |k| {
        SyncBackend::store_blob(k, &bytes).map(O256)
    })?
    .map_err(|e| PyRuntimeError::new_err(e.to_string()))
}

/// Store a UTF-8 string as a blob and return its hash.
#[pyfunction]
pub fn store_str(py: Python<'_>, text: &str) -> PyResult<O256> {
    let tx = default_tx()?;
    let data = text.as_bytes().to_vec();
    kernel_call(py, tx, move |k| SyncBackend::store_blob(k, &data).map(O256))?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
}

/// Get a blob by hash. Returns None if not found.
#[pyfunction]
pub fn get<'py>(py: Python<'py>, hash: &Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
    let tx = default_tx()?;
    let h = parse_hash(hash)?;
    let result = kernel_call(py, tx, move |k| SyncBackend::get_blob(k, &h))?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    match result {
        Some(data) => Ok(PyBytes::new(py, &data).into_any()),
        None => Ok(py.None().into_bound(py)),
    }
}

/// Check whether a blob exists.
#[pyfunction]
pub fn has(py: Python<'_>, hash: &Bound<'_, PyAny>) -> PyResult<bool> {
    let tx = default_tx()?;
    let h = parse_hash(hash)?;
    kernel_call(py, tx, move |k| SyncBackend::has_blob(k, &h))?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
}

/// Compile WAT source to WASM, store it, and return the hash.
#[pyfunction]
pub fn compile_wat(py: Python<'_>, wat: &str) -> PyResult<O256> {
    let wasm =
        covalence_wasm::compile_wat(wat).map_err(|e| PyValueError::new_err(e.to_string()))?;
    let tx = default_tx()?;
    kernel_call(py, tx, move |k| SyncBackend::store_blob(k, &wasm).map(O256))?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
}
