use std::sync::mpsc;

use pyo3::exceptions::{PyRuntimeError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_kernel::{Kernel, SyncBackend};
use covalence_store::BlobStore;

use crate::component::{HashOrComponent, extract_bytes, parse_hash_or_component};
use crate::container::Container;
use crate::hash::O256;
use crate::store::Store;
use crate::worker::{KernelTask, kernel_call, spawn_kernel_worker};

pub fn parse_hash(obj: &Bound<'_, PyAny>) -> PyResult<covalence_hash::O256> {
    if let Ok(o) = obj.extract::<PyRef<O256>>() {
        return Ok(o.0);
    }
    if let Ok(hex) = obj.extract::<String>() {
        return covalence_hash::O256::from_hex(&hex)
            .ok_or_else(|| PyValueError::new_err("invalid hex hash (expected 64 hex chars)"));
    }
    Err(PyTypeError::new_err("expected O256 or hex string"))
}

/// Covalence backend: content store + WASM engine on a background thread.
#[pyclass]
pub struct Backend {
    tx: mpsc::Sender<KernelTask>,
}

#[pymethods]
impl Backend {
    /// Store data and return its hash. Accepts bytes, str, or Component.
    fn store(&self, py: Python<'_>, data: &Bound<'_, PyAny>) -> PyResult<O256> {
        let bytes = extract_bytes(data)?;
        kernel_call(py, &self.tx, move |k| {
            SyncBackend::store_blob(k, &bytes).map(O256)
        })?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn store_blob(&self, py: Python<'_>, data: &[u8]) -> PyResult<O256> {
        let data = data.to_vec();
        kernel_call(py, &self.tx, move |k| {
            SyncBackend::store_blob(k, &data).map(O256)
        })?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn store_str(&self, py: Python<'_>, text: &str) -> PyResult<O256> {
        let data = text.as_bytes().to_vec();
        kernel_call(py, &self.tx, move |k| {
            SyncBackend::store_blob(k, &data).map(O256)
        })?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn get_blob<'py>(
        &self,
        py: Python<'py>,
        hash: &Bound<'py, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let h = parse_hash(hash)?;
        let result = kernel_call(py, &self.tx, move |k| SyncBackend::get_blob(k, &h))?
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        match result {
            Some(data) => Ok(PyBytes::new(py, &data).into_any()),
            None => Ok(py.None().into_bound(py)),
        }
    }

    fn has_blob(&self, py: Python<'_>, hash: &Bound<'_, PyAny>) -> PyResult<bool> {
        let h = parse_hash(hash)?;
        kernel_call(py, &self.tx, move |k| SyncBackend::has_blob(k, &h))?
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn blob_count(&self, py: Python<'_>) -> PyResult<Option<usize>> {
        kernel_call(py, &self.tx, |k| SyncBackend::blob_count(k))?
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn compile_wat(&self, py: Python<'_>, wat: &str) -> PyResult<O256> {
        // Compile WAT->WASM on the calling thread (no kernel needed)
        let wasm =
            covalence_wasm::compile_wat(wat).map_err(|e| PyValueError::new_err(e.to_string()))?;
        // Store the blob on the kernel thread
        kernel_call(py, &self.tx, move |k| {
            SyncBackend::store_blob(k, &wasm).map(O256)
        })?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    /// Decide a WASM proposition. Accepts O256, hex string, or Component.
    /// When given a Component, stores and decides in a single worker round-trip.
    fn decide<'py>(
        &self,
        py: Python<'py>,
        hash: &Bound<'py, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let parsed = parse_hash_or_component(hash)?;
        let output = match parsed {
            HashOrComponent::Hash(h) => {
                kernel_call(py, &self.tx, move |k| SyncBackend::decide(k, &h))?
            }
            HashOrComponent::Component(wasm) => kernel_call(py, &self.tx, move |k| {
                let h = SyncBackend::store_blob(k, &wasm)?;
                SyncBackend::decide(k, &h)
            })?,
        }
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        let dict = pyo3::types::PyDict::new(py);
        dict.set_item("decision", output.decision.to_string())?;
        let proved: Vec<String> = output.proved.iter().map(|h| h.to_string()).collect();
        dict.set_item("proved", proved)?;
        Ok(dict.into_any())
    }

    /// Prove a container: store it, run it, and if Sat add the container's
    /// own hash to the proved set. Accepts a Container.
    fn prove<'py>(&self, py: Python<'py>, container: &Container) -> PyResult<Bound<'py, PyAny>> {
        let wasm = container.wasm_bytes().to_vec();
        let output = kernel_call(py, &self.tx, move |k| {
            let h = SyncBackend::store_blob(k, &wasm)?;
            k.prove_container(&h)
        })?
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        let dict = pyo3::types::PyDict::new(py);
        dict.set_item("decision", output.decision.to_string())?;
        let proved: Vec<String> = output.proved.iter().map(|h| h.to_string()).collect();
        dict.set_item("proved", proved)?;
        Ok(dict.into_any())
    }

    fn info<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let info = kernel_call(py, &self.tx, |k| SyncBackend::info(k))?;
        let dict = pyo3::types::PyDict::new(py);
        dict.set_item("kind", info.kind)?;
        dict.set_item("target", info.target)?;
        Ok(dict.into_any())
    }
}

/// Create an in-memory backend (no networking).
/// Optionally accepts a Store to use as the backing store.
#[pyfunction]
#[pyo3(signature = (store=None))]
pub fn local(store: Option<&Store>) -> PyResult<Backend> {
    let kernel = match store {
        Some(s) => Kernel::with_store(s.blob_store()),
        None => Kernel::new(),
    }
    .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    let tx = spawn_kernel_worker(kernel);
    Ok(Backend { tx })
}

/// Create a SQLite-backed backend at the given path.
#[pyfunction]
pub fn local_persistent(path: &str) -> PyResult<Backend> {
    let store = covalence_store::SqliteStore::open(path)
        .map_err(|e| PyRuntimeError::new_err(format!("sqlite open: {e}")))?;
    let kernel = Kernel::with_store(BlobStore::new(store))
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    let tx = spawn_kernel_worker(kernel);
    Ok(Backend { tx })
}
