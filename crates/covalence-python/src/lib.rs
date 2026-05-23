use std::sync::Mutex;

use pyo3::exceptions::{PyRuntimeError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

use covalence_hash::{Blake3Ctx, HashCtx, Sha256};
use covalence_kernel::{Kernel, SyncBackend};
use covalence_store::BlobStore;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse_hash(obj: &Bound<'_, PyAny>) -> PyResult<covalence_hash::O256> {
    if let Ok(o) = obj.extract::<PyRef<O256>>() {
        return Ok(o.0);
    }
    if let Ok(hex) = obj.extract::<String>() {
        return covalence_hash::O256::from_hex(&hex)
            .ok_or_else(|| PyValueError::new_err("invalid hex hash (expected 64 hex chars)"));
    }
    Err(PyTypeError::new_err("expected O256 or hex string"))
}

// ---------------------------------------------------------------------------
// O256
// ---------------------------------------------------------------------------

/// 256-bit hash value. Also acts as a BLAKE3 keyed-hash key.
#[pyclass(from_py_object)]
#[derive(Clone)]
struct O256(covalence_hash::O256);

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

// ---------------------------------------------------------------------------
// GitObject
// ---------------------------------------------------------------------------

/// Git object hash (SHA-1 or SHA-256).
#[pyclass(from_py_object)]
#[derive(Clone)]
struct GitObject {
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
            return Err(PyValueError::new_err(
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

// ---------------------------------------------------------------------------
// Hasher (O256-producing)
// ---------------------------------------------------------------------------

enum HasherInner {
    Blake3,
    Blake3Keyed(covalence_hash::O256),
    Blake3Kdf(Blake3Ctx),
    Sha256,
}

/// Hashing strategy that produces O256 values.
#[pyclass]
struct Hasher {
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

// ---------------------------------------------------------------------------
// GitHasher
// ---------------------------------------------------------------------------

/// Git hashing strategy that produces GitObject values.
#[pyclass]
struct GitHasher {
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

// ---------------------------------------------------------------------------
// Backend
// ---------------------------------------------------------------------------

/// Covalence backend: content store + WASM engine.
#[pyclass]
struct Backend {
    inner: Mutex<Box<dyn SyncBackend>>,
}

#[pymethods]
impl Backend {
    fn store_blob(&self, data: &[u8]) -> PyResult<O256> {
        let backend = self.inner.lock().unwrap();
        backend
            .store_blob(data)
            .map(O256)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn store_str(&self, text: &str) -> PyResult<O256> {
        self.store_blob(text.as_bytes())
    }

    fn get_blob<'py>(
        &self,
        py: Python<'py>,
        hash: &Bound<'py, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let h = parse_hash(hash)?;
        let backend = self.inner.lock().unwrap();
        match backend
            .get_blob(&h)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?
        {
            Some(data) => Ok(PyBytes::new(py, &data).into_any()),
            None => Ok(py.None().into_bound(py)),
        }
    }

    fn has_blob(&self, hash: &Bound<'_, PyAny>) -> PyResult<bool> {
        let h = parse_hash(hash)?;
        let backend = self.inner.lock().unwrap();
        backend
            .has_blob(&h)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn blob_count(&self) -> PyResult<Option<usize>> {
        let backend = self.inner.lock().unwrap();
        backend
            .blob_count()
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn compile_wat(&self, wat: &str) -> PyResult<O256> {
        let wasm =
            covalence_wasm::compile_wat(wat).map_err(|e| PyValueError::new_err(e.to_string()))?;
        let backend = self.inner.lock().unwrap();
        backend
            .store_blob(&wasm)
            .map(O256)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    fn decide<'py>(
        &self,
        hash: &Bound<'py, PyAny>,
        py: Python<'py>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let h = parse_hash(hash)?;
        let backend = self.inner.lock().unwrap();
        let output = backend
            .decide(&h)
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        let dict = pyo3::types::PyDict::new(py);
        dict.set_item("decision", output.decision.to_string())?;
        let proved: Vec<String> = output.proved.iter().map(|h| h.to_string()).collect();
        dict.set_item("proved", proved)?;
        Ok(dict.into_any())
    }

    fn info<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let backend = self.inner.lock().unwrap();
        let info = backend.info();
        let dict = pyo3::types::PyDict::new(py);
        dict.set_item("kind", info.kind)?;
        dict.set_item("target", info.target)?;
        Ok(dict.into_any())
    }
}

// ---------------------------------------------------------------------------
// Session
// ---------------------------------------------------------------------------

/// REPL session for evaluating S-expression commands.
#[pyclass]
struct Session {
    inner: Mutex<covalence_repl::Session>,
}

#[pymethods]
impl Session {
    fn eval(&self, input: &str) -> String {
        let mut session = self.inner.lock().unwrap();
        session.eval(input)
    }
}

// ---------------------------------------------------------------------------
// Server
// ---------------------------------------------------------------------------

/// Background embedded HTTP server.
#[pyclass]
struct Server {
    port: u16,
    shutdown: Option<tokio::sync::oneshot::Sender<()>>,
    handle: Option<std::thread::JoinHandle<()>>,
}

#[pymethods]
impl Server {
    #[getter]
    fn port(&self) -> u16 {
        self.port
    }

    #[getter]
    fn url(&self) -> String {
        format!("http://127.0.0.1:{}", self.port)
    }

    fn stop(&mut self) -> PyResult<()> {
        if let Some(tx) = self.shutdown.take() {
            let _ = tx.send(());
        }
        if let Some(handle) = self.handle.take() {
            handle
                .join()
                .map_err(|_| PyRuntimeError::new_err("server thread panicked"))?;
        }
        Ok(())
    }

    fn __enter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __exit__(
        &mut self,
        _exc_type: Option<&Bound<'_, PyAny>>,
        _exc_val: Option<&Bound<'_, PyAny>>,
        _exc_tb: Option<&Bound<'_, PyAny>>,
    ) -> PyResult<bool> {
        self.stop()?;
        Ok(false)
    }
}

// ---------------------------------------------------------------------------
// Module functions
// ---------------------------------------------------------------------------

/// Create an in-memory backend (no networking).
#[pyfunction]
fn local() -> PyResult<Backend> {
    let kernel = Kernel::new().map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    Ok(Backend {
        inner: Mutex::new(Box::new(kernel)),
    })
}

/// Create a SQLite-backed backend at the given path.
#[pyfunction]
fn local_persistent(path: &str) -> PyResult<Backend> {
    let store = covalence_store::SqliteStore::open(path)
        .map_err(|e| PyRuntimeError::new_err(format!("sqlite open: {e}")))?;
    let kernel = Kernel::with_store(BlobStore::new(store))
        .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    Ok(Backend {
        inner: Mutex::new(Box::new(kernel)),
    })
}

/// Create a REPL session backed by a fresh in-memory kernel.
#[pyfunction]
fn session_local() -> PyResult<Session> {
    let kernel = Kernel::new().map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    let repl = covalence_repl::Session::new(Box::new(kernel), true, false);
    Ok(Session {
        inner: Mutex::new(repl),
    })
}

/// Start an embedded HTTP server in a background thread.
#[pyfunction]
#[pyo3(signature = (port=0, store=None))]
fn serve(port: u16, store: Option<&str>) -> PyResult<Server> {
    let blob_store = match store {
        Some(path) => {
            let s = covalence_store::SqliteStore::open(path)
                .map_err(|e| PyRuntimeError::new_err(format!("sqlite open: {e}")))?;
            BlobStore::new(s)
        }
        None => BlobStore::new(covalence_store::SharedMemoryStore::new()),
    };

    let kernel =
        Kernel::with_store(blob_store).map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

    let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel::<()>();
    let (port_tx, port_rx) = std::sync::mpsc::channel::<Result<u16, String>>();

    let handle = std::thread::spawn(move || {
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("tokio runtime");

        rt.block_on(async move {
            let addr = format!("127.0.0.1:{port}");
            let tcp = match tokio::net::TcpListener::bind(&addr).await {
                Ok(l) => l,
                Err(e) => {
                    let _ = port_tx.send(Err(format!("bind {addr}: {e}")));
                    return;
                }
            };
            let actual_port = tcp.local_addr().unwrap().port();
            let _ = port_tx.send(Ok(actual_port));

            let state = covalence_serve::AppState {
                version: "python",
                target: "covalence-python",
                started: std::time::Instant::now(),
                kernel,
            };

            let app = build_api_router(state);

            tokio::select! {
                r = axum::serve(tcp, app).into_future() => {
                    if let Err(e) = r {
                        eprintln!("server error: {e}");
                    }
                }
                _ = async {
                    shutdown_rx.await.ok();
                } => {}
            }
        });
    });

    let actual_port = port_rx
        .recv()
        .map_err(|_| PyRuntimeError::new_err("server thread died before binding"))?
        .map_err(|e| PyRuntimeError::new_err(e))?;

    Ok(Server {
        port: actual_port,
        shutdown: Some(shutdown_tx),
        handle: Some(handle),
    })
}

/// Build a minimal API-only router (no static files, no service discovery).
fn build_api_router(state: covalence_serve::AppState) -> axum::Router {
    covalence_serve::build_router(state, true)
}

// Hasher constructors

/// Plain BLAKE3 hasher.
#[pyfunction]
fn blake3() -> Hasher {
    Hasher {
        inner: HasherInner::Blake3,
    }
}

/// BLAKE3 keyed hasher.
#[pyfunction]
fn blake3_keyed(key: &O256) -> Hasher {
    Hasher {
        inner: HasherInner::Blake3Keyed(key.0),
    }
}

/// BLAKE3 key-derivation hasher.
#[pyfunction]
fn blake3_kdf(ctx: &str) -> Hasher {
    Hasher {
        inner: HasherInner::Blake3Kdf(Blake3Ctx::new(ctx)),
    }
}

/// SHA-256 hasher.
#[pyfunction]
fn sha256() -> Hasher {
    Hasher {
        inner: HasherInner::Sha256,
    }
}

/// Get a hasher by name.
#[pyfunction]
fn hasher(name: &str) -> PyResult<Hasher> {
    match name {
        "blake3" => Ok(blake3()),
        "sha256" => Ok(sha256()),
        _ => Err(PyValueError::new_err(format!("unknown hasher: {name}"))),
    }
}

/// Git SHA-1 blob/tree hasher.
#[pyfunction]
fn git_sha1() -> GitHasher {
    GitHasher {
        kind: covalence_hash::gix_hash::Kind::Sha1,
    }
}

/// Git SHA-256 blob/tree hasher.
#[pyfunction]
fn git_sha256() -> GitHasher {
    GitHasher {
        kind: covalence_hash::gix_hash::Kind::Sha256,
    }
}

// ---------------------------------------------------------------------------
// Python module
// ---------------------------------------------------------------------------

#[pymodule]
fn covalence(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<O256>()?;
    m.add_class::<GitObject>()?;
    m.add_class::<Hasher>()?;
    m.add_class::<GitHasher>()?;
    m.add_class::<Backend>()?;
    m.add_class::<Session>()?;
    m.add_class::<Server>()?;
    m.add_function(wrap_pyfunction!(local, m)?)?;
    m.add_function(wrap_pyfunction!(local_persistent, m)?)?;
    m.add_function(wrap_pyfunction!(session_local, m)?)?;
    m.add_function(wrap_pyfunction!(serve, m)?)?;
    m.add_function(wrap_pyfunction!(blake3, m)?)?;
    m.add_function(wrap_pyfunction!(blake3_keyed, m)?)?;
    m.add_function(wrap_pyfunction!(blake3_kdf, m)?)?;
    m.add_function(wrap_pyfunction!(sha256, m)?)?;
    m.add_function(wrap_pyfunction!(hasher, m)?)?;
    m.add_function(wrap_pyfunction!(git_sha1, m)?)?;
    m.add_function(wrap_pyfunction!(git_sha256, m)?)?;
    Ok(())
}
