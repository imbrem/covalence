use std::sync::mpsc;
use std::thread;

use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;

use covalence_shell::Kernel;
use covalence_store::BlobStore;

/// Background embedded HTTP server.
#[pyclass]
pub struct Server {
    port: u16,
    shutdown: Option<tokio::sync::oneshot::Sender<()>>,
    handle: Option<thread::JoinHandle<()>>,
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

/// Start an embedded HTTP server in a background thread.
#[pyfunction]
#[pyo3(signature = (port=0, store=None))]
pub fn serve(port: u16, store: Option<&str>) -> PyResult<Server> {
    let blob_store = match store {
        Some(path) => {
            let s = covalence_store::SqliteStore::open(path)
                .map_err(|e| PyRuntimeError::new_err(format!("sqlite open: {e}")))?;
            BlobStore::new(s)
        }
        None => BlobStore::new(covalence_store::SharedMemoryStore::new()),
    };

    let kernel = Kernel::with_store(blob_store);

    let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel::<()>();
    let (port_tx, port_rx) = mpsc::channel::<Result<u16, String>>();

    let handle = thread::spawn(move || {
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

            let tagged_store = covalence_serve::new_tagged_store();
            let object_store = covalence_store::GitTaggedObjectStore::new(tagged_store.clone());
            let state = covalence_serve::AppState {
                version: "python",
                target: "covalence-python",
                started: std::time::Instant::now(),
                kernel,
                tagged_store,
                object_store,
            };

            let app = covalence_serve::build_router(state, true);

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
