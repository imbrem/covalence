use std::sync::mpsc;

use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;

use covalence_kernel::Kernel;

use crate::worker::{SessionTask, session_call, spawn_session_worker};

/// REPL session for evaluating S-expression commands, on a background thread.
#[pyclass]
pub struct Session {
    tx: mpsc::Sender<SessionTask>,
}

#[pymethods]
impl Session {
    fn eval(&self, py: Python<'_>, input: &str) -> PyResult<String> {
        let input = input.to_string();
        session_call(py, &self.tx, move |s| s.eval(&input))
    }
}

/// Create a REPL session backed by a fresh in-memory kernel.
#[pyfunction]
pub fn session_local() -> PyResult<Session> {
    let kernel = Kernel::new().map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
    let repl = covalence_repl::Session::new(Box::new(kernel), true, false);
    let tx = spawn_session_worker(repl);
    Ok(Session { tx })
}
