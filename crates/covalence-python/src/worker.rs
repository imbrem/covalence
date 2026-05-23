use std::sync::mpsc;
use std::thread;

use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;

use covalence_kernel::Kernel;

/// Type-erased task: a closure that runs on the worker's owned state.
pub type KernelTask = Box<dyn FnOnce(&Kernel) + Send>;
pub type SessionTask = Box<dyn FnOnce(&mut covalence_repl::Session) + Send>;

/// Send a closure to a kernel worker, release the GIL, block until it replies.
pub fn kernel_call<F, R>(py: Python<'_>, tx: &mpsc::Sender<KernelTask>, f: F) -> PyResult<R>
where
    F: FnOnce(&Kernel) -> R + Send + 'static,
    R: Send + 'static,
{
    let (reply_tx, reply_rx) = mpsc::sync_channel(1);
    let task: KernelTask = Box::new(move |kernel| {
        let _ = reply_tx.send(f(kernel));
    });
    tx.send(task)
        .map_err(|_| PyRuntimeError::new_err("backend thread stopped"))?;
    py.detach(move || {
        reply_rx
            .recv()
            .map_err(|_| PyRuntimeError::new_err("backend thread stopped"))
    })
}

/// Send a closure to a session worker, release the GIL, block until it replies.
pub fn session_call<F, R>(py: Python<'_>, tx: &mpsc::Sender<SessionTask>, f: F) -> PyResult<R>
where
    F: FnOnce(&mut covalence_repl::Session) -> R + Send + 'static,
    R: Send + 'static,
{
    let (reply_tx, reply_rx) = mpsc::sync_channel(1);
    let task: SessionTask = Box::new(move |session| {
        let _ = reply_tx.send(f(session));
    });
    tx.send(task)
        .map_err(|_| PyRuntimeError::new_err("session thread stopped"))?;
    py.detach(move || {
        reply_rx
            .recv()
            .map_err(|_| PyRuntimeError::new_err("session thread stopped"))
    })
}

/// Spawn a background thread that processes kernel tasks.
pub fn spawn_kernel_worker(kernel: Kernel) -> mpsc::Sender<KernelTask> {
    let (tx, rx) = mpsc::channel::<KernelTask>();
    thread::spawn(move || {
        while let Ok(task) = rx.recv() {
            task(&kernel);
        }
    });
    tx
}

/// Spawn a background thread that processes session tasks.
pub fn spawn_session_worker(session: covalence_repl::Session) -> mpsc::Sender<SessionTask> {
    let (tx, rx) = mpsc::channel::<SessionTask>();
    thread::spawn(move || {
        let mut session = session;
        while let Ok(task) = rx.recv() {
            task(&mut session);
        }
    });
    tx
}
