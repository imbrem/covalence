use covalence_repl::Session;
use covalence_shell::Kernel;

/// Create a Session backed by the given Kernel.
/// This is the server-side constructor used by API handlers and the WS REPL.
pub fn server_session(kernel: Kernel) -> Session {
    Session::new(Box::new(kernel), false, false)
}
