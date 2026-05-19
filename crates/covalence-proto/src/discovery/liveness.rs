use std::path::Path;

use super::descriptor::ServiceDescriptor;

/// Check if a process with the given PID is alive.
pub fn pid_alive(pid: u32) -> bool {
    use nix::sys::signal;
    use nix::unistd::Pid;
    signal::kill(Pid::from_raw(pid as i32), None).is_ok()
}

/// Clean up a stale descriptor (dead PID). Removes the descriptor file and socket.
pub fn cleanup_stale(descriptor_path: &Path, descriptor: &ServiceDescriptor) {
    tracing::debug!("cleaning up stale descriptor: {}", descriptor.id);
    let _ = std::fs::remove_file(descriptor_path);
    if let Some(socket) = &descriptor.socket {
        let _ = std::fs::remove_file(socket);
    }
}
