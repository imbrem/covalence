#![cfg(unix)]

use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

use covalence_client::SyncHttpBackend;
use covalence_kernel::SyncBackend;
use covalence_repl::Session;
use tempfile::TempDir;

/// RAII wrapper around a `cov serve --socket-only` child process.
/// Kills the server and cleans up the temp dir on drop.
struct TestServer {
    child: Child,
    socket_path: PathBuf,
    _temp: TempDir,
}

impl Drop for TestServer {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl TestServer {
    fn backend(&self) -> SyncHttpBackend {
        SyncHttpBackend::unix(self.socket_path.display().to_string())
    }

    fn session(&self) -> Session {
        Session::new(Box::new(self.backend()), false, false)
    }
}

/// Spawn `cov serve --socket-only` with fully isolated XDG dirs.
fn start_server() -> TestServer {
    let temp = TempDir::new().expect("create temp dir");

    let runtime = temp.path().join("runtime");
    let data = temp.path().join("data");
    let config = temp.path().join("config");
    let home = temp.path().join("home");

    for dir in [&runtime, &data, &config, &home] {
        std::fs::create_dir_all(dir).expect("create subdir");
    }

    let bin = env!("CARGO_BIN_EXE_cov");
    let child = Command::new(bin)
        .args(["serve", "--socket-only"])
        .env("XDG_RUNTIME_DIR", &runtime)
        .env("XDG_DATA_HOME", &data)
        .env("XDG_CONFIG_HOME", &config)
        .env("HOME", &home)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn cov serve");

    let socket_path = wait_for_socket(&runtime);

    TestServer {
        child,
        socket_path,
        _temp: temp,
    }
}

/// Poll for a `.sock` file under `{runtime_dir}/covalence/sockets/` and verify
/// it is connectable. Panics after 10 seconds with diagnostics.
fn wait_for_socket(runtime_dir: &Path) -> PathBuf {
    let sockets_dir = runtime_dir.join("covalence").join("sockets");
    let deadline = Instant::now() + Duration::from_secs(10);

    loop {
        if Instant::now() > deadline {
            panic!("timed out waiting for socket in {}", sockets_dir.display());
        }

        if let Ok(entries) = std::fs::read_dir(&sockets_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) == Some("sock") {
                    // Verify the socket is connectable
                    if UnixStream::connect(&path).is_ok() {
                        return path;
                    }
                }
            }
        }

        std::thread::sleep(Duration::from_millis(50));
    }
}

// ---------------------------------------------------------------------------
// Test cases
// ---------------------------------------------------------------------------

#[test]
fn server_starts_and_creates_socket() {
    let server = start_server();
    assert!(server.socket_path.exists(), "socket file should exist");
}

#[test]
fn repl_status_shows_http_backend() {
    let server = start_server();
    let mut session = server.session();
    let output = session.eval("(status)");
    assert!(
        output.contains("http"),
        "status should mention http backend: {output}"
    );
    assert!(
        output.contains("unix:"),
        "status should mention unix socket: {output}"
    );
}

#[test]
fn repl_store_and_read_roundtrip() {
    let server = start_server();
    let mut session = server.session();

    let hash_output = session.eval(r#"(store "hello world")"#);
    // Hash should be 64 hex characters
    let hash = hash_output.trim();
    assert_eq!(hash.len(), 64, "expected 64-char hex hash, got: {hash}");
    assert!(
        hash.chars().all(|c| c.is_ascii_hexdigit()),
        "hash should be hex: {hash}"
    );

    let read_output = session.eval(&format!("(read {hash})"));
    assert_eq!(read_output.trim(), "hello world");
}

#[test]
fn repl_help_lists_commands() {
    let server = start_server();
    let mut session = server.session();
    let output = session.eval("(help)");
    for cmd in [
        "store",
        "read",
        "module",
        "component",
        "decide",
        "status",
        "help",
    ] {
        assert!(
            output.contains(cmd),
            "help should mention '{cmd}': {output}"
        );
    }
}

#[test]
fn repl_module_compile_and_read_wat() {
    let server = start_server();
    let mut session = server.session();

    // Compile a minimal WAT module
    let hash_output = session.eval(r#"(module (func (export "f")))"#);
    let hash = hash_output.trim();
    assert_eq!(hash.len(), 64, "expected 64-char hex hash, got: {hash}");

    // Decompile back to WAT
    let wat_output = session.eval(&format!("(read-wat {hash})"));
    assert!(
        wat_output.contains("module"),
        "WAT output should contain 'module': {wat_output}"
    );
    assert!(
        wat_output.contains("func"),
        "WAT output should contain 'func': {wat_output}"
    );
}

#[test]
fn client_store_get_has_blob() {
    let server = start_server();
    let backend = server.backend();

    let data = b"integration test blob";
    let hash = backend.store_blob(data).expect("store_blob");

    let got = backend.get_blob(&hash).expect("get_blob");
    assert_eq!(got, Some(data.to_vec()));

    let exists = backend.has_blob(&hash).expect("has_blob");
    assert!(exists, "has_blob should return true for stored blob");
}

#[test]
fn client_get_missing_blob_returns_none() {
    let server = start_server();
    let backend = server.backend();

    let zero_hash = covalence_hash::O256::from_hex(&"0".repeat(64)).expect("valid zero hash");
    let result = backend.get_blob(&zero_hash).expect("get_blob");
    assert_eq!(result, None, "missing blob should return None");
}

#[test]
fn server_state_persists_across_requests() {
    let server = start_server();
    let mut session = server.session();

    let hash1 = session.eval(r#"(store "first")"#).trim().to_string();
    let hash2 = session.eval(r#"(store "second")"#).trim().to_string();

    assert_ne!(
        hash1, hash2,
        "different content should produce different hashes"
    );

    let read1 = session.eval(&format!("(read {hash1})"));
    assert_eq!(read1.trim(), "first");

    let read2 = session.eval(&format!("(read {hash2})"));
    assert_eq!(read2.trim(), "second");
}

#[test]
fn repl_unknown_command_returns_error() {
    let server = start_server();
    let mut session = server.session();
    let output = session.eval("(nonexistent)");
    // Should contain an error indication
    let lower = output.to_lowercase();
    assert!(
        lower.contains("unknown") || lower.contains("error") || lower.contains("unrecognized"),
        "unknown command should produce error: {output}"
    );
}

#[test]
fn repl_read_nonexistent_blob_returns_error() {
    let server = start_server();
    let mut session = server.session();
    let zero_hash = "0".repeat(64);
    let output = session.eval(&format!("(read {zero_hash})"));
    let lower = output.to_lowercase();
    assert!(
        lower.contains("not found") || lower.contains("error"),
        "reading nonexistent blob should produce error: {output}"
    );
}
