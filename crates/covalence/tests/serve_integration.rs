#![cfg(unix)]

use std::io::{Read, Write};
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
    let output = session.eval("status");
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

    let hash_output = session.eval(r#""hello world" store"#);
    // Hash should be 64 hex characters
    let hash = hash_output.trim();
    assert_eq!(hash.len(), 64, "expected 64-char hex hash, got: {hash}");
    assert!(
        hash.chars().all(|c| c.is_ascii_hexdigit()),
        "hash should be hex: {hash}"
    );

    // `read` pushes a blob; show formats it as "hello world" (with quotes)
    let read_output = session.eval(&format!("{hash} read print"));
    assert!(
        read_output.contains("hello world"),
        "read output should contain content: {read_output}"
    );
}

#[test]
fn repl_help_lists_commands() {
    let server = start_server();
    let mut session = server.session();
    let output = session.eval("help");
    for cmd in ["store", "read", "compile-wat", "decide", "status", "help"] {
        assert!(
            output.contains(cmd),
            "help should mention '{cmd}': {output}"
        );
    }
}

#[test]
fn repl_compile_wat_and_read_wat() {
    let server = start_server();
    let mut session = server.session();

    // Compile a minimal WAT module via compile-wat
    let hash_output = session.eval(r#""(module (func (export \"f\")))" compile-wat"#);
    let hash = hash_output.trim();
    assert_eq!(hash.len(), 64, "expected 64-char hex hash, got: {hash}");

    // Decompile back to WAT — read-wat pushes a blob, print it
    let wat_output = session.eval(&format!("{hash} read-wat print"));
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

    let hash1 = session.eval(r#""first" store"#).trim().to_string();
    let hash2 = session.eval(r#""second" store"#).trim().to_string();

    assert_ne!(
        hash1, hash2,
        "different content should produce different hashes"
    );

    let read1 = session.eval(&format!("{hash1} read print"));
    assert!(
        read1.contains("first"),
        "read should contain 'first': {read1}"
    );

    let read2 = session.eval(&format!("{hash2} read print"));
    assert!(
        read2.contains("second"),
        "read should contain 'second': {read2}"
    );
}

#[test]
fn repl_unknown_command_returns_error() {
    let server = start_server();
    let mut session = server.session();
    let output = session.eval("nonexistent");
    // Should contain an error indication
    let lower = output.to_lowercase();
    assert!(
        lower.contains("unbound") || lower.contains("error"),
        "unknown command should produce error: {output}"
    );
}

#[test]
fn repl_read_nonexistent_blob_returns_error() {
    let server = start_server();
    let mut session = server.session();
    let zero_hash = "0".repeat(64);
    let output = session.eval(&format!("{zero_hash} read"));
    let lower = output.to_lowercase();
    assert!(
        lower.contains("not found") || lower.contains("error"),
        "reading nonexistent blob should produce error: {output}"
    );
}

// ---------------------------------------------------------------------------
// Object info endpoint tests
// ---------------------------------------------------------------------------

/// Raw GET over Unix socket, returning (status_code, body_bytes).
fn unix_http_get(socket_path: &Path, path: &str) -> (u16, Vec<u8>) {
    let mut stream = UnixStream::connect(socket_path).expect("connect to socket");
    let request = format!("GET {path} HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n");
    stream.write_all(request.as_bytes()).expect("write request");

    let mut response = Vec::new();
    stream.read_to_end(&mut response).expect("read response");

    let header_end = response
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("find header end");
    let header_str = std::str::from_utf8(&response[..header_end]).expect("parse headers");
    let status_line = header_str.lines().next().expect("status line");
    let status: u16 = status_line
        .split_whitespace()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .expect("parse status code");
    let body = response[header_end + 4..].to_vec();
    (status, body)
}

#[test]
fn object_info_blob() {
    use std::io::{Read, Write};

    let server = start_server();

    // Store a blob via the object store API (not the kernel blob store)
    let data = b"hello info endpoint";
    let mut stream = UnixStream::connect(&server.socket_path).expect("connect");
    let request = format!(
        "POST /api/objects/blob HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/octet-stream\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        data.len()
    );
    stream.write_all(request.as_bytes()).expect("write");
    stream.write_all(data).expect("write body");
    let mut response = Vec::new();
    stream.read_to_end(&mut response).expect("read");
    let header_end = response
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("headers");
    let resp_body = &response[header_end + 4..];
    let resp_json: serde_json::Value =
        serde_json::from_slice(resp_body).expect("parse store response");
    let hash = resp_json["hash"].as_str().expect("hash field");

    let (status, body) = unix_http_get(&server.socket_path, &format!("/api/objects/info/{hash}"));
    assert_eq!(status, 200, "expected 200 OK");

    let json: serde_json::Value = serde_json::from_slice(&body).expect("parse JSON");
    assert_eq!(json["kind"], "blob");
    assert_eq!(json["size"], data.len());
}

#[test]
fn object_info_tree() {
    let server = start_server();
    let mut session = server.session();

    // Store a blob first, then build a tree referencing it
    let blob_hash = session.eval(r#""tree-child" store"#).trim().to_string();

    // Build a tree via the JSON API
    let tree_json = format!(r#"[{{"name":"file.txt","mode":"regular","hash":"{blob_hash}"}}]"#);
    let mut stream = UnixStream::connect(&server.socket_path).expect("connect");
    let request = format!(
        "POST /api/objects/tree/json HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
        tree_json.len(),
        tree_json
    );
    stream.write_all(request.as_bytes()).expect("write");
    let mut response = Vec::new();
    stream.read_to_end(&mut response).expect("read");
    let header_end = response
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("headers");
    let body = &response[header_end + 4..];
    let tree_resp: serde_json::Value = serde_json::from_slice(body).expect("parse tree response");
    let tree_hash = tree_resp["hash"].as_str().expect("tree hash");

    let (status, info_body) = unix_http_get(
        &server.socket_path,
        &format!("/api/objects/info/{tree_hash}"),
    );
    assert_eq!(status, 200, "expected 200 OK for tree info");

    let json: serde_json::Value = serde_json::from_slice(&info_body).expect("parse JSON");
    assert_eq!(json["kind"], "tree");
    assert!(json["size"].as_u64().unwrap() > 0);
}

#[test]
fn object_info_missing() {
    let server = start_server();
    let zero_hash = "0".repeat(64);
    let (status, _body) = unix_http_get(
        &server.socket_path,
        &format!("/api/objects/info/{zero_hash}"),
    );
    assert_eq!(status, 404, "expected 404 for nonexistent hash");
}

// ---------------------------------------------------------------------------
// REPL → viewer workflow tests
// ---------------------------------------------------------------------------

/// Store data via the REPL, then verify the viewer API can find and serve it.
#[test]
fn repl_store_then_view_info() {
    let server = start_server();
    let mut session = server.session();

    // Store via REPL — this goes to the kernel blob store
    let hash = session.eval(r#""hello viewer" store"#).trim().to_string();
    assert_eq!(hash.len(), 64);

    // The viewer info endpoint should find it (falls back to kernel store)
    let (status, body) = unix_http_get(&server.socket_path, &format!("/api/objects/info/{hash}"));
    assert_eq!(status, 200, "info should find REPL-stored blob");

    let json: serde_json::Value = serde_json::from_slice(&body).expect("parse JSON");
    assert_eq!(json["kind"], "blob");
    assert_eq!(json["size"], "hello viewer".len());
}

/// Store data via the REPL, then fetch the blob content through the object API.
#[test]
fn repl_store_then_view_blob_content() {
    let server = start_server();
    let mut session = server.session();

    let hash = session
        .eval(r#""blob viewer content" store"#)
        .trim()
        .to_string();

    // Fetch via the object blob endpoint (used by the viewer)
    let (status, body) = unix_http_get(&server.socket_path, &format!("/api/objects/blob/{hash}"));
    assert_eq!(status, 200, "object blob should find REPL-stored blob");
    assert_eq!(std::str::from_utf8(&body).unwrap(), "blob viewer content");
}

/// Full REPL workflow: store multiple items, verify each is viewable.
#[test]
fn repl_store_multiple_then_view_all() {
    let server = start_server();
    let mut session = server.session();

    let items = vec![
        ("first item", "blob"),
        ("second item", "blob"),
        ("third item", "blob"),
    ];

    let mut hashes = Vec::new();
    for (content, _kind) in &items {
        let hash = session
            .eval(&format!(r#""{content}" store"#))
            .trim()
            .to_string();
        assert_eq!(hash.len(), 64, "hash should be 64 hex chars");
        hashes.push(hash);
    }

    // All distinct
    for i in 0..hashes.len() {
        for j in (i + 1)..hashes.len() {
            assert_ne!(hashes[i], hashes[j], "different content = different hash");
        }
    }

    // All viewable via info endpoint
    for (i, hash) in hashes.iter().enumerate() {
        let (status, body) =
            unix_http_get(&server.socket_path, &format!("/api/objects/info/{hash}"));
        assert_eq!(status, 200, "item {i} should be viewable");

        let json: serde_json::Value = serde_json::from_slice(&body).expect("parse JSON");
        assert_eq!(json["kind"], "blob");
    }

    // All fetchable via blob endpoint
    for (i, hash) in hashes.iter().enumerate() {
        let (status, body) =
            unix_http_get(&server.socket_path, &format!("/api/objects/blob/{hash}"));
        assert_eq!(status, 200, "item {i} blob should be fetchable");

        let content = std::str::from_utf8(&body).unwrap();
        assert_eq!(content, items[i].0);
    }
}
