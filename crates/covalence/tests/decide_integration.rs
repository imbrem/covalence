#![cfg(unix)]

use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use tempfile::TempDir;

// ---------------------------------------------------------------------------
// Infrastructure
// ---------------------------------------------------------------------------

/// A running `cov serve --socket-only` process with a Unix socket.
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

fn start_server() -> TestServer {
    let temp = TempDir::new().expect("create temp dir");
    for sub in ["runtime", "data", "config", "home"] {
        std::fs::create_dir_all(temp.path().join(sub)).expect("create subdir");
    }

    let bin = env!("CARGO_BIN_EXE_cov");
    let child = Command::new(bin)
        .args(["serve", "--socket-only"])
        .env("XDG_RUNTIME_DIR", temp.path().join("runtime"))
        .env("XDG_DATA_HOME", temp.path().join("data"))
        .env("XDG_CONFIG_HOME", temp.path().join("config"))
        .env("HOME", temp.path().join("home"))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn cov serve");

    let socket_path = wait_for_socket(&temp.path().join("runtime"));

    TestServer {
        child,
        socket_path,
        _temp: temp,
    }
}

/// Poll for a `.sock` file under `{runtime_dir}/covalence/sockets/` and verify
/// it is connectable. Panics after 10 seconds.
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
                    if UnixStream::connect(&path).is_ok() {
                        return path;
                    }
                }
            }
        }

        std::thread::sleep(Duration::from_millis(50));
    }
}

/// Run `cov decide` with isolated XDG dirs.
/// If `connect` is Some, passes `--connect <socket_path>`; otherwise `--standalone`.
fn cov_decide(connect: Option<&Path>, args: &[&str]) -> Output {
    let temp = TempDir::new().expect("create temp dir");
    let bin = env!("CARGO_BIN_EXE_cov");
    let mut cmd = Command::new(bin);
    cmd.arg("decide")
        .env("XDG_RUNTIME_DIR", temp.path().join("runtime"))
        .env("XDG_DATA_HOME", temp.path().join("data"))
        .env("HOME", temp.path().join("home"));

    match connect {
        Some(socket) => {
            cmd.args(["--connect", socket.to_str().unwrap()]);
        }
        None => {
            cmd.arg("--standalone");
        }
    }

    cmd.args(args).output().expect("spawn cov decide")
}

fn write_wat(dir: &Path, name: &str, content: &str) -> PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, content).expect("write WAT file");
    path
}

fn compile_wat(source: &str) -> Vec<u8> {
    wat::parse_str(source).expect("compile WAT").to_vec()
}

const TRUE_WAT: &str = r#"(component
    (import "attest" (func $attest))
    (core module $m
        (import "env" "attest" (func $attest))
        (func $start (call $attest))
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
        ))
    ))
)"#;

const FALSE_WAT: &str = "(component)";

const UNKNOWN_WAT: &str = r#"(component
    (import "attest" (func $attest))
)"#;

// ---------------------------------------------------------------------------
// Macro: generate standalone + server variants for each behavioral test
// ---------------------------------------------------------------------------

macro_rules! decide_tests {
    ($(fn $name:ident($connect:ident) $body:block)*) => {
        $(
            mod $name {
                use super::*;

                #[test]
                fn standalone() {
                    let $connect: Option<&Path> = None;
                    $body
                }

                #[test]
                fn with_server() {
                    let server = start_server();
                    let $connect: Option<&Path> = Some(&server.socket_path);
                    $body
                }
            }
        )*
    };
}

// ---------------------------------------------------------------------------
// Behavioral tests (run both standalone and against a server)
// ---------------------------------------------------------------------------

decide_tests! {
    fn true_proposition(connect) {
        let tmp = TempDir::new().unwrap();
        let path = write_wat(tmp.path(), "true.wat", TRUE_WAT);
        let out = cov_decide(connect, &[path.to_str().unwrap()]);

        assert!(out.status.success(), "exit code: {:?}", out.status);
        let stdout = String::from_utf8_lossy(&out.stdout);
        let line = stdout.trim();
        assert!(line.ends_with(" true"), "expected '{{hash}} true', got: {line}");
        assert_eq!(line.split_whitespace().count(), 2);
        let hash = line.split_whitespace().next().unwrap();
        assert_eq!(hash.len(), 64, "hash should be 64 hex chars: {hash}");
    }

    fn false_proposition(connect) {
        let tmp = TempDir::new().unwrap();
        let path = write_wat(tmp.path(), "false.wat", FALSE_WAT);
        let out = cov_decide(connect, &[path.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        let line = stdout.trim();
        assert!(line.ends_with(" false"), "expected '{{hash}} false', got: {line}");
    }

    fn unknown_proposition_prints_nothing(connect) {
        let tmp = TempDir::new().unwrap();
        let path = write_wat(tmp.path(), "unknown.wat", UNKNOWN_WAT);
        let out = cov_decide(connect, &[path.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        let line = stdout.trim();
        assert!(line.ends_with(" unknown"), "expected '{{hash}} unknown', got: {line}");
    }

    fn multiple_files(connect) {
        let tmp = TempDir::new().unwrap();
        let t = write_wat(tmp.path(), "t.wat", TRUE_WAT);
        let f = write_wat(tmp.path(), "f.wat", FALSE_WAT);
        let u = write_wat(tmp.path(), "u.wat", UNKNOWN_WAT);

        let out = cov_decide(connect, &[
            t.to_str().unwrap(),
            f.to_str().unwrap(),
            u.to_str().unwrap(),
        ]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines.len(), 3, "expected 3 lines (true + false + unknown), got: {stdout}");
        assert!(lines[0].ends_with(" true"));
        assert!(lines[1].ends_with(" false"));
        assert!(lines[2].ends_with(" unknown"));
    }

    fn compiled_wasm_file(connect) {
        let tmp = TempDir::new().unwrap();
        let wasm_bytes = compile_wat(TRUE_WAT);
        let path = tmp.path().join("prop.wasm");
        std::fs::write(&path, &wasm_bytes).unwrap();

        let out = cov_decide(connect, &[path.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.trim().ends_with(" true"));
    }

    fn force_format_wat(connect) {
        let tmp = TempDir::new().unwrap();
        let path = tmp.path().join("prop.txt");
        std::fs::write(&path, TRUE_WAT).unwrap();

        let out = cov_decide(connect, &["--format", "wat", path.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.trim().ends_with(" true"));
    }

    fn force_format_wasm(connect) {
        let tmp = TempDir::new().unwrap();
        let wasm_bytes = compile_wat(FALSE_WAT);
        let path = tmp.path().join("prop.bin");
        std::fs::write(&path, &wasm_bytes).unwrap();

        let out = cov_decide(connect, &["--format", "wasm", path.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.trim().ends_with(" false"));
    }

    fn auto_detects_wasm_by_magic_bytes(connect) {
        let tmp = TempDir::new().unwrap();
        let wasm_bytes = compile_wat(TRUE_WAT);
        let path = tmp.path().join("prop");
        std::fs::write(&path, &wasm_bytes).unwrap();

        let out = cov_decide(connect, &[path.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.trim().ends_with(" true"));
    }

    fn same_content_produces_same_hash(connect) {
        let tmp = TempDir::new().unwrap();
        let a = write_wat(tmp.path(), "a.wat", TRUE_WAT);
        let b = write_wat(tmp.path(), "b.wat", TRUE_WAT);

        let out = cov_decide(connect, &[a.to_str().unwrap(), b.to_str().unwrap()]);

        assert!(out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        let lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(lines.len(), 2);
        let hash_a = lines[0].split_whitespace().next().unwrap();
        let hash_b = lines[1].split_whitespace().next().unwrap();
        assert_eq!(hash_a, hash_b, "identical WAT should produce the same hash");
    }

    fn stats_flag_prints_timing(connect) {
        let tmp = TempDir::new().unwrap();
        let path = write_wat(tmp.path(), "t.wat", TRUE_WAT);

        let out = cov_decide(connect, &["--stats", path.to_str().unwrap()]);

        assert!(out.status.success());
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(stderr.contains("decided in"), "stderr should contain timing: {stderr}");
        assert!(stderr.contains("total:"), "stderr should contain total: {stderr}");
    }

    fn no_stats_flag_stderr_is_quiet(connect) {
        let tmp = TempDir::new().unwrap();
        let path = write_wat(tmp.path(), "t.wat", TRUE_WAT);

        let out = cov_decide(connect, &[path.to_str().unwrap()]);

        assert!(out.status.success());
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(!stderr.contains("decided in"), "stderr should be quiet without --stats: {stderr}");
    }
}

// ---------------------------------------------------------------------------
// Error cases (standalone only — these don't exercise the backend)
// ---------------------------------------------------------------------------

#[test]
fn error_no_files() {
    let out = cov_decide(None, &[]);
    assert!(!out.status.success(), "should fail with no input files");
}

#[test]
fn error_nonexistent_file() {
    let out = cov_decide(None, &["/tmp/nonexistent_cov_test_file.wat"]);
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("read") || stderr.contains("No such file"),
        "should mention read error: {stderr}"
    );
}

#[test]
fn error_invalid_wat() {
    let tmp = TempDir::new().unwrap();
    let path = write_wat(tmp.path(), "bad.wat", "(component (invalid_syntax");
    let out = cov_decide(None, &[path.to_str().unwrap()]);
    assert!(!out.status.success());
}
