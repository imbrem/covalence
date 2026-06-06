//! Integration tests for the `git-*` REPL commands.
#![cfg(feature = "cogit")]

use std::fs;
use std::path::PathBuf;

use covalence_hash::O256;
use covalence_repl::Session;
use covalence_shell::Kernel;

fn tmp_db(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "cov_repl_cogit_{name}_{}_{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir.join("git.db")
}

fn session() -> Session {
    Session::new(Box::new(Kernel::new()), false, false)
}

#[test]
fn store_blob_then_resolve_and_reverse_round_trip() {
    let db = tmp_db("roundtrip");
    let mut s = session();
    let db_str = db.display().to_string();

    // Open the store.
    let out = s.eval(&format!("\"{db_str}\" git-open"));
    assert!(out.contains("opened git store"), "got: {out}");

    // Register a blob; the result on the stack is the git OID hex string.
    let payload = "hello cogit";
    let oid_blob_out = s.eval(&format!("\"{payload}\" git-store-blob"));
    let oid_hex = oid_blob_out.trim_matches('"');
    assert_eq!(oid_hex.len(), 40, "expected SHA-1 hex, got: {oid_blob_out}");

    // Resolving the same OID hex yields the O256 of the payload.
    let resolved = s.eval(&format!("\"{oid_hex}\" git-resolve"));
    let expected = O256::blob(payload.as_bytes());
    assert_eq!(resolved.trim(), expected.to_string(), "got: {resolved}");

    // Reverse: O256 → OID.
    let reversed = s.eval(&format!("{expected} git-reverse"));
    assert_eq!(reversed.trim_matches('"'), oid_hex, "got: {reversed}");
}

#[test]
fn git_info_reports_counts() {
    let db = tmp_db("info");
    let mut s = session();
    let db_str = db.display().to_string();
    s.eval(&format!("\"{db_str}\" git-open"));

    let before = s.eval("git-info");
    assert!(before.contains("git objects:    0"), "got: {before}");

    s.eval("\"a\" git-store-blob");
    s.eval("\"b\" git-store-blob");
    let after = s.eval("git-info");
    assert!(after.contains("git objects:    2"), "got: {after}");
}

#[test]
fn commands_error_before_open() {
    let mut s = session();
    // `git-info` doesn't pop anything from the stack, so it hits the
    // "store not open" guard directly.
    let out = s.eval("git-info");
    assert!(
        out.to_lowercase().contains("git store not open"),
        "got: {out}"
    );
}

#[test]
fn git_close_drops_handle() {
    let db = tmp_db("close");
    let mut s = session();
    let db_str = db.display().to_string();
    s.eval(&format!("\"{db_str}\" git-open"));
    let closed = s.eval("git-close");
    assert!(closed.contains("closed git store"), "got: {closed}");
    // After close, subsequent commands error again.
    let out = s.eval("git-info");
    assert!(out.to_lowercase().contains("git store not open"), "got: {out}");
}

#[test]
fn resolve_unknown_oid_errors() {
    let db = tmp_db("unknown");
    let mut s = session();
    let db_str = db.display().to_string();
    s.eval(&format!("\"{db_str}\" git-open"));
    let out = s.eval("\"0000000000000000000000000000000000000000\" git-resolve");
    assert!(out.to_lowercase().contains("not resolvable"), "got: {out}");
}
