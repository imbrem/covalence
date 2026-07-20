#![cfg(feature = "acl2")]

use std::fs;
use std::process::{Command, Output};

use tempfile::tempdir;

fn cov(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_cov"))
        .args(args)
        .output()
        .expect("run cov")
}

fn write_green_book(root: &std::path::Path) {
    fs::write(
        root.join("green.lisp"),
        "(in-package \"ACL2\")\n(defthm truth (equal 1 1))\n",
    )
    .unwrap();
}

#[test]
fn progress_is_observational_but_check_is_fail_closed() {
    let temp = tempdir().unwrap();
    write_green_book(temp.path());
    let root = temp.path().to_str().unwrap();

    let progress = cov(&["acl2", "progress", "--inventory", root, "pin", "green"]);
    assert!(progress.status.success(), "{progress:?}");
    let stdout = String::from_utf8(progress.stdout).unwrap();
    assert!(stdout.starts_with("acl2-progress-v1\n"));
    assert!(stdout.contains("mode\tinventory\n"));

    let rejected = cov(&[
        "acl2",
        "check",
        "--inventory",
        "--require",
        "source-green",
        root,
        "pin",
        "green",
    ]);
    assert_eq!(rejected.status.code(), Some(1), "{rejected:?}");
    assert!(
        String::from_utf8_lossy(&rejected.stderr).contains("gate.inventory-mode"),
        "{rejected:?}"
    );

    let missing = cov(&["acl2", "progress", root, "pin", "missing"]);
    assert!(missing.status.success(), "{missing:?}");
    assert!(String::from_utf8_lossy(&missing.stdout).contains("load-error"));
}

#[test]
fn source_green_and_exact_manifest_are_automation_gates() {
    let temp = tempdir().unwrap();
    write_green_book(temp.path());
    let root = temp.path().to_str().unwrap();

    let manifest = cov(&["acl2", "progress", "--manifest", root, "pin", "green"]);
    assert!(manifest.status.success(), "{manifest:?}");
    assert!(manifest.stdout.starts_with(b"acl2-corpus-manifest-v1\n"));
    let expected = temp.path().join("expected.tsv");
    fs::write(&expected, &manifest.stdout).unwrap();
    let expected = expected.to_str().unwrap();

    let accepted = cov(&[
        "acl2",
        "check",
        "--expected-manifest",
        expected,
        root,
        "pin",
        "green",
    ]);
    assert!(accepted.status.success(), "{accepted:?}");

    fs::write(
        temp.path().join("green.lisp"),
        "(in-package \"ACL2\")\n(defthm truth (equal 2 2))\n",
    )
    .unwrap();
    let drifted = cov(&[
        "acl2",
        "check",
        "--expected-manifest",
        expected,
        root,
        "pin",
        "green",
    ]);
    assert_eq!(drifted.status.code(), Some(1), "{drifted:?}");
    assert!(
        String::from_utf8_lossy(&drifted.stderr).contains("manifest.mismatch"),
        "{drifted:?}"
    );
}
