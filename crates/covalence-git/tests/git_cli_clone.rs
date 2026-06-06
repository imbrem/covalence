//! End-to-end integration tests for `clone_into` against repositories built by
//! the real `git` CLI. Each test:
//!
//! 1. Probes that `git` is on PATH and skips otherwise (so CI without git
//!    doesn't fail).
//! 2. Initializes a repository, runs a sequence of porcelain commands to
//!    populate it, then drives `clone_into` against it.
//! 3. Asserts that the resulting `GitStore` and `CloneResult` reflect what
//!    `git` actually wrote.

#![cfg(feature = "clone")]

use std::path::{Path, PathBuf};
use std::process::Command;

use covalence_git::clone::{CloneOptions, clone_into};
use covalence_git::gix_hash;
use covalence_git::store::{GitBackend, GitObjectKind, GitStore};

/// Returns true if the `git` CLI is callable.
fn git_available() -> bool {
    Command::new("git")
        .arg("--version")
        .output()
        .map(|out| out.status.success())
        .unwrap_or(false)
}

/// Run `git <args>` with the given working directory, asserting success.
/// Sets author/committer env so commits are deterministic.
fn git(cwd: &Path, args: &[&str]) -> std::process::Output {
    let out = Command::new("git")
        .args(args)
        .current_dir(cwd)
        // Pin identity + dates so test runs are reproducible across machines.
        .env("GIT_AUTHOR_NAME", "Cov Test")
        .env("GIT_AUTHOR_EMAIL", "cov@test.invalid")
        .env("GIT_AUTHOR_DATE", "2026-01-01T00:00:00Z")
        .env("GIT_COMMITTER_NAME", "Cov Test")
        .env("GIT_COMMITTER_EMAIL", "cov@test.invalid")
        .env("GIT_COMMITTER_DATE", "2026-01-01T00:00:00Z")
        // Don't let global user config leak in.
        .env("HOME", cwd)
        .env("XDG_CONFIG_HOME", cwd)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .output()
        .expect("git invocation");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr),
    );
    out
}

/// Trim trailing whitespace from a captured `git` stdout to a single-line
/// `String`.
fn one_line(out: std::process::Output) -> String {
    String::from_utf8(out.stdout)
        .expect("utf8")
        .trim()
        .to_string()
}

fn rev_parse(cwd: &Path, rev: &str) -> gix_hash::ObjectId {
    let s = one_line(git(cwd, &["rev-parse", rev]));
    gix_hash::ObjectId::from_hex(s.as_bytes()).expect("hex oid")
}

/// Create a worktree-shaped repo on `main` with two commits and a nested
/// directory layout:
///
/// ```text
/// repo/
///   README.md            -- commit 1: "init"
///   src/
///     lib.rs             -- commit 2: "add lib"
///   docs/
///     notes.md           -- commit 2
/// ```
///
/// Returns the worktree root, the two commit OIDs (initial, second), and the
/// final-tree OID.
fn build_worktree_repo(
    work: &Path,
) -> (PathBuf, gix_hash::ObjectId, gix_hash::ObjectId, gix_hash::ObjectId) {
    let repo = work.join("repo");
    std::fs::create_dir_all(&repo).unwrap();

    git(&repo, &["init", "-q", "--initial-branch=main"]);
    std::fs::write(repo.join("README.md"), b"hello\n").unwrap();
    git(&repo, &["add", "README.md"]);
    git(&repo, &["commit", "-q", "-m", "init"]);
    let c1 = rev_parse(&repo, "HEAD");

    std::fs::create_dir_all(repo.join("src")).unwrap();
    std::fs::create_dir_all(repo.join("docs")).unwrap();
    std::fs::write(repo.join("src/lib.rs"), b"pub fn it() {}\n").unwrap();
    std::fs::write(repo.join("docs/notes.md"), b"hi\n").unwrap();
    git(&repo, &["add", "src/lib.rs", "docs/notes.md"]);
    git(&repo, &["commit", "-q", "-m", "add lib"]);
    let c2 = rev_parse(&repo, "HEAD");
    let tree2 = rev_parse(&repo, "HEAD^{tree}");

    (repo, c1, c2, tree2)
}

#[test]
fn clone_basic_worktree() {
    if !git_available() {
        eprintln!("skipping: git CLI not available");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let (repo, c1, c2, tree2) = build_worktree_repo(tmp.path());

    let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
    let opts = CloneOptions {
        url: repo.to_string_lossy().into_owned(),
        depth: None,
        filter: None,
        ref_prefixes: Vec::new(),
    };
    let result = clone_into(&opts, &dest, |_| {}).unwrap();

    // Every git object git made is now in our store: two commits, three
    // trees ({c1, c2, c2/src, c2/docs}), three blobs (README, lib.rs,
    // notes.md). Allow for git emitting an extra dedup'd object — the
    // invariants we care about are: every commit + tree + blob is present.
    assert!(dest.contains_object(&c1), "commit 1 missing");
    assert!(dest.contains_object(&c2), "commit 2 missing");
    assert!(dest.contains_object(&tree2), "tree of HEAD missing");
    assert!(result.objects_stored >= 7, "got {}", result.objects_stored);

    // HEAD resolves through to refs/heads/main, both pointing at c2.
    let head = result.refs.iter().find(|r| r.name == "HEAD").expect("HEAD");
    assert_eq!(head.oid, c2);
    assert_eq!(head.symref_target.as_deref(), Some("refs/heads/main"));
    let main = result
        .refs
        .iter()
        .find(|r| r.name == "refs/heads/main")
        .expect("main");
    assert_eq!(main.oid, c2);

    // Three trees in the final tree (root + src + docs) all converted.
    let conv = result.cov_trees.len();
    assert!(conv >= 3, "expected >= 3 cov trees, got {conv}");
    // The git OID of HEAD's root tree is in the conversion map.
    assert!(
        result.cov_trees.iter().any(|(g, _)| *g == tree2),
        "HEAD root tree not converted",
    );
}

#[test]
fn clone_with_branch_and_tag() {
    if !git_available() {
        eprintln!("skipping: git CLI not available");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let (repo, c1, c2, _) = build_worktree_repo(tmp.path());

    // Add a feature branch off c1 with one extra commit.
    git(&repo, &["checkout", "-q", "-b", "feature", &c1.to_string()]);
    std::fs::write(repo.join("FEATURE"), b"work in progress\n").unwrap();
    git(&repo, &["add", "FEATURE"]);
    git(&repo, &["commit", "-q", "-m", "feature work"]);
    let feature = rev_parse(&repo, "HEAD");

    // Lightweight tag on c2.
    git(&repo, &["checkout", "-q", "main"]);
    git(&repo, &["tag", "v1.0", &c2.to_string()]);

    let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
    let result = clone_into(
        &CloneOptions {
            url: repo.to_string_lossy().into_owned(),
            depth: None,
            filter: None,
            ref_prefixes: Vec::new(),
        },
        &dest,
        |_| {},
    )
    .unwrap();

    let names: Vec<&str> = result.refs.iter().map(|r| r.name.as_str()).collect();
    assert!(names.contains(&"refs/heads/main"), "main missing in {names:?}");
    assert!(
        names.contains(&"refs/heads/feature"),
        "feature missing in {names:?}",
    );
    assert!(
        names.contains(&"refs/tags/v1.0"),
        "tag missing in {names:?}",
    );

    let feat = result
        .refs
        .iter()
        .find(|r| r.name == "refs/heads/feature")
        .unwrap();
    assert_eq!(feat.oid, feature);
    let tag = result
        .refs
        .iter()
        .find(|r| r.name == "refs/tags/v1.0")
        .unwrap();
    assert_eq!(tag.oid, c2);
}

#[test]
fn clone_packed_repo() {
    if !git_available() {
        eprintln!("skipping: git CLI not available");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let (repo, c1, c2, tree2) = build_worktree_repo(tmp.path());

    // Force git to pack everything and prune the loose objects so the clone
    // exercises the packfile read path inside gix-odb.
    git(&repo, &["repack", "-q", "-a", "-d"]);
    git(&repo, &["prune-packed"]);
    git(&repo, &["pack-refs", "--all", "--prune"]);

    let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
    let result = clone_into(
        &CloneOptions {
            url: repo.to_string_lossy().into_owned(),
            depth: None,
            filter: None,
            ref_prefixes: Vec::new(),
        },
        &dest,
        |_| {},
    )
    .unwrap();

    assert!(dest.contains_object(&c1), "packed c1 missing");
    assert!(dest.contains_object(&c2), "packed c2 missing");
    assert!(dest.contains_object(&tree2), "packed tree missing");

    // packed-refs path is exercised: HEAD + refs/heads/main both present.
    let head = result.refs.iter().find(|r| r.name == "HEAD").unwrap();
    assert_eq!(head.oid, c2);
    let main = result
        .refs
        .iter()
        .find(|r| r.name == "refs/heads/main")
        .unwrap();
    assert_eq!(main.oid, c2);
}

#[test]
fn clone_bare_repo() {
    if !git_available() {
        eprintln!("skipping: git CLI not available");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let (worktree, _, c2, _) = build_worktree_repo(tmp.path());

    // Clone the worktree repo into a fresh bare repo via `git clone --bare`,
    // then point our cloner at that bare directory.
    let bare = tmp.path().join("bare.git");
    git(
        tmp.path(),
        &[
            "clone",
            "-q",
            "--bare",
            &worktree.to_string_lossy(),
            &bare.to_string_lossy(),
        ],
    );

    let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
    let result = clone_into(
        &CloneOptions {
            url: bare.to_string_lossy().into_owned(),
            depth: None,
            filter: None,
            ref_prefixes: Vec::new(),
        },
        &dest,
        |_| {},
    )
    .unwrap();

    assert!(dest.contains_object(&c2));
    let main = result
        .refs
        .iter()
        .find(|r| r.name == "refs/heads/main")
        .unwrap();
    assert_eq!(main.oid, c2);
}

#[test]
fn clone_object_payload_round_trip() {
    if !git_available() {
        eprintln!("skipping: git CLI not available");
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let repo = tmp.path().join("repo");
    std::fs::create_dir_all(&repo).unwrap();
    git(&repo, &["init", "-q", "--initial-branch=main"]);

    // Write a specific payload, then verify the destination store hands back
    // those exact bytes when looked up by the git-computed OID.
    let payload = b"the exact bytes we expect back\n";
    std::fs::write(repo.join("file.txt"), payload).unwrap();
    git(&repo, &["add", "file.txt"]);
    git(&repo, &["commit", "-q", "-m", "x"]);
    let blob_oid = rev_parse(&repo, "HEAD:file.txt");

    let dest = GitStore::memory(gix_hash::Kind::Sha1).unwrap();
    clone_into(
        &CloneOptions {
            url: repo.to_string_lossy().into_owned(),
            depth: None,
            filter: None,
            ref_prefixes: Vec::new(),
        },
        &dest,
        |_| {},
    )
    .unwrap();

    let obj = dest.read_object(&blob_oid).unwrap();
    assert_eq!(obj.kind, GitObjectKind::Blob);
    assert_eq!(obj.data, payload);
}
