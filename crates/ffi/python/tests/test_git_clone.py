"""Tests for `covalence.GitImport` / `covalence.git_clone` — building a real
git repository via the `git` CLI, then importing it through the bindings."""

import os
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

import covalence


def _git_available() -> bool:
    return shutil.which("git") is not None


pytestmark = pytest.mark.skipif(not _git_available(), reason="git CLI not on PATH")


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _git(cwd: Path, *args: str) -> str:
    """Run `git <args>` in `cwd` with a hermetic environment."""
    env = {
        **os.environ,
        "GIT_AUTHOR_NAME": "Cov Test",
        "GIT_AUTHOR_EMAIL": "cov@test.invalid",
        "GIT_COMMITTER_NAME": "Cov Test",
        "GIT_COMMITTER_EMAIL": "cov@test.invalid",
        "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z",
        "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_SYSTEM": "/dev/null",
        "HOME": str(cwd),
        "XDG_CONFIG_HOME": str(cwd),
    }
    out = subprocess.run(
        ["git", *args], cwd=cwd, env=env, check=True, capture_output=True, text=True
    )
    return out.stdout.strip()


def _build_repo(work: Path) -> tuple[Path, str, str]:
    """Two commits on `main`. Returns (repo_path, commit1_oid, commit2_oid)."""
    repo = work / "repo"
    repo.mkdir(parents=True)
    _git(repo, "init", "-q", "--initial-branch=main")
    (repo / "README.md").write_bytes(b"hello\n")
    _git(repo, "add", "README.md")
    _git(repo, "commit", "-q", "-m", "init")
    c1 = _git(repo, "rev-parse", "HEAD")

    (repo / "src").mkdir()
    (repo / "src" / "lib.rs").write_bytes(b"pub fn it() {}\n")
    _git(repo, "add", "src/lib.rs")
    _git(repo, "commit", "-q", "-m", "add lib")
    c2 = _git(repo, "rev-parse", "HEAD")
    return repo, c1, c2


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------


def test_clone_local_into_memory_store():
    """Clone into an in-memory store and verify objects, refs, and trees."""
    with tempfile.TemporaryDirectory() as d:
        repo, c1, c2 = _build_repo(Path(d))

        result = covalence.git_clone(str(repo))
        assert isinstance(result, covalence.GitCloneResult)
        assert isinstance(result.store, covalence.GitImport)
        assert result.url == str(repo)

        # Two commits + at least one root tree + at least one blob.
        assert result.objects_stored >= 4
        store = result.store
        assert store.contains(c1)
        assert store.contains(c2)

        # HEAD resolves through to main.
        head = [r for r in result.refs if r.name == "HEAD"][0]
        assert head.oid == c2
        assert head.symref_target == "refs/heads/main"

        main = [r for r in result.refs if r.name == "refs/heads/main"][0]
        assert main.oid == c2

        # Covalence trees populated.
        assert result.cov_trees_count >= 2
        assert store.cov_tree_count == result.cov_trees_count


def test_resolve_and_reverse_round_trip():
    """A blob committed via git should round-trip through resolve/reverse."""
    with tempfile.TemporaryDirectory() as d:
        work = Path(d)
        repo = work / "repo"
        repo.mkdir()
        _git(repo, "init", "-q", "--initial-branch=main")
        payload = b"the exact bytes we expect back\n"
        (repo / "file.txt").write_bytes(payload)
        _git(repo, "add", "file.txt")
        _git(repo, "commit", "-q", "-m", "x")
        blob_oid = _git(repo, "rev-parse", "HEAD:file.txt")

        store = covalence.git_clone(str(repo)).store

        # Resolve: SHA-1 OID → O256 of the blob payload.
        o256 = store.resolve(blob_oid)
        assert isinstance(o256, covalence.O256)
        expected = covalence.O256.blob(payload)
        assert o256 == expected

        # Reverse: O256 → SHA-1 OID hex.
        found = store.reverse(o256)
        assert found is not None
        assert found.hex == blob_oid


def test_store_blob_extends_the_map():
    """`store_blob` writes a new git blob and the map grows by one entry."""
    with tempfile.TemporaryDirectory() as d:
        repo, _, _ = _build_repo(Path(d))
        result = covalence.git_clone(str(repo))
        store = result.store
        before = store.count

        oid = store.store_blob(b"a new blob added from python")
        assert oid.kind == "sha1"
        assert len(oid.hex) == 40

        # Count went up by one; resolve hits the new OID directly.
        assert store.count == before + 1
        o256 = store.resolve(oid)
        expected = covalence.O256.blob(b"a new blob added from python")
        assert o256 == expected


def test_classify_url():
    """Sanity-check the URL classifier surfaced for Python callers."""
    assert covalence.GitImport.classify("/abs/path") == "local"
    assert covalence.GitImport.classify("./rel") == "local"
    assert covalence.GitImport.classify("file:///tmp/x") == "local"
    assert covalence.GitImport.classify("https://github.com/foo/bar") == "http"


def test_clone_into_sqlite_persists_across_handles():
    """Clone with `store=path` writes to disk; reopening sees the same map."""
    with tempfile.TemporaryDirectory() as d:
        work = Path(d)
        repo, _, c2 = _build_repo(work)
        db = work / "out.db"

        first = covalence.git_clone(str(repo), store=str(db))
        first_count = first.store.count
        del first  # drop the handle; sqlite file remains

        reopened = covalence.GitImport.open(str(db))
        assert reopened.count == first_count
        assert reopened.contains(c2)


def test_branch_filter_restricts_refs():
    """`branch=main` drops a feature branch from the result."""
    with tempfile.TemporaryDirectory() as d:
        work = Path(d)
        repo, c1, _ = _build_repo(work)
        _git(repo, "checkout", "-q", "-b", "feature", c1)
        (repo / "FEATURE").write_bytes(b"work\n")
        _git(repo, "add", "FEATURE")
        _git(repo, "commit", "-q", "-m", "feature")
        _git(repo, "checkout", "-q", "main")

        result = covalence.git_clone(str(repo), branch="main")
        names = {r.name for r in result.refs}
        assert "refs/heads/main" in names
        assert "refs/heads/feature" not in names
        # HEAD survives the filter.
        assert "HEAD" in names


def test_clone_url_for_nonexistent_local_path_errors():
    with tempfile.TemporaryDirectory() as d:
        bad = Path(d) / "nope"
        with pytest.raises(Exception) as exc:
            covalence.git_clone(str(bad))
        assert "not a git repository" in str(exc.value) or "No such" in str(exc.value)
