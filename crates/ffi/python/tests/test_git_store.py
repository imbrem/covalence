"""Tests for GitStore (git loose object store)."""

import os
import tempfile

import pytest

import covalence


# ---------------------------------------------------------------------------
# SHA-1 basics
# ---------------------------------------------------------------------------

def test_sha1_insert_get():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert(b"hello world")
        assert isinstance(h, covalence.GitObject)
        assert h.kind == "sha1"
        assert s.get(h) == b"hello world"


def test_sha1_put_get():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        # Insert first to get a valid hash, then put the same data
        h = s.insert(b"put-test")
        data = s.get(h)
        assert data == b"put-test"
        # put with the same key is idempotent
        s.put(h, b"put-test")
        assert s.get(h) == b"put-test"


def test_sha1_contains():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert(b"abc")
        assert s.contains(h)


def test_sha1_in_operator():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert(b"x")
        assert h in s


def test_sha1_get_missing():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        # Compute a hash for data that's not in the store
        hasher = covalence.git_sha1()
        h = hasher.hash_blob(b"not-stored")
        assert s.get(h) is None
        assert not s.contains(h)
        assert h not in s


def test_sha1_get_by_hex():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert(b"hex-test")
        assert s.get(h.hex) == b"hex-test"


def test_sha1_dedup():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h1 = s.insert(b"same")
        h2 = s.insert(b"same")
        assert h1 == h2


# ---------------------------------------------------------------------------
# SHA-256
# ---------------------------------------------------------------------------

def test_sha256_insert_get():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d, algo="sha256")
        h = s.insert(b"sha256 data")
        assert isinstance(h, covalence.GitObject)
        assert h.kind == "sha256"
        assert s.get(h) == b"sha256 data"


def test_sha256_hash_differs():
    with tempfile.TemporaryDirectory() as d1, tempfile.TemporaryDirectory() as d2:
        s1 = covalence.GitStore(d1, algo="sha1")
        s256 = covalence.GitStore(d2, algo="sha256")
        h1 = s1.insert(b"test")
        h256 = s256.insert(b"test")
        assert h1.hex != h256.hex
        assert h1.kind != h256.kind


# ---------------------------------------------------------------------------
# from_repo
# ---------------------------------------------------------------------------

def test_from_repo():
    with tempfile.TemporaryDirectory() as repo:
        # Create .git/objects structure
        objects_dir = os.path.join(repo, ".git", "objects")
        os.makedirs(objects_dir)
        s = covalence.GitStore.from_repo(repo)
        h = s.insert(b"repo data")
        assert s.get(h) == b"repo data"


def test_from_repo_sha256():
    with tempfile.TemporaryDirectory() as repo:
        objects_dir = os.path.join(repo, ".git", "objects")
        os.makedirs(objects_dir)
        s = covalence.GitStore.from_repo(repo, algo="sha256")
        assert s.algo == "sha256"
        h = s.insert(b"repo256")
        assert h.kind == "sha256"


# ---------------------------------------------------------------------------
# Properties and repr
# ---------------------------------------------------------------------------

def test_algo_property():
    with tempfile.TemporaryDirectory() as d:
        s1 = covalence.GitStore(d, algo="sha1")
        assert s1.algo == "sha1"
    with tempfile.TemporaryDirectory() as d:
        s256 = covalence.GitStore(d, algo="sha256")
        assert s256.algo == "sha256"


def test_repr():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        r = repr(s)
        assert "GitStore" in r
        assert "sha1" in r
        assert d in r


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------

def test_bad_algo():
    with tempfile.TemporaryDirectory() as d:
        with pytest.raises(ValueError, match="unknown algo"):
            covalence.GitStore(d, algo="md5")
