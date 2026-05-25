"""Tests for GitStore typed object store API (insert_object, get_object, get_typed)."""

import tempfile

import pytest

import covalence


# ---------------------------------------------------------------------------
# insert_object / get_object round-trip
# ---------------------------------------------------------------------------


def test_insert_blob_get_object():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("blob", b"hello")
        assert isinstance(h, covalence.GitObject)

        result = s.get_object(h)
        assert result is not None
        kind, data = result
        assert kind == "blob"
        assert data == b"hello"


def test_insert_tree_get_object():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("tree", b"fake tree data")

        kind, data = s.get_object(h)
        assert kind == "tree"
        assert data == b"fake tree data"


def test_insert_commit_get_object():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("commit", b"commit payload")

        kind, data = s.get_object(h)
        assert kind == "commit"
        assert data == b"commit payload"


def test_insert_tag_get_object():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("tag", b"tag payload")

        kind, data = s.get_object(h)
        assert kind == "tag"
        assert data == b"tag payload"


# ---------------------------------------------------------------------------
# get_typed — successful retrieval
# ---------------------------------------------------------------------------


def test_get_typed_blob():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("blob", b"typed blob")
        assert s.get_typed(h, "blob") == b"typed blob"


def test_get_typed_tree():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("tree", b"tree bytes")
        assert s.get_typed(h, "tree") == b"tree bytes"


# ---------------------------------------------------------------------------
# get_typed — type mismatch
# ---------------------------------------------------------------------------


def test_get_typed_mismatch_raises():
    """Reading a tree as a blob raises TypeError."""
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("tree", b"tree data")

        with pytest.raises(TypeError, match="type mismatch"):
            s.get_typed(h, "blob")


def test_get_typed_mismatch_message():
    """Error message includes expected and actual kinds."""
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("commit", b"commit data")

        with pytest.raises(TypeError, match="expected tag.*got commit"):
            s.get_typed(h, "tag")


# ---------------------------------------------------------------------------
# get_typed / get_object — missing key
# ---------------------------------------------------------------------------


def test_get_typed_missing_returns_none():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        hasher = covalence.git_sha1()
        h = hasher.hash_blob(b"not stored")
        assert s.get_typed(h, "blob") is None


def test_get_object_missing_returns_none():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        hasher = covalence.git_sha1()
        h = hasher.hash_blob(b"not stored")
        assert s.get_object(h) is None


# ---------------------------------------------------------------------------
# insert_object validation
# ---------------------------------------------------------------------------


def test_insert_object_bad_kind():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        with pytest.raises(ValueError, match="unknown object kind"):
            s.insert_object("invalid", b"data")


# ---------------------------------------------------------------------------
# Cross-API consistency
# ---------------------------------------------------------------------------


def test_insert_blob_matches_untyped_insert():
    """insert_object("blob", data) produces the same hash as insert(data)."""
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h1 = s.insert(b"same content")
        h2 = s.insert_object("blob", b"same content")
        assert h1 == h2


def test_untyped_get_reads_typed_object():
    """Untyped get() can read objects written with insert_object."""
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d)
        h = s.insert_object("tree", b"tree bytes")
        # Untyped get returns raw data regardless of kind
        assert s.get(h) == b"tree bytes"


# ---------------------------------------------------------------------------
# SHA-256
# ---------------------------------------------------------------------------


def test_sha256_typed_round_trip():
    with tempfile.TemporaryDirectory() as d:
        s = covalence.GitStore(d, algo="sha256")
        h = s.insert_object("tree", b"sha256 tree")
        assert h.kind == "sha256"

        kind, data = s.get_object(h)
        assert kind == "tree"
        assert data == b"sha256 tree"
