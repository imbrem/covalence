"""Tests for O256, Hasher, GitHasher, and GitObject."""

import os
import tempfile

import pytest

import covalence


# ---------------------------------------------------------------------------
# O256
# ---------------------------------------------------------------------------

def test_o256_blob():
    h = covalence.O256.blob(b"hello")
    assert len(h.hex) == 64
    assert h.hex == "ea8f163db38682925e4491c5e58d4bb3506ef8c14eb78a86e908c5624a67200f"


def test_o256_from_hex_roundtrip():
    h = covalence.O256.blob(b"hello")
    h2 = covalence.O256.from_hex(h.hex)
    assert h == h2


def test_o256_from_bytes_roundtrip():
    h = covalence.O256.blob(b"hello")
    raw = bytes(h)
    assert len(raw) == 32
    h2 = covalence.O256.from_bytes(raw)
    assert h == h2


def test_o256_str_repr():
    h = covalence.O256.blob(b"test")
    assert str(h) == h.hex
    assert repr(h).startswith("O256(")


def test_o256_hash_usable_in_set():
    a = covalence.O256.blob(b"a")
    b = covalence.O256.blob(b"b")
    s = {a, b, a}
    assert len(s) == 2


def test_o256_equality_and_inequality():
    a = covalence.O256.blob(b"a")
    b = covalence.O256.blob(b"b")
    a2 = covalence.O256.blob(b"a")
    assert a == a2
    assert a != b


def test_o256_keyed_hash():
    key = covalence.O256.blob(b"hello")
    h = key.hash(b"world")
    assert h.hex == "3cc37778d40bea3cc1de2563ec424204b0916e2d5b870d7e61f4dcb5830fa69f"


def test_o256_keyed_hash_different_keys():
    k1 = covalence.O256.blob(b"key1")
    k2 = covalence.O256.blob(b"key2")
    assert k1.hash(b"data") != k2.hash(b"data")


def test_o256_hash_file():
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(b"world")
        f.flush()
        path = f.name
    try:
        key = covalence.O256.blob(b"hello")
        assert key.hash_file(path) == key.hash(b"world")
    finally:
        os.unlink(path)


def test_o256_from_hex_bad_input():
    with pytest.raises(ValueError):
        covalence.O256.from_hex("not-hex")
    with pytest.raises(ValueError):
        covalence.O256.from_hex("abcd")  # too short


def test_o256_from_bytes_bad_length():
    with pytest.raises(ValueError):
        covalence.O256.from_bytes(b"too short")
    with pytest.raises(ValueError):
        covalence.O256.from_bytes(b"\x00" * 33)  # too long


def test_o256_hash_file_missing():
    key = covalence.O256.blob(b"key")
    with pytest.raises(RuntimeError):
        key.hash_file("/nonexistent/path/to/file")


def test_o256_blob_empty():
    h = covalence.O256.blob(b"")
    assert len(h.hex) == 64
    assert h != covalence.O256.blob(b"\x00")


def test_o256_deterministic():
    """Same input always produces the same hash."""
    for _ in range(10):
        assert covalence.O256.blob(b"deterministic") == covalence.O256.blob(b"deterministic")


# ---------------------------------------------------------------------------
# Hasher
# ---------------------------------------------------------------------------

def test_blake3_hasher():
    h = covalence.blake3()
    result = h.hash(b"hello")
    assert result == covalence.O256.blob(b"hello")


def test_sha256_hasher():
    h = covalence.sha256()
    result = h.hash(b"hello")
    assert result.hex == "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"


def test_blake3_keyed_hasher():
    key = covalence.O256.blob(b"hello")
    h = covalence.blake3_keyed(key)
    result = h.hash(b"world")
    assert result == key.hash(b"world")


def test_blake3_kdf_hasher():
    h = covalence.blake3_kdf("covalence test")
    result = h.hash(b"hello")
    assert result.hex == "dbebf5103aedc920c405537138558c171a6ae79ec591b5875029e2186951ea35"


def test_blake3_kdf_different_contexts():
    h1 = covalence.blake3_kdf("context A")
    h2 = covalence.blake3_kdf("context B")
    assert h1.hash(b"same data") != h2.hash(b"same data")


def test_hasher_by_name():
    h = covalence.hasher("blake3")
    assert h.hash(b"hello") == covalence.blake3().hash(b"hello")
    h2 = covalence.hasher("sha256")
    assert h2.hash(b"hello") == covalence.sha256().hash(b"hello")


def test_hasher_by_name_unknown():
    with pytest.raises(ValueError):
        covalence.hasher("md5")


def test_hasher_hash_file():
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(b"hello")
        f.flush()
        path = f.name
    try:
        h = covalence.blake3()
        assert h.hash_file(path) == h.hash(b"hello")
    finally:
        os.unlink(path)


def test_hasher_hash_file_missing():
    h = covalence.blake3()
    with pytest.raises(RuntimeError):
        h.hash_file("/nonexistent/path")


# ---------------------------------------------------------------------------
# GitHasher / GitObject
# ---------------------------------------------------------------------------

def test_git_sha1():
    h = covalence.git_sha1()
    obj = h.hash_blob(b"hello")
    assert obj.kind == "sha1"
    assert obj.hex == "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0"


def test_git_sha256():
    h = covalence.git_sha256()
    obj = h.hash_blob(b"hello")
    assert obj.kind == "sha256"
    assert obj.hex == "8aec4e4876f854f688d0ebfc8f37598f38e5fd6903cccc850ca36591175aeb60"


def test_git_object_str_repr():
    h = covalence.git_sha1()
    obj = h.hash_blob(b"test")
    assert str(obj) == obj.hex
    assert "GitObject" in repr(obj)
    assert obj.kind in repr(obj)


def test_git_sha256_to_o256():
    h = covalence.git_sha256()
    obj = h.hash_blob(b"hello")
    o = obj.to_o256()
    assert isinstance(o, covalence.O256)
    assert o.hex == obj.hex  # same 64-char hex for sha256


def test_git_sha1_to_o256_raises():
    h = covalence.git_sha1()
    obj = h.hash_blob(b"hello")
    with pytest.raises(ValueError, match="SHA-1"):
        obj.to_o256()


def test_git_hash_blob_file():
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(b"hello")
        f.flush()
        path = f.name
    try:
        h = covalence.git_sha1()
        obj = h.hash_blob_file(path)
        assert obj == h.hash_blob(b"hello")
    finally:
        os.unlink(path)


def test_git_object_bytes():
    obj = covalence.git_sha1().hash_blob(b"test")
    raw = bytes(obj)
    assert len(raw) == 20  # SHA-1 is 20 bytes

    obj256 = covalence.git_sha256().hash_blob(b"test")
    raw256 = bytes(obj256)
    assert len(raw256) == 32  # SHA-256 is 32 bytes


def test_git_object_equality():
    h = covalence.git_sha1()
    a = h.hash_blob(b"hello")
    b = h.hash_blob(b"hello")
    c = h.hash_blob(b"world")
    assert a == b
    assert a != c


def test_git_object_hash_in_set():
    h = covalence.git_sha1()
    a = h.hash_blob(b"a")
    b = h.hash_blob(b"b")
    s = {a, b, a}
    assert len(s) == 2


def test_git_tree_hash():
    h = covalence.git_sha1()
    tree = h.hash_tree(b"\x00" * 40)  # arbitrary tree-shaped data
    assert tree.kind == "sha1"
    blob = h.hash_blob(b"\x00" * 40)
    assert tree != blob  # tree vs blob hashing should differ


def test_git_hash_blob_file_missing():
    h = covalence.git_sha1()
    with pytest.raises(RuntimeError):
        h.hash_blob_file("/nonexistent/path")
