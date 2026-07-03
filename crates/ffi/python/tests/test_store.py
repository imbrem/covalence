"""Tests for Store (memory, SQLite, Python-backed) and Backend integration."""

import os
import tempfile

import pytest

import covalence


# ---------------------------------------------------------------------------
# Memory store
# ---------------------------------------------------------------------------

def test_memory_insert_get():
    s = covalence.Store.memory()
    h = s.insert(b"hello")
    assert isinstance(h, covalence.O256)
    assert s.get(h) == b"hello"


def test_memory_put_get():
    s = covalence.Store.memory()
    h = covalence.O256.blob(b"world")
    s.put(h, b"world")
    assert s.get(h) == b"world"


def test_memory_contains():
    s = covalence.Store.memory()
    h = s.insert(b"abc")
    assert s.contains(h)
    missing = covalence.O256.blob(b"nope")
    assert not s.contains(missing)


def test_memory_in_operator():
    s = covalence.Store.memory()
    h = s.insert(b"x")
    assert h in s
    missing = covalence.O256.blob(b"nope")
    assert missing not in s


def test_memory_len():
    s = covalence.Store.memory()
    assert len(s) == 0
    s.insert(b"a")
    assert len(s) == 1
    s.insert(b"b")
    assert len(s) == 2


def test_memory_dedup():
    s = covalence.Store.memory()
    h1 = s.insert(b"same")
    h2 = s.insert(b"same")
    assert h1 == h2
    assert len(s) == 1


def test_memory_get_missing():
    s = covalence.Store.memory()
    assert s.get(covalence.O256.blob(b"nope")) is None


def test_memory_get_by_hex():
    s = covalence.Store.memory()
    h = s.insert(b"hex-test")
    assert s.get(h.hex) == b"hex-test"


def test_memory_repr():
    s = covalence.Store.memory()
    assert "0 blobs" in repr(s)
    s.insert(b"a")
    assert "1 blobs" in repr(s)


# ---------------------------------------------------------------------------
# SQLite store
# ---------------------------------------------------------------------------

def test_sqlite_basics():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "test.db")
        s = covalence.Store.sqlite(path)
        h = s.insert(b"hello")
        assert s.get(h) == b"hello"
        assert s.contains(h)
        assert len(s) == 1


def test_sqlite_persistence():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "test.db")
        s1 = covalence.Store.sqlite(path)
        h = s1.insert(b"persistent")
        del s1
        s2 = covalence.Store.sqlite(path)
        assert s2.get(h) == b"persistent"


# ---------------------------------------------------------------------------
# Python-backed store (minimal: get + put only)
# ---------------------------------------------------------------------------

class MinimalStore:
    """Bare-minimum store: only get and put."""
    def __init__(self):
        self._data = {}

    def get(self, key):
        return self._data.get(str(key))

    def put(self, key, data):
        self._data[str(key)] = bytes(data)


def test_python_store_insert_get():
    s = covalence.Store(MinimalStore())
    h = s.insert(b"hello")
    assert isinstance(h, covalence.O256)
    assert s.get(h) == b"hello"


def test_python_store_put_get():
    s = covalence.Store(MinimalStore())
    h = covalence.O256.blob(b"data")
    s.put(h, b"data")
    assert s.get(h) == b"data"


def test_python_store_contains_fallback():
    """Without a contains method, falls back to get() is not None."""
    s = covalence.Store(MinimalStore())
    h = s.insert(b"yes")
    assert s.contains(h)
    assert not s.contains(covalence.O256.blob(b"no"))


def test_python_store_len_raises_without_dunder():
    """MinimalStore has no __len__, so len(store) should raise."""
    s = covalence.Store(MinimalStore())
    s.insert(b"x")
    with pytest.raises(RuntimeError):
        len(s)


def test_python_store_missing_get():
    class NoPut:
        def get(self, key):
            return None
    with pytest.raises(TypeError, match="put"):
        covalence.Store(NoPut())


def test_python_store_missing_put():
    class NoGet:
        def put(self, key, data):
            pass
    with pytest.raises(TypeError, match="get"):
        covalence.Store(NoGet())


# ---------------------------------------------------------------------------
# Python-backed store (full protocol)
# ---------------------------------------------------------------------------

class FullStore:
    """Store implementing all optional methods."""
    def __init__(self):
        self._data = {}
        self.insert_called = False
        self.contains_called = False
        self.len_called = False

    def get(self, key):
        return self._data.get(str(key))

    def put(self, key, data):
        self._data[str(key)] = bytes(data)

    def insert(self, data):
        self.insert_called = True
        h = covalence.O256.blob(data)
        self._data[str(h)] = bytes(data)
        return h

    def contains(self, key):
        self.contains_called = True
        return str(key) in self._data

    def __len__(self):
        self.len_called = True
        return len(self._data)


def test_python_store_full_insert():
    inner = FullStore()
    s = covalence.Store(inner)
    h = s.insert(b"custom")
    assert inner.insert_called
    assert s.get(h) == b"custom"


def test_python_store_full_contains():
    inner = FullStore()
    s = covalence.Store(inner)
    s.insert(b"x")
    s.contains(covalence.O256.blob(b"x"))
    assert inner.contains_called


def test_python_store_full_len():
    inner = FullStore()
    s = covalence.Store(inner)
    s.insert(b"a")
    assert len(s) == 1
    assert inner.len_called


# ---------------------------------------------------------------------------
# Backend integration
# ---------------------------------------------------------------------------

def test_backend_with_memory_store():
    s = covalence.Store.memory()
    b = covalence.local(store=s)
    h = b.store_blob(b"shared")
    assert s.get(h) == b"shared"


def test_backend_with_sqlite_store():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "test.db")
        s = covalence.Store.sqlite(path)
        b = covalence.local(store=s)
        h = b.store_blob(b"sqlite-shared")
        assert s.get(h) == b"sqlite-shared"


def test_backend_with_python_store():
    s = covalence.Store(MinimalStore())
    b = covalence.local(store=s)
    h = b.store_blob(b"py-shared")
    assert s.get(h) == b"py-shared"


def test_backend_shared_visibility():
    """Data stored via Store is visible from Backend, and vice versa."""
    s = covalence.Store.memory()
    b = covalence.local(store=s)
    # Store -> Backend
    h1 = s.insert(b"from-store")
    assert b.get_blob(h1) == b"from-store"
    # Backend -> Store
    h2 = b.store_blob(b"from-backend")
    assert s.get(h2) == b"from-backend"


def test_backend_default_no_store():
    """local() without store still works (backward compat)."""
    b = covalence.local()
    h = b.store_blob(b"test")
    assert b.get_blob(h) == b"test"


def test_two_backends_one_store():
    """Two backends sharing one store see each other's data."""
    s = covalence.Store.memory()
    b1 = covalence.local(store=s)
    b2 = covalence.local(store=s)
    h = b1.store_blob(b"shared-data")
    assert b2.get_blob(h) == b"shared-data"
