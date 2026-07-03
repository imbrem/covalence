"""Tests for TreeStore (memory and Python-backed)."""

import pytest

import covalence


# ---------------------------------------------------------------------------
# Memory TreeStore
# ---------------------------------------------------------------------------

def test_memory_set_get():
    kv = covalence.TreeStore.memory()
    kv.set(b"key", b"value")
    assert kv.get(b"key") == b"value"


def test_memory_get_missing():
    kv = covalence.TreeStore.memory()
    assert kv.get(b"nope") is None


def test_memory_overwrite():
    kv = covalence.TreeStore.memory()
    kv.set(b"k", b"v1")
    kv.set(b"k", b"v2")
    assert kv.get(b"k") == b"v2"


def test_memory_touch_touched():
    kv = covalence.TreeStore.memory()
    assert not kv.touched(b"x")
    kv.touch(b"x")
    assert kv.touched(b"x")


def test_memory_ns_isolation():
    kv = covalence.TreeStore.memory()
    kv.set(b"k", b"root")
    child = kv.ns(b"child")
    child.set(b"k", b"nested")
    assert kv.get(b"k") == b"root"
    assert child.get(b"k") == b"nested"


def test_memory_ns_sharing():
    """Two ns() calls with the same key return the same child."""
    kv = covalence.TreeStore.memory()
    c1 = kv.ns(b"x")
    c1.set(b"a", b"1")
    c2 = kv.ns(b"x")
    assert c2.get(b"a") == b"1"


def test_memory_dup_sharing():
    """dup() shares the underlying data."""
    kv = covalence.TreeStore.memory()
    kv.set(b"k", b"v")
    duped = kv.dup()
    assert duped.get(b"k") == b"v"
    duped.set(b"k2", b"v2")
    assert kv.get(b"k2") == b"v2"


def test_memory_repr():
    kv = covalence.TreeStore.memory()
    assert "TreeStore" in repr(kv)


# ---------------------------------------------------------------------------
# Python-backed TreeStore
# ---------------------------------------------------------------------------

class MinimalTreeStore:
    """Minimal tree store: set, get, ns, dup."""
    def __init__(self):
        self._data = {}
        self._children = {}

    def set(self, key, value):
        self._data[bytes(key)] = bytes(value)

    def get(self, key):
        return self._data.get(bytes(key))

    def ns(self, key):
        key = bytes(key)
        if key not in self._children:
            self._children[key] = MinimalTreeStore()
        return self._children[key]

    def dup(self):
        # Returns self (same data)
        return self


def test_python_store_set_get():
    kv = covalence.TreeStore(MinimalTreeStore())
    kv.set(b"hello", b"world")
    assert kv.get(b"hello") == b"world"


def test_python_store_ns():
    kv = covalence.TreeStore(MinimalTreeStore())
    child = kv.ns(b"sub")
    child.set(b"k", b"v")
    assert kv.get(b"k") is None
    assert child.get(b"k") == b"v"


def test_python_store_missing_method():
    """Must have set, get, ns, dup."""
    class NoNs:
        def set(self, k, v): pass
        def get(self, k): return None
        def dup(self): return self
    with pytest.raises(TypeError, match="ns"):
        covalence.TreeStore(NoNs())


def test_python_store_missing_dup():
    class NoDup:
        def set(self, k, v): pass
        def get(self, k): return None
        def ns(self, k): return self
    with pytest.raises(TypeError, match="dup"):
        covalence.TreeStore(NoDup())
