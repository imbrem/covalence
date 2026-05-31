"""Tests for module-level convenience API (lazy default backend)."""

import covalence


def test_store_and_get():
    h = covalence.store(b"default hello")
    assert isinstance(h, covalence.O256)
    data = covalence.get(h)
    assert data == b"default hello"


def test_store_str():
    h = covalence.store_str("text value")
    assert covalence.get(h) == b"text value"


def test_has():
    h = covalence.store(b"check me")
    assert covalence.has(h)
    missing = covalence.O256.blob(b"nonexistent")
    assert not covalence.has(missing)


def test_get_missing():
    missing = covalence.O256.blob(b"not stored")
    assert covalence.get(missing) is None


def test_shared_state():
    """Multiple calls share the same default backend."""
    h = covalence.store(b"shared state test")
    assert covalence.has(h)
    assert covalence.get(h) == b"shared state test"


def test_get_by_hex():
    h = covalence.store(b"hex lookup")
    data = covalence.get(h.hex)
    assert data == b"hex lookup"
