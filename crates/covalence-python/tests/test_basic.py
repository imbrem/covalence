"""Tests for Backend and Session (in-process, no TCP)."""

import os
import tempfile

import pytest

import covalence


TRIVIAL_TRUE = """
(component
    (import "attest" (func $attest))
    (core module $m
        (import "env" "attest" (func $attest))
        (func $start (call $attest))
        (start $start)
    )
    (core func $attest_lowered (canon lower (func $attest)))
    (core instance $i (instantiate $m
        (with "env" (instance
            (export "attest" (func $attest_lowered))
        ))
    ))
)
"""


# ---------------------------------------------------------------------------
# Backend (local)
# ---------------------------------------------------------------------------

def test_local_backend():
    k = covalence.local()
    h = k.store_blob(b"hello world")
    assert isinstance(h, covalence.O256)
    data = k.get_blob(h)
    assert data == b"hello world"


def test_store_str():
    k = covalence.local()
    h = k.store_str("hello")
    assert k.get_blob(h) == b"hello"


def test_has_blob():
    k = covalence.local()
    h = k.store_blob(b"data")
    assert k.has_blob(h)
    missing = covalence.O256.blob(b"nonexistent")
    assert not k.has_blob(missing)


def test_blob_count():
    k = covalence.local()
    assert k.blob_count() == 0
    k.store_blob(b"a")
    assert k.blob_count() == 1
    k.store_blob(b"b")
    assert k.blob_count() == 2


def test_blob_count_deduplication():
    k = covalence.local()
    k.store_blob(b"same")
    k.store_blob(b"same")
    assert k.blob_count() == 1


def test_get_blob_hex():
    k = covalence.local()
    h = k.store_blob(b"test")
    data = k.get_blob(h.hex)
    assert data == b"test"


def test_get_blob_missing():
    k = covalence.local()
    missing = covalence.O256.blob(b"nonexistent")
    assert k.get_blob(missing) is None


def test_get_blob_bad_hash():
    k = covalence.local()
    with pytest.raises(TypeError):
        k.get_blob(42)


def test_info():
    k = covalence.local()
    info = k.info()
    assert info["kind"] == "local"


def test_store_blob_content_addressed():
    """Storing the same data twice returns the same hash."""
    k = covalence.local()
    h1 = k.store_blob(b"dedup me")
    h2 = k.store_blob(b"dedup me")
    assert h1 == h2


def test_store_empty_blob():
    k = covalence.local()
    h = k.store_blob(b"")
    assert k.has_blob(h)
    assert k.get_blob(h) == b""


def test_store_large_blob():
    k = covalence.local()
    data = b"x" * (1024 * 1024)  # 1 MiB
    h = k.store_blob(data)
    assert k.get_blob(h) == data


def test_compile_wat_and_decide():
    k = covalence.local()
    h = k.compile_wat(TRIVIAL_TRUE)
    result = k.decide(h)
    assert result["decision"] == "sat"


def test_compile_wat_false():
    k = covalence.local()
    h = k.compile_wat("(component)")
    result = k.decide(h)
    assert result["decision"] == "unsat"


def test_compile_wat_invalid():
    k = covalence.local()
    with pytest.raises(ValueError):
        k.compile_wat("not valid wat at all")


def test_decide_returns_proved():
    k = covalence.local()
    h = k.compile_wat(TRIVIAL_TRUE)
    result = k.decide(h)
    assert "proved" in result
    assert isinstance(result["proved"], list)


def test_decide_with_hex():
    k = covalence.local()
    h = k.compile_wat(TRIVIAL_TRUE)
    result = k.decide(h.hex)
    assert result["decision"] == "sat"


def test_multiple_backends_independent():
    """Two backends should have independent stores."""
    a = covalence.local()
    b = covalence.local()
    h = a.store_blob(b"only in a")
    assert a.has_blob(h)
    assert not b.has_blob(h)


# ---------------------------------------------------------------------------
# Backend (persistent)
# ---------------------------------------------------------------------------

def test_local_persistent():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "test.db")
        k = covalence.local_persistent(path)
        h = k.store_blob(b"persistent")
        assert k.get_blob(h) == b"persistent"
        assert os.path.exists(path)


def test_local_persistent_survives_reopen():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "test.db")
        k1 = covalence.local_persistent(path)
        h = k1.store_blob(b"survive")
        del k1  # drop first backend
        k2 = covalence.local_persistent(path)
        assert k2.get_blob(h) == b"survive"


# ---------------------------------------------------------------------------
# Session
# ---------------------------------------------------------------------------

def test_session_local():
    s = covalence.session_local()
    result = s.eval("(help)")
    assert "store" in result
    assert "decide" in result


def test_session_eval():
    s = covalence.session_local()
    result = s.eval('(store "hello")')
    assert len(result) == 64  # hex hash


def test_session_eval_sequence():
    """Session should maintain state across eval calls."""
    s = covalence.session_local()
    h = s.eval('(store "hello")')
    result = s.eval(f'(read {h})')
    assert "hello" in result
