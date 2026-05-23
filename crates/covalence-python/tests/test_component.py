"""Tests for Component, polymorphic store(), and polymorphic decide()."""

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

TRIVIAL_FALSE = "(component)"

EMPTY_COMPONENT = "(component)"


# ---------------------------------------------------------------------------
# Construction
# ---------------------------------------------------------------------------

def test_from_wat():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    assert isinstance(c, covalence.Component)


def test_from_bytes_roundtrip():
    c1 = covalence.Component.from_wat(TRIVIAL_TRUE)
    raw = bytes(c1)
    c2 = covalence.Component.from_bytes(raw)
    assert c1 == c2


def test_from_wat_empty_component():
    c = covalence.Component.from_wat(EMPTY_COMPONENT)
    assert c.imports == []
    assert c.exports == []


def test_from_wat_invalid_syntax():
    with pytest.raises(ValueError):
        covalence.Component.from_wat("not valid wat")


def test_from_wat_rejects_module():
    with pytest.raises(ValueError, match="component"):
        covalence.Component.from_wat("(module)")


def test_from_bytes_rejects_module():
    import covalence
    # Compile a module to get its bytes, then try Component.from_bytes
    wasm = bytes(covalence.Component.from_wat(EMPTY_COMPONENT))  # valid component bytes
    # Construct module bytes by compiling
    k = covalence.local()
    h = k.compile_wat("(module)")
    module_bytes = k.get_blob(h)
    with pytest.raises(ValueError, match="component"):
        covalence.Component.from_bytes(module_bytes)


def test_from_bytes_rejects_garbage():
    with pytest.raises(ValueError):
        covalence.Component.from_bytes(b"not wasm")


# ---------------------------------------------------------------------------
# Properties
# ---------------------------------------------------------------------------

def test_imports():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    assert c.imports == ["attest"]


def test_exports():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    assert c.exports == []


def test_wat_roundtrip():
    c1 = covalence.Component.from_wat(TRIVIAL_TRUE)
    wat_text = c1.wat
    assert "(component" in wat_text
    # Roundtrip: WAT -> Component -> WAT -> Component -> same bytes
    c2 = covalence.Component.from_wat(wat_text)
    assert bytes(c1) == bytes(c2)


def test_hash_matches_blob():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    expected = covalence.O256.blob(bytes(c))
    assert c.hash == expected


def test_hash_is_cached():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    h1 = c.hash
    h2 = c.hash
    assert h1 == h2


# ---------------------------------------------------------------------------
# Dunder methods
# ---------------------------------------------------------------------------

def test_len():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    assert len(c) == len(bytes(c))
    assert len(c) > 0


def test_repr():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    r = repr(c)
    assert r.startswith("Component(")
    assert "bytes" in r
    assert "imports" in r
    assert "exports" in r


def test_bytes_dunder():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    raw = bytes(c)
    assert isinstance(raw, bytes)
    assert raw[:4] == b"\x00asm"


def test_eq():
    c1 = covalence.Component.from_wat(TRIVIAL_TRUE)
    c2 = covalence.Component.from_wat(TRIVIAL_TRUE)
    assert c1 == c2


def test_eq_different():
    c1 = covalence.Component.from_wat(TRIVIAL_TRUE)
    c2 = covalence.Component.from_wat(EMPTY_COMPONENT)
    assert c1 != c2


def test_hash_in_set():
    c1 = covalence.Component.from_wat(TRIVIAL_TRUE)
    c2 = covalence.Component.from_wat(TRIVIAL_TRUE)
    c3 = covalence.Component.from_wat(EMPTY_COMPONENT)
    s = {c1, c2, c3}
    assert len(s) == 2


# ---------------------------------------------------------------------------
# Polymorphic store (module-level)
# ---------------------------------------------------------------------------

def test_store_bytes():
    h = covalence.store(b"hello")
    assert isinstance(h, covalence.O256)


def test_store_str():
    h = covalence.store("hello")
    expected = covalence.store(b"hello")
    assert h == expected


def test_store_component():
    c = covalence.Component.from_wat(EMPTY_COMPONENT)
    h = covalence.store(c)
    assert h == c.hash


def test_store_bad_type():
    with pytest.raises(TypeError):
        covalence.store(42)


# ---------------------------------------------------------------------------
# Polymorphic decide (module-level)
# ---------------------------------------------------------------------------

def test_decide_component_sat():
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    result = covalence.decide(c)
    assert result["decision"] == "sat"


def test_decide_component_unsat():
    c = covalence.Component.from_wat(TRIVIAL_FALSE)
    result = covalence.decide(c)
    assert result["decision"] == "unsat"


# ---------------------------------------------------------------------------
# Backend.store (polymorphic)
# ---------------------------------------------------------------------------

def test_backend_store_bytes():
    k = covalence.local()
    h = k.store(b"data")
    assert k.get_blob(h) == b"data"


def test_backend_store_str():
    k = covalence.local()
    h = k.store("text")
    assert k.get_blob(h) == b"text"


def test_backend_store_component():
    k = covalence.local()
    c = covalence.Component.from_wat(EMPTY_COMPONENT)
    h = k.store(c)
    assert h == c.hash
    assert k.has_blob(h)


# ---------------------------------------------------------------------------
# Backend.decide (polymorphic)
# ---------------------------------------------------------------------------

def test_backend_decide_component():
    k = covalence.local()
    c = covalence.Component.from_wat(TRIVIAL_TRUE)
    result = k.decide(c)
    assert result["decision"] == "sat"
