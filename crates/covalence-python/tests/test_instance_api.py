"""Tests for Module, Container, and prove()."""

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

EMPTY_COMPONENT = "(component)"


# ---------------------------------------------------------------------------
# Module basics
# ---------------------------------------------------------------------------

def test_module_from_wat():
    m = covalence.Module.from_wat("(module)")
    assert isinstance(m, covalence.Module)


def test_module_bytes():
    m = covalence.Module.from_wat("(module)")
    raw = bytes(m)
    assert raw[:4] == b"\x00asm"
    assert raw[4] == 0x01  # module encoding byte


def test_module_hash():
    m = covalence.Module.from_wat("(module)")
    expected = covalence.O256.blob(bytes(m))
    assert m.hash == expected


def test_module_imports_exports():
    m = covalence.Module.from_wat("(module)")
    assert m.imports == []
    assert m.exports == []


def test_module_with_import():
    m = covalence.Module.from_wat(
        '(module (import "env" "foo" (func)))'
    )
    assert m.imports == [("env", "foo")]


def test_module_with_export():
    m = covalence.Module.from_wat(
        '(module (func (export "bar")))'
    )
    assert m.exports == ["bar"]


def test_module_rejects_component():
    c = covalence.Component.from_wat(EMPTY_COMPONENT)
    with pytest.raises(ValueError, match="module"):
        covalence.Module.from_bytes(bytes(c))


def test_module_repr():
    m = covalence.Module.from_wat("(module)")
    r = repr(m)
    assert r.startswith("Module(")
    assert "bytes" in r


def test_module_len():
    m = covalence.Module.from_wat("(module)")
    assert len(m) == len(bytes(m))


def test_module_eq():
    m1 = covalence.Module.from_wat("(module)")
    m2 = covalence.Module.from_wat("(module)")
    assert m1 == m2


def test_module_hash_in_set():
    m1 = covalence.Module.from_wat("(module)")
    m2 = covalence.Module.from_wat("(module)")
    s = {m1, m2}
    assert len(s) == 1


# ---------------------------------------------------------------------------
# Container basics
# ---------------------------------------------------------------------------

def test_container_from_wat():
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    assert isinstance(c, covalence.Container)


def test_container_hash():
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    expected = covalence.O256.blob(bytes(c))
    assert c.hash == expected


def test_container_imports():
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    assert c.imports == ["attest"]


def test_container_empty():
    c = covalence.Container.from_wat(EMPTY_COMPONENT)
    assert c.imports == []
    assert c.exports == []


def test_container_from_component():
    comp = covalence.Component.from_wat(TRIVIAL_TRUE)
    c = covalence.Container.from_component(comp)
    assert c.hash == comp.hash


def test_container_repr():
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    r = repr(c)
    assert r.startswith("Container(")
    assert "bytes" in r


def test_container_eq():
    c1 = covalence.Container.from_wat(TRIVIAL_TRUE)
    c2 = covalence.Container.from_wat(TRIVIAL_TRUE)
    assert c1 == c2


# ---------------------------------------------------------------------------
# store() accepts Module and Container
# ---------------------------------------------------------------------------

def test_store_module():
    m = covalence.Module.from_wat("(module)")
    h = covalence.store(m)
    assert h == m.hash


def test_store_container():
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    h = covalence.store(c)
    assert h == c.hash


def test_backend_store_module():
    k = covalence.local()
    m = covalence.Module.from_wat("(module)")
    h = k.store(m)
    assert h == m.hash
    assert k.has_blob(h)


def test_backend_store_container():
    k = covalence.local()
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    h = k.store(c)
    assert h == c.hash
    assert k.has_blob(h)
