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


def test_container_rejects_unknown_import():
    wat = """
    (component
        (import "unknown-import" (func))
    )
    """
    with pytest.raises(ValueError, match="unknown kernel import"):
        covalence.Container.from_wat(wat)


def test_container_from_component():
    comp = covalence.Component.from_wat(TRIVIAL_TRUE)
    c = covalence.Container.from_component(comp)
    assert c.hash == comp.hash


def test_container_from_component_rejects_unknown():
    wat = """
    (component
        (import "unknown-import" (func))
    )
    """
    comp = covalence.Component.from_wat(wat)
    with pytest.raises(ValueError, match="unknown kernel import"):
        covalence.Container.from_component(comp)


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
# prove: composition
# ---------------------------------------------------------------------------

def test_prove_trivial_sat():
    """Prove a trivial attesting container: decision=sat, container hash in proved."""
    k = covalence.local()
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    result = k.prove(c)
    assert result["decision"] == "sat"
    assert str(c.hash) in result["proved"]


def test_prove_composition():
    """
    Build a dep that attests and exports a function, then a parent that
    calls through prove-{dep} (triggering the dep's start/attest) and attests.
    Both hashes should appear in proved.
    """
    k = covalence.local()

    # 1. Create the dep: attests in start, exports a dummy function
    dep_wat = """
    (component
        (import "attest" (func $attest))
        (core module $m
            (import "env" "attest" (func $attest))
            (func $start (call $attest))
            (start $start)
            (func $dummy (export "dummy"))
        )
        (core func $attest_lowered (canon lower (func $attest)))
        (core instance $i (instantiate $m
            (with "env" (instance
                (export "attest" (func $attest_lowered))
            ))
        ))
        (func $dummy_lifted (canon lift (core func $i "dummy")))
        (export "dummy" (func $dummy_lifted))
    )
    """
    dep = covalence.Container.from_wat(dep_wat)
    dep_hex = str(dep.hash)
    k.store(dep)

    # 2. Parent: imports prove-{dep} instance, calls dep's dummy, then attests
    parent_wat = f"""
    (component
        (import "attest" (func $attest))
        (import "prove-{dep_hex}" (instance $dep
            (export "dummy" (func))
        ))
        (alias export $dep "dummy" (func $dep_dummy))
        (core module $m
            (import "env" "attest" (func $attest))
            (import "dep" "dummy" (func $dep_dummy))
            (func $start
                (call $dep_dummy)
                (call $attest)
            )
            (start $start)
        )
        (core func $attest_lowered (canon lower (func $attest)))
        (core func $dep_dummy_lowered (canon lower (func $dep_dummy)))
        (core instance $i (instantiate $m
            (with "env" (instance
                (export "attest" (func $attest_lowered))
            ))
            (with "dep" (instance
                (export "dummy" (func $dep_dummy_lowered))
            ))
        ))
    )
    """
    parent = covalence.Container.from_wat(parent_wat)
    result = k.prove(parent)
    assert result["decision"] == "sat"
    # The dep hash should be in proved (from prove-{dep_hex} call-through)
    assert dep_hex in result["proved"]
    # The parent's own hash should also be in proved (prove_container adds it)
    assert str(parent.hash) in result["proved"]


def test_prove_unsat():
    """An empty container should be unsat."""
    k = covalence.local()
    c = covalence.Container.from_wat(EMPTY_COMPONENT)
    result = k.prove(c)
    assert result["decision"] == "unsat"


# ---------------------------------------------------------------------------
# Module-level prove convenience
# ---------------------------------------------------------------------------

def test_module_level_prove():
    c = covalence.Container.from_wat(TRIVIAL_TRUE)
    result = covalence.prove(c)
    assert result["decision"] == "sat"
    assert str(c.hash) in result["proved"]


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
