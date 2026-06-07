"""Smoke tests for `covalence.Graph` / `covalence.GraphBuilder`."""

import pytest

import covalence


def _src_snk(kind1="pure", kind2="pure"):
    b = covalence.GraphBuilder()
    src = b.add_node(
        ports=[{"name": "o", "type_id": 1, "kind": "output"}],
        payload=b"src",
        kind=kind1,
    )
    snk = b.add_node(
        ports=[{"name": "i", "type_id": 1, "kind": "input"}],
        payload=b"snk",
        kind=kind2,
    )
    b.wire(src, 0, snk, 0)
    return b.finish()


def test_build_and_inspect():
    g = _src_snk()
    assert g.node_count == 2
    assert g.edge_count == 1
    n0 = g.get_node(0)
    assert n0["kind"] == "pure"
    assert n0["payload"] == b"src"
    assert n0["ports"][0]["name"] == "o"
    assert n0["ports"][0]["kind"] == "output"


def test_canonical_roundtrip():
    g = _src_snk("ordered", "pure")
    data = g.to_bytes()
    assert data[:4] == b"COVG"
    g2 = covalence.Graph.from_bytes(data)
    assert g.equal(g2)
    assert g == g2
    assert g2.get_node(0)["kind"] == "ordered"
    assert g2.get_node(1)["kind"] == "pure"


def test_ordered_and_unordered_hashes_differ():
    g = _src_snk("ordered", "ordered")
    assert g.ordered_hash() != g.unordered_hash()
    assert len(g.ordered_hash()) == 32
    assert len(g.ordered_hash_hex()) == 64


def test_ordered_nodes_listed_in_order():
    g = _src_snk("ordered", "pure")
    assert g.ordered_nodes() == [0]
    g2 = _src_snk("pure", "ordered")
    assert g2.ordered_nodes() == [1]


def test_insertion_order_affects_equality():
    g1 = _src_snk()
    b = covalence.GraphBuilder()
    snk = b.add_node(
        ports=[{"name": "i", "type_id": 1, "kind": "input"}],
        payload=b"snk",
    )
    src = b.add_node(
        ports=[{"name": "o", "type_id": 1, "kind": "output"}],
        payload=b"src",
    )
    b.wire(src, 0, snk, 0)
    g2 = b.finish()
    assert not g1.equal(g2)
    assert g1.ordered_hash() != g2.ordered_hash()


def test_type_mismatch_rejected():
    b = covalence.GraphBuilder()
    src = b.add_node(
        ports=[{"name": "o", "type_id": 1, "kind": "output"}], payload=b""
    )
    snk = b.add_node(
        ports=[{"name": "i", "type_id": 2, "kind": "input"}], payload=b""
    )
    with pytest.raises(ValueError, match="type mismatch"):
        b.wire(src, 0, snk, 0)


def test_input_linearity():
    b = covalence.GraphBuilder()
    s1 = b.add_node(
        ports=[{"name": "o", "type_id": 1, "kind": "output"}], payload=b""
    )
    s2 = b.add_node(
        ports=[{"name": "o", "type_id": 1, "kind": "output"}], payload=b""
    )
    k = b.add_node(
        ports=[{"name": "i", "type_id": 1, "kind": "input"}], payload=b""
    )
    b.wire(s1, 0, k, 0)
    with pytest.raises(ValueError, match="already wired"):
        b.wire(s2, 0, k, 0)


def test_finish_rejects_unwired_inputs():
    b = covalence.GraphBuilder()
    b.add_node(ports=[{"name": "i", "type_id": 1, "kind": "input"}], payload=b"")
    with pytest.raises(ValueError, match="not wired"):
        b.finish()


def test_snapshot_shape():
    g = _src_snk("ordered", "pure")
    s = g.snapshot()
    assert s["version"] == 1
    assert len(s["nodes"]) == 2
    assert s["nodes"][0]["kind"] == "ordered"
    assert s["edges"][0] == {
        "from_node": 0,
        "from_port": 0,
        "to_node": 1,
        "to_port": 0,
    }


def test_bad_magic_rejected():
    with pytest.raises(ValueError, match="bad magic"):
        covalence.Graph.from_bytes(b"NOPE\x01\x00")
