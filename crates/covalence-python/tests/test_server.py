"""Tests for the embedded HTTP server (TCP-based)."""

import json
import os
import tempfile
import urllib.request
import urllib.error

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


@pytest.fixture
def server():
    with covalence.serve() as srv:
        yield srv


def api(server, path, *, method="GET", body=None, content_type=None):
    """Helper: make an HTTP request to the server."""
    url = f"{server.url}/api{path}"
    data = None
    if body is not None:
        data = body if isinstance(body, bytes) else body.encode()
    req = urllib.request.Request(url, data=data, method=method)
    if content_type:
        req.add_header("Content-Type", content_type)
    try:
        with urllib.request.urlopen(req) as resp:
            return resp.status, resp.read(), resp.headers
    except urllib.error.HTTPError as e:
        return e.code, e.read(), e.headers


def api_json(server, path, **kwargs):
    """Helper: make request, parse JSON response."""
    status, body, _ = api(server, path, **kwargs)
    return status, json.loads(body)


# ---------------------------------------------------------------------------
# Server lifecycle
# ---------------------------------------------------------------------------

def test_serve_and_stop():
    srv = covalence.serve()
    assert srv.port > 0
    assert "127.0.0.1" in srv.url
    srv.stop()


def test_serve_context_manager():
    with covalence.serve() as srv:
        assert srv.port > 0


def test_serve_with_sqlite():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "srv.db")
        with covalence.serve(store=path) as srv:
            assert srv.port > 0


def test_serve_ephemeral_port():
    """port=0 should pick a random available port."""
    with covalence.serve(port=0) as s1, covalence.serve(port=0) as s2:
        assert s1.port != s2.port


def test_stop_idempotent():
    srv = covalence.serve()
    srv.stop()
    srv.stop()  # should not raise


# ---------------------------------------------------------------------------
# /api/info + /api/health
# ---------------------------------------------------------------------------

def test_info(server):
    status, data = api_json(server, "/info")
    assert status == 200
    assert data["target"] == "covalence-python"
    assert "version" in data


def test_health(server):
    status, data = api_json(server, "/health")
    assert status == 200
    assert data["status"] == "ok"
    assert data["uptime_secs"] >= 0


# ---------------------------------------------------------------------------
# /api/blobs — store and retrieve
# ---------------------------------------------------------------------------

def test_store_and_get_blob(server):
    payload = b"hello from python"
    status, data = api_json(server, "/blobs", method="POST", body=payload)
    assert status == 201
    h = data["hash"]
    assert len(h) == 64

    status2, body2, headers = api(server, f"/blobs/{h}")
    assert status2 == 200
    assert body2 == payload
    assert headers["Content-Type"] == "application/octet-stream"


def test_get_blob_missing(server):
    fake = "00" * 32
    status, _, _ = api(server, f"/blobs/{fake}")
    assert status == 404


def test_head_blob(server):
    status, data = api_json(server, "/blobs", method="POST", body=b"head check")
    h = data["hash"]

    status2, body, _ = api(server, f"/blobs/{h}", method="HEAD")
    assert status2 == 200
    assert body == b""  # HEAD has no body


def test_head_blob_missing(server):
    fake = "00" * 32
    status, _, _ = api(server, f"/blobs/{fake}", method="HEAD")
    assert status == 404


def test_blob_count(server):
    status, data = api_json(server, "/blobs")
    assert status == 200
    initial = data["count"]

    api(server, "/blobs", method="POST", body=b"blob1")
    api(server, "/blobs", method="POST", body=b"blob2")

    status2, data2 = api_json(server, "/blobs")
    assert data2["count"] == initial + 2


def test_store_blob_deduplication(server):
    api(server, "/blobs", method="POST", body=b"same content")
    _, before = api_json(server, "/blobs")
    api(server, "/blobs", method="POST", body=b"same content")
    _, after = api_json(server, "/blobs")
    assert before["count"] == after["count"]


def test_store_empty_blob(server):
    status, data = api_json(server, "/blobs", method="POST", body=b"")
    assert status == 201
    h = data["hash"]
    status2, body2, _ = api(server, f"/blobs/{h}")
    assert body2 == b""


def test_store_large_blob(server):
    payload = os.urandom(256 * 1024)  # 256 KiB
    status, data = api_json(server, "/blobs", method="POST", body=payload)
    assert status == 201
    status2, body2, _ = api(server, f"/blobs/{data['hash']}")
    assert body2 == payload


def test_store_blob_from_file(server):
    with tempfile.NamedTemporaryFile(delete=False, suffix=".txt") as f:
        f.write(b"file content")
        f.flush()
        path = f.name
    try:
        body = json.dumps({"path": path}).encode()
        status, data = api_json(
            server, "/blobs/file", method="POST", body=body,
            content_type="application/json",
        )
        assert status == 201
        status2, body2, _ = api(server, f"/blobs/{data['hash']}")
        assert body2 == b"file content"
    finally:
        os.unlink(path)


# ---------------------------------------------------------------------------
# /api/eval — stateless REPL
# ---------------------------------------------------------------------------

def test_eval(server):
    status, body, headers = api(
        server, "/eval", method="POST", body="(status)",
        content_type="text/plain",
    )
    assert status == 200
    assert b"local" in body


def test_eval_store(server):
    status, body, _ = api(
        server, "/eval", method="POST", body='(store "via eval")',
        content_type="text/plain",
    )
    assert status == 200
    h = body.decode().strip()
    assert len(h) == 64


# ---------------------------------------------------------------------------
# /api/decide — proposition deciding
# ---------------------------------------------------------------------------

def test_decide_true(server):
    # First store the component via the blob API (compile WAT locally)
    k = covalence.local()
    wasm_hash = k.compile_wat(TRIVIAL_TRUE)
    wasm_bytes = k.get_blob(wasm_hash)

    # Store the compiled WASM in the server
    status, data = api_json(server, "/blobs", method="POST", body=wasm_bytes)
    assert status == 201
    h = data["hash"]

    # Decide
    status2, result = api_json(server, f"/decide/{h}")
    assert status2 == 200
    assert result["result"] == "sat"
    assert isinstance(result["proved"], list)


def test_decide_false(server):
    k = covalence.local()
    wasm_hash = k.compile_wat("(component)")
    wasm_bytes = k.get_blob(wasm_hash)

    status, data = api_json(server, "/blobs", method="POST", body=wasm_bytes)
    h = data["hash"]

    status2, result = api_json(server, f"/decide/{h}")
    assert status2 == 200
    assert result["result"] == "unsat"


def test_decide_bad_hash(server):
    status, _, _ = api(server, "/decide/not-a-hash")
    assert status == 400


# ---------------------------------------------------------------------------
# Persistence across requests
# ---------------------------------------------------------------------------

def test_server_state_persists(server):
    """Data stored via one request is visible to subsequent requests."""
    api(server, "/blobs", method="POST", body=b"first")
    _, d1 = api_json(server, "/blobs")
    api(server, "/blobs", method="POST", body=b"second")
    _, d2 = api_json(server, "/blobs")
    assert d2["count"] == d1["count"] + 1


def test_server_sqlite_persistence():
    """SQLite-backed server persists data across restarts."""
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "persist.db")

        with covalence.serve(store=path) as srv:
            status, data = api_json(srv, "/blobs", method="POST", body=b"persist me")
            h = data["hash"]

        # Restart with same DB
        with covalence.serve(store=path) as srv:
            status, body, _ = api(srv, f"/blobs/{h}")
            assert status == 200
            assert body == b"persist me"


# ---------------------------------------------------------------------------
# Multi-server isolation
# ---------------------------------------------------------------------------

def test_multi_server_isolation():
    """Two concurrent servers have independent stores."""
    with covalence.serve() as srv_a, covalence.serve() as srv_b:
        assert srv_a.port != srv_b.port

        # Store in A, absent from B
        status, data = api_json(srv_a, "/blobs", method="POST", body=b"only in A")
        h_a = data["hash"]
        assert status == 201

        status_b, _, _ = api(srv_b, f"/blobs/{h_a}")
        assert status_b == 404

        # Store in B, absent from A
        status, data = api_json(srv_b, "/blobs", method="POST", body=b"only in B")
        h_b = data["hash"]
        assert status == 201

        status_a, _, _ = api(srv_a, f"/blobs/{h_b}")
        assert status_a == 404

        # Each server still has its own data
        status_a2, body_a, _ = api(srv_a, f"/blobs/{h_a}")
        assert status_a2 == 200
        assert body_a == b"only in A"

        status_b2, body_b, _ = api(srv_b, f"/blobs/{h_b}")
        assert status_b2 == 200
        assert body_b == b"only in B"


def test_multi_server_independent_decide():
    """Two concurrent servers can decide propositions independently."""
    k = covalence.local()
    wasm_true = k.get_blob(k.compile_wat(TRIVIAL_TRUE))
    wasm_false = k.get_blob(k.compile_wat("(component)"))

    with covalence.serve() as srv_a, covalence.serve() as srv_b:
        # Store true prop in A, false prop in B
        _, data_a = api_json(srv_a, "/blobs", method="POST", body=wasm_true)
        _, data_b = api_json(srv_b, "/blobs", method="POST", body=wasm_false)

        _, result_a = api_json(srv_a, f"/decide/{data_a['hash']}")
        assert result_a["result"] == "sat"

        _, result_b = api_json(srv_b, f"/decide/{data_b['hash']}")
        assert result_b["result"] == "unsat"
