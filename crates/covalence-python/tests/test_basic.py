"""Basic tests for the covalence Python bindings."""

import covalence
import tempfile
import os


# ---------------------------------------------------------------------------
# O256
# ---------------------------------------------------------------------------

def test_o256_blob():
    h = covalence.O256.blob(b"hello")
    assert len(h.hex) == 64
    # Reference: echo -n "hello" | b3sum
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


def test_o256_keyed_hash():
    key = covalence.O256.blob(b"hello")
    h = key.hash(b"world")
    # Reference: echo -n "world" | b3sum --keyed < <(echo -n "hello" | b3sum --raw)
    assert h.hex == "3cc37778d40bea3cc1de2563ec424204b0916e2d5b870d7e61f4dcb5830fa69f"


def test_o256_hash_file():
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(b"world")
        f.flush()
        path = f.name
    try:
        key = covalence.O256.blob(b"hello")
        h = key.hash_file(path)
        assert h == key.hash(b"world")
    finally:
        os.unlink(path)


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
    # Reference: echo -n "hello" | sha256sum
    assert result.hex == "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824"


def test_blake3_keyed_hasher():
    key = covalence.O256.blob(b"hello")
    h = covalence.blake3_keyed(key)
    result = h.hash(b"world")
    assert result == key.hash(b"world")


def test_blake3_kdf_hasher():
    h = covalence.blake3_kdf("covalence test")
    result = h.hash(b"hello")
    # Reference: echo -n "hello" | b3sum --derive-key "covalence test"
    assert result.hex == "dbebf5103aedc920c405537138558c171a6ae79ec591b5875029e2186951ea35"


def test_hasher_by_name():
    h = covalence.hasher("blake3")
    assert h.hash(b"hello") == covalence.blake3().hash(b"hello")
    h2 = covalence.hasher("sha256")
    assert h2.hash(b"hello") == covalence.sha256().hash(b"hello")


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


# ---------------------------------------------------------------------------
# GitHasher / GitObject
# ---------------------------------------------------------------------------

def test_git_sha1():
    h = covalence.git_sha1()
    obj = h.hash_blob(b"hello")
    assert obj.kind == "sha1"
    # Reference: echo -n "hello" | git hash-object --stdin
    assert obj.hex == "b6fc4c620b67d95f953a5c1c1230aaab5db5a1b0"


def test_git_sha256():
    h = covalence.git_sha256()
    obj = h.hash_blob(b"hello")
    assert obj.kind == "sha256"
    # Reference: echo -n "hello" | git hash-object --stdin (sha256 repo)
    assert obj.hex == "8aec4e4876f854f688d0ebfc8f37598f38e5fd6903cccc850ca36591175aeb60"


def test_git_object_str_repr():
    h = covalence.git_sha1()
    obj = h.hash_blob(b"test")
    assert str(obj) == obj.hex
    assert "GitObject" in repr(obj)


def test_git_sha256_to_o256():
    h = covalence.git_sha256()
    obj = h.hash_blob(b"hello")
    o = obj.to_o256()
    assert isinstance(o, covalence.O256)


def test_git_sha1_to_o256_raises():
    h = covalence.git_sha1()
    obj = h.hash_blob(b"hello")
    try:
        obj.to_o256()
        assert False, "should have raised"
    except ValueError:
        pass


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


def test_get_blob_hex():
    k = covalence.local()
    h = k.store_blob(b"test")
    data = k.get_blob(h.hex)
    assert data == b"test"


def test_get_blob_missing():
    k = covalence.local()
    missing = covalence.O256.blob(b"nonexistent")
    assert k.get_blob(missing) is None


def test_info():
    k = covalence.local()
    info = k.info()
    assert info["kind"] == "local"


def test_compile_wat_and_decide():
    k = covalence.local()
    # A trivial true proposition: imports attest, core module calls it at start
    wat = """
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
    h = k.compile_wat(wat)
    result = k.decide(h)
    assert result["decision"] == "true"


def test_compile_wat_false():
    k = covalence.local()
    # A component that doesn't import attest at all -> false
    wat = "(component)"
    h = k.compile_wat(wat)
    result = k.decide(h)
    assert result["decision"] == "false"


# ---------------------------------------------------------------------------
# Backend (persistent)
# ---------------------------------------------------------------------------

def test_local_persistent():
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "test.db")
        k = covalence.local_persistent(path)
        h = k.store_blob(b"persistent")
        assert k.get_blob(h) == b"persistent"
        # Verify the file was created
        assert os.path.exists(path)


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
    # Should return a hex hash
    assert len(result) == 64


# ---------------------------------------------------------------------------
# Server
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
