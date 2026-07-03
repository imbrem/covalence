"""End-to-end Python tests for the wasm_store bindings.

Mirrors the Rust integration tests so a Python user can drive every
example (single_blob leaf, merge composer, s3_path composer) from
the REPL or a script.
"""

import pytest

from covalence import wasm_store as ws


# ---------------------------------------------------------------------------
# Leaf — single_blob
# ---------------------------------------------------------------------------

def test_single_blob_round_trip():
    key = b"any-key-bytes"
    blob = b"the stored value"
    leaf_bytes = ws.build_single_blob(key, blob)
    leaf = ws.WasmStore.from_bytes(leaf_bytes)

    assert leaf.get(key) == blob
    assert leaf.contains(key)
    assert leaf.head(key) == len(blob)


def test_single_blob_miss_raises_keyerror():
    leaf_bytes = ws.build_single_blob(b"alpha", b"value")
    leaf = ws.WasmStore.from_bytes(leaf_bytes)

    with pytest.raises(KeyError):
        leaf.get(b"beta")
    assert leaf.try_get(b"beta") is None
    assert not leaf.contains(b"beta")
    assert leaf.head(b"beta") is None


# ---------------------------------------------------------------------------
# Composer — merge
# ---------------------------------------------------------------------------

def test_merge_composer_first_hit_wins():
    alpha = ws.WasmStore.from_bytes(ws.build_single_blob(b"k1", b"alpha-val"))
    beta = ws.WasmStore.from_bytes(ws.build_single_blob(b"k2", b"beta-val"))

    merger = ws.WasmStore.compose(ws.build_merge_composer(), [alpha, beta])

    assert merger.get(b"k1") == b"alpha-val"
    assert merger.get(b"k2") == b"beta-val"
    assert merger.contains(b"k1")
    assert merger.contains(b"k2")
    assert not merger.contains(b"k3")


# ---------------------------------------------------------------------------
# Composer — s3_path
# ---------------------------------------------------------------------------

def test_s3_path_routes_prefix_plus_hex():
    """Mirrors `s3_path_get_routes_through_prefix_plus_hex` in Rust.

    The backing leaf is keyed on the *encoded path* the composer
    will construct; the composer turns the caller's raw key
    `bytes.fromhex("abcdef12")` into `b"blobs/abcdef12"` and looks
    that up in the upstream.
    """
    prefix = "blobs/"
    key = bytes.fromhex("abcdef12")
    blob = b"the stored blob"

    # Same as Rust's build_path_keyed_leaf helper.
    path = (prefix + ws.hex_encode(key)).encode()
    backing = ws.WasmStore.from_bytes(ws.build_single_blob(path, blob))

    composer = ws.WasmStore.compose(
        ws.build_s3_path_composer(prefix),
        [backing],
    )

    assert composer.get(key) == blob
    assert composer.contains(key)
    assert composer.head(key) == len(blob)

    # Wrong key misses.
    with pytest.raises(KeyError):
        composer.get(bytes.fromhex("deadbeef"))


def test_s3_path_different_prefix_different_path():
    """Confirms the prefix actually shapes the path."""
    key = b"\x12\x34"
    wrong_path = (b"other/" + ws.hex_encode(key).encode())
    backing = ws.WasmStore.from_bytes(
        ws.build_single_blob(wrong_path, b"wrong-prefix data")
    )

    composer = ws.WasmStore.compose(
        ws.build_s3_path_composer("blobs/"),
        [backing],
    )

    with pytest.raises(KeyError):
        composer.get(key)


def test_s3_path_prefix_pinned_in_component_hash():
    """Different prefix ⇒ different component binary.

    Sanity-checks the identity contract from inside Python.
    """
    a = ws.build_s3_path_composer("a/")
    b = ws.build_s3_path_composer("b/")
    assert a != b


def test_hex_encode():
    assert ws.hex_encode(b"") == ""
    assert ws.hex_encode(b"\x00\xab\xff") == "00abff"


# ---------------------------------------------------------------------------
# Kv-backed adapter
# ---------------------------------------------------------------------------

def test_kv_backed_composer():
    """Drives an s3_path composer with a KvStore backing.

    Same as the s3_path test above, but the backing is a real
    `MemoryKvStore` rather than a `single_blob` leaf. This is the
    exact glue you'd use against R2 — swap `MemoryKvStore` for
    `S3KvStore(endpoint=..., access_key_id=..., ...)`.
    """
    import covalence

    prefix = "blobs/"
    key = bytes.fromhex("c0ffeebabe")
    blob = b"the stored blob"

    # 1) Build a kv backing and pre-populate it as if we'd uploaded
    #    via S3 with `kv.put(path, blob)`.
    kv = covalence.MemoryKvStore()
    path = prefix + ws.hex_encode(key)
    kv.put(path, blob)

    # 2) Wrap the kv as a WasmStore backing.
    backing = ws.WasmStore.from_kv(kv)

    # 3) Compose the s3_path composer over it.
    composer = ws.WasmStore.compose(
        ws.build_s3_path_composer(prefix),
        [backing],
    )

    # 4) The composer turns key -> b"blobs/c0ffeebabe" -> kv.get -> blob.
    assert composer.get(key) == blob
    assert composer.contains(key)
    assert composer.head(key) == len(blob)

    with pytest.raises(KeyError):
        composer.get(bytes.fromhex("deadbeef"))


def test_kv_backed_directly_as_store():
    """A kv-backed WasmStore is itself a valid store — no composer needed.

    Useful for talking to a kv-shaped backend without the prefix +
    hex routing.
    """
    import covalence

    kv = covalence.MemoryKvStore()
    kv.put("greeting", b"hello world")

    store = ws.WasmStore.from_kv(kv)

    assert store.get(b"greeting") == b"hello world"
    assert store.contains(b"greeting")
    assert store.head(b"greeting") == len(b"hello world")
    assert store.try_get(b"missing") is None
