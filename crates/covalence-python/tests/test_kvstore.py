"""Tests for KvStore + backend subclasses."""

import pytest

import covalence


# ---------------------------------------------------------------------------
# Base class
# ---------------------------------------------------------------------------

def test_base_class_is_abstract():
    with pytest.raises(TypeError, match="abstract"):
        covalence.KvStore()


# ---------------------------------------------------------------------------
# MemoryKvStore
# ---------------------------------------------------------------------------

def test_memory_subclass_of_kvstore():
    kv = covalence.MemoryKvStore()
    assert isinstance(kv, covalence.KvStore)
    assert isinstance(kv, covalence.MemoryKvStore)


def test_memory_put_get():
    kv = covalence.MemoryKvStore()
    kv.put("foo/bar", b"hello")
    assert kv.get("foo/bar") == b"hello"


def test_memory_get_missing_raises_keyerror():
    kv = covalence.MemoryKvStore()
    with pytest.raises(KeyError):
        kv.get("nope")


def test_memory_overwrite():
    kv = covalence.MemoryKvStore()
    kv.put("k", b"v1")
    kv.put("k", b"v2")
    assert kv.get("k") == b"v2"


def test_memory_delete():
    kv = covalence.MemoryKvStore()
    kv.put("k", b"v")
    kv.delete("k")
    with pytest.raises(KeyError):
        kv.get("k")


def test_memory_delete_missing_idempotent():
    kv = covalence.MemoryKvStore()
    kv.delete("never-existed")  # must not raise


def test_memory_head():
    kv = covalence.MemoryKvStore()
    kv.put("k", b"hello")
    meta = kv.head("k")
    assert meta["size"] == 5
    assert meta["etag"] is None


def test_memory_head_missing_raises_keyerror():
    kv = covalence.MemoryKvStore()
    with pytest.raises(KeyError):
        kv.head("nope")


def test_memory_get_range_default_impl():
    kv = covalence.MemoryKvStore()
    kv.put("data", b"0123456789")
    assert kv.get_range("data", 2, 7) == b"23456"


def test_memory_get_range_out_of_bounds():
    kv = covalence.MemoryKvStore()
    kv.put("data", b"short")
    with pytest.raises(ValueError, match="out of bounds"):
        kv.get_range("data", 0, 999)


# ---------------------------------------------------------------------------
# AwsKvStore / S3KvStore — construction only (no network in tests)
# ---------------------------------------------------------------------------

def test_aws_constructor_returns_kvstore_subclass():
    kv = covalence.AwsKvStore("my-bucket", "us-east-1")
    assert isinstance(kv, covalence.KvStore)
    assert isinstance(kv, covalence.AwsKvStore)
    # No I/O calls — operations would fail without real creds, but the
    # object is well-formed.


def test_s3_constructor_returns_kvstore_subclass():
    kv = covalence.S3KvStore(
        endpoint="http://127.0.0.1:1",
        region="us-east-1",
        bucket="my-bucket",
        access_key_id="AKIAEXAMPLE",
        secret_access_key="secret",
        allow_http=True,
    )
    assert isinstance(kv, covalence.KvStore)
    assert isinstance(kv, covalence.S3KvStore)
