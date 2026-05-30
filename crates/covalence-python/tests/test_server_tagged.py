"""Tests for tagged store and object store REST endpoints,
plus Python binding of REST API as TaggedStore / ObjectStore."""

import json
import urllib.request
import urllib.error

import pytest

import covalence


@pytest.fixture
def server():
    with covalence.serve() as srv:
        yield srv


def api(server, path, *, method="GET", body=None, content_type=None):
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
    status, body, _ = api(server, path, **kwargs)
    return status, json.loads(body)


# ===========================================================================
# Tagged store REST endpoints
# ===========================================================================


class TestTaggedStoreREST:
    """Direct REST API tests for /api/tagged/* endpoints."""

    def test_insert_and_get_blob(self, server):
        status, data = api_json(server, "/tagged", method="POST", body=b"hello")
        assert status == 201
        h = data["hash"]
        assert len(h) == 64

        status2, body2, _ = api(server, f"/tagged/{h}")
        assert status2 == 200
        assert body2 == b"hello"

    def test_get_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/tagged/{fake}")
        assert status == 404

    def test_put_blob(self, server):
        # Insert to get a key
        status, data = api_json(server, "/tagged", method="POST", body=b"put test")
        h = data["hash"]

        # Put with same key
        status2, _, _ = api(server, f"/tagged/{h}", method="PUT", body=b"put test")
        assert status2 == 200

    def test_head_contains(self, server):
        status, data = api_json(server, "/tagged", method="POST", body=b"check")
        h = data["hash"]

        status2, _, _ = api(server, f"/tagged/{h}", method="HEAD")
        assert status2 == 200

    def test_head_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/tagged/{fake}", method="HEAD")
        assert status == 404

    def test_count(self, server):
        status, data = api_json(server, "/tagged")
        assert status == 200
        initial = data["count"]

        api(server, "/tagged", method="POST", body=b"one")
        api(server, "/tagged", method="POST", body=b"two")

        _, data2 = api_json(server, "/tagged")
        assert data2["count"] == initial + 2

    def test_insert_tagged_tree(self, server):
        status, data = api_json(
            server, "/tagged/kind/tree", method="POST", body=b"tree data"
        )
        assert status == 201
        h = data["hash"]

        # get (blob-only) should return 404 for a tree
        status2, _, _ = api(server, f"/tagged/{h}")
        assert status2 == 404

        # get_repr should return the data
        status3, body3, headers3 = api(server, f"/tagged/repr/{h}")
        assert status3 == 200
        assert body3 == b"tree data"
        assert headers3["x-object-type"] == "tree"

    def test_get_tag(self, server):
        _, data = api_json(server, "/tagged", method="POST", body=b"blob data")
        h = data["hash"]

        status, tag_data = api_json(server, f"/tagged/tag/{h}")
        assert status == 200
        assert tag_data["tag"] == "blob"

    def test_get_tag_tree(self, server):
        _, data = api_json(
            server, "/tagged/kind/tree", method="POST", body=b"tree"
        )
        h = data["hash"]

        status, tag_data = api_json(server, f"/tagged/tag/{h}")
        assert status == 200
        assert tag_data["tag"] == "tree"

    def test_get_tag_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/tagged/tag/{fake}")
        assert status == 404

    def test_get_repr_blob(self, server):
        _, data = api_json(server, "/tagged", method="POST", body=b"repr test")
        h = data["hash"]

        status, body, headers = api(server, f"/tagged/repr/{h}")
        assert status == 200
        assert body == b"repr test"
        assert headers["x-object-type"] == "blob"

    def test_different_types_different_keys(self, server):
        _, blob_data = api_json(
            server, "/tagged", method="POST", body=b"same"
        )
        _, tree_data = api_json(
            server, "/tagged/kind/tree", method="POST", body=b"same"
        )
        assert blob_data["hash"] != tree_data["hash"]


# ===========================================================================
# Object store REST endpoints
# ===========================================================================


class TestObjectStoreREST:
    """Direct REST API tests for /api/objects/* endpoints."""

    def test_insert_and_get_blob(self, server):
        status, data = api_json(
            server, "/objects/blob", method="POST", body=b"hello"
        )
        assert status == 201
        h = data["hash"]

        status2, body2, _ = api(server, f"/objects/blob/{h}")
        assert status2 == 200
        assert body2 == b"hello"

    def test_insert_and_get_tree(self, server):
        status, data = api_json(
            server, "/objects/tree", method="POST", body=b"tree bytes"
        )
        assert status == 201
        h = data["hash"]

        status2, body2, _ = api(server, f"/objects/tree/{h}")
        assert status2 == 200
        assert body2 == b"tree bytes"

    def test_kind_mismatch_tree_as_blob(self, server):
        _, data = api_json(
            server, "/objects/tree", method="POST", body=b"tree"
        )
        h = data["hash"]

        # Getting a tree key as blob → 409 Conflict (kind mismatch)
        status, _, _ = api(server, f"/objects/blob/{h}")
        assert status == 409

    def test_kind_mismatch_blob_as_tree(self, server):
        _, data = api_json(
            server, "/objects/blob", method="POST", body=b"blob"
        )
        h = data["hash"]

        status, _, _ = api(server, f"/objects/tree/{h}")
        assert status == 409

    def test_get_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/objects/blob/{fake}")
        assert status == 404

    def test_contains(self, server):
        _, data = api_json(
            server, "/objects/blob", method="POST", body=b"exists"
        )
        h = data["hash"]

        status, _, _ = api(server, f"/objects/{h}", method="HEAD")
        assert status == 200

    def test_contains_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/objects/{fake}", method="HEAD")
        assert status == 404

    def test_get_any_blob(self, server):
        _, data = api_json(
            server, "/objects/blob", method="POST", body=b"any blob"
        )
        h = data["hash"]

        status, body, headers = api(server, f"/objects/any/{h}")
        assert status == 200
        assert body == b"any blob"
        assert headers["x-object-kind"] == "blob"

    def test_get_any_tree(self, server):
        _, data = api_json(
            server, "/objects/tree", method="POST", body=b"any tree"
        )
        h = data["hash"]

        status, body, headers = api(server, f"/objects/any/{h}")
        assert status == 200
        assert body == b"any tree"
        assert headers["x-object-kind"] == "tree"

    def test_get_any_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/objects/any/{fake}")
        assert status == 404

    def test_insert_any_blob(self, server):
        status, data = api_json(
            server, "/objects/any/blob", method="POST", body=b"via any"
        )
        assert status == 201

        status2, body2, _ = api(server, f"/objects/blob/{data['hash']}")
        assert status2 == 200
        assert body2 == b"via any"

    def test_insert_any_tree(self, server):
        status, data = api_json(
            server, "/objects/any/tree", method="POST", body=b"tree via any"
        )
        assert status == 201

        status2, body2, _ = api(server, f"/objects/tree/{data['hash']}")
        assert status2 == 200
        assert body2 == b"tree via any"


# ===========================================================================
# Python binding of REST as TaggedStore
# ===========================================================================


class RestTaggedClient:
    """Python object implementing the TaggedStore protocol via HTTP."""

    def __init__(self, server):
        self.base = f"{server.url}/api/tagged"

    def _request(self, path, *, method="GET", body=None):
        url = f"{self.base}{path}"
        data = body if isinstance(body, bytes) else None
        req = urllib.request.Request(url, data=data, method=method)
        try:
            with urllib.request.urlopen(req) as resp:
                return resp.status, resp.read(), resp.headers
        except urllib.error.HTTPError as e:
            return e.code, e.read(), e.headers

    def get(self, key):
        status, body, _ = self._request(f"/{key.hex}")
        if status == 200:
            return body
        return None

    def put(self, key, data):
        self._request(f"/{key.hex}", method="PUT", body=data)

    def insert(self, data):
        status, body, _ = self._request("", method="POST", body=data)
        result = json.loads(body)
        return covalence.O256.from_hex(result["hash"])

    def contains(self, key):
        status, _, _ = self._request(f"/{key.hex}", method="HEAD")
        return status == 200

    def get_repr(self, key):
        status, body, _ = self._request(f"/repr/{key.hex}")
        if status == 200:
            return body
        return None

    def get_tag(self, key):
        status, body, _ = self._request(f"/tag/{key.hex}")
        if status == 200:
            result = json.loads(body)
            return result["tag"]
        return None

    def insert_tagged(self, kind, data):
        status, body, _ = self._request(f"/kind/{kind}", method="POST", body=data)
        result = json.loads(body)
        return covalence.O256.from_hex(result["hash"])


class TestRESTAsTaggedStore:
    """Bind a REST API as a TaggedStore and use it."""

    def test_wrap_as_tagged_store(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        assert "TaggedStore" in repr(ts)

    def test_insert_and_get_blob(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)

        key = ts.insert(b"hello REST")
        assert isinstance(key, covalence.O256)
        assert ts.get(key) == b"hello REST"

    def test_insert_tagged_and_get_repr(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)

        key = ts.insert_tagged("tree", b"tree via REST")
        assert ts.get_repr(key) == b"tree via REST"
        assert ts.get_tag(key) == "tree"

    def test_contains(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)

        key = ts.insert(b"data")
        assert key in ts

    def test_get_returns_none_for_tree(self, server):
        """TaggedStore.get (blob-only) returns None for tree objects."""
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)

        key = ts.insert_tagged("tree", b"tree data")
        assert ts.get(key) is None
        assert ts.get_repr(key) == b"tree data"


# ===========================================================================
# Python binding of REST as ObjectStore (via TaggedStore)
# ===========================================================================


class TestRESTAsObjectStore:
    """Bind REST API as TaggedStore, then wrap with ObjectStore.git_tagged."""

    def test_blob_round_trip(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_blob(b"blob via REST OS")
        assert os.get_blob(key) == b"blob via REST OS"

    def test_tree_round_trip(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_tree(b"tree via REST OS")
        assert os.get_tree(key) == b"tree via REST OS"

    def test_different_types_different_keys(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        k_blob = os.insert_blob(b"same data")
        k_tree = os.insert_tree(b"same data")
        assert k_blob != k_tree

    def test_kind_mismatch(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_tree(b"tree data")
        with pytest.raises(RuntimeError, match="mismatch"):
            os.get_blob(key)

    def test_contains(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_blob(b"data")
        assert os.contains(key)
        assert key in os

    def test_get_any(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_tree(b"tree")
        kind, data = os.get_any(key)
        assert kind == "tree"
        assert data == b"tree"

    def test_insert_any(self, server):
        client = RestTaggedClient(server)
        ts = covalence.TaggedStore(client)
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_any("blob", b"any blob")
        assert os.get_blob(key) == b"any blob"
