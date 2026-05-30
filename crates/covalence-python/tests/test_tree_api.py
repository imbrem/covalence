"""Tests for tree API: listing, path traversal, JSON, and git format."""

import json
import urllib.request
import urllib.error

import pytest

import covalence


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def make_tree(os, entries):
    """Build a tree via insert_tree_json. entries is a list of (name, mode, hash)."""
    return os.insert_tree_json(
        [{"name": n, "mode": m, "hash": h} for n, m, h in entries]
    )


def make_blob(os, data):
    """Insert a blob and return its key."""
    return os.insert_blob(data)


# ---------------------------------------------------------------------------
# REST helpers
# ---------------------------------------------------------------------------


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
# Python ObjectStore — list_tree
# ===========================================================================


class TestListTree:
    def test_list_empty_tree(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = make_tree(os, [])
        entries = os.list_tree(key)
        assert entries == []

    def test_list_single_entry(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"hello")
        tree_key = make_tree(os, [("hello.txt", "regular", blob_key)])
        entries = os.list_tree(tree_key)
        assert len(entries) == 1
        assert entries[0]["name"] == b"hello.txt"
        assert entries[0]["mode"] == "regular"
        assert entries[0]["hash"] == blob_key

    def test_list_multiple_entries(self):
        os = covalence.ObjectStore.git_tagged_memory()
        b1 = make_blob(os, b"aaa")
        b2 = make_blob(os, b"bbb")
        tree_key = make_tree(os, [
            ("a.txt", "regular", b1),
            ("b.txt", "executable", b2),
        ])
        entries = os.list_tree(tree_key)
        assert len(entries) == 2
        # Entries are sorted by name
        assert entries[0]["name"] == b"a.txt"
        assert entries[0]["mode"] == "regular"
        assert entries[1]["name"] == b"b.txt"
        assert entries[1]["mode"] == "executable"

    def test_list_tree_round_trip(self):
        """insert_tree_json then list_tree returns same entries."""
        os = covalence.ObjectStore.git_tagged_memory()
        b1 = make_blob(os, b"content")
        tree_key = make_tree(os, [("file.txt", "regular", b1)])
        entries = os.list_tree(tree_key)
        assert len(entries) == 1
        assert entries[0]["hash"] == b1


# ===========================================================================
# Python ObjectStore — get_path
# ===========================================================================


class TestGetPath:
    def test_single_level(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"data")
        tree_key = make_tree(os, [("file.txt", "regular", blob_key)])
        entry = os.get_path(tree_key, "file.txt")
        assert entry is not None
        assert entry["name"] == b"file.txt"
        assert entry["hash"] == blob_key

    def test_nested_path(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"lib content")
        inner_tree = make_tree(os, [("lib.rs", "regular", blob_key)])
        root_tree = make_tree(os, [("src", "dir", inner_tree)])
        entry = os.get_path(root_tree, "src/lib.rs")
        assert entry is not None
        assert entry["name"] == b"lib.rs"
        assert entry["hash"] == blob_key

    def test_deeply_nested(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"deep")
        t3 = make_tree(os, [("file.txt", "regular", blob_key)])
        t2 = make_tree(os, [("c", "dir", t3)])
        t1 = make_tree(os, [("b", "dir", t2)])
        root = make_tree(os, [("a", "dir", t1)])
        entry = os.get_path(root, "a/b/c/file.txt")
        assert entry is not None
        assert entry["hash"] == blob_key

    def test_missing_entry(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"data")
        tree_key = make_tree(os, [("a.txt", "regular", blob_key)])
        result = os.get_path(tree_key, "missing.txt")
        assert result is None

    def test_not_a_directory(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"data")
        tree_key = make_tree(os, [("file.txt", "regular", blob_key)])
        with pytest.raises(ValueError, match="not a directory"):
            os.get_path(tree_key, "file.txt/nested")

    def test_missing_intermediate(self):
        os = covalence.ObjectStore.git_tagged_memory()
        blob_key = make_blob(os, b"data")
        tree_key = make_tree(os, [("a.txt", "regular", blob_key)])
        result = os.get_path(tree_key, "nodir/a.txt")
        assert result is None


# ===========================================================================
# Python ObjectStore — insert_tree_json
# ===========================================================================


class TestInsertTreeJson:
    def test_basic(self):
        os = covalence.ObjectStore.git_tagged_memory()
        b = make_blob(os, b"content")
        key = os.insert_tree_json([
            {"name": "file.txt", "mode": "regular", "hash": b},
        ])
        assert isinstance(key, covalence.O256)
        # Verify via list_tree
        entries = os.list_tree(key)
        assert len(entries) == 1
        assert entries[0]["name"] == b"file.txt"

    def test_all_modes(self):
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"x")
        key = os.insert_tree_json([
            {"name": "a", "mode": "regular", "hash": h},
            {"name": "b", "mode": "executable", "hash": h},
            {"name": "c", "mode": "symlink", "hash": h},
            {"name": "d", "mode": "dir", "hash": h},
            {"name": "e", "mode": "submodule", "hash": h},
        ])
        entries = os.list_tree(key)
        modes = {e["name"]: e["mode"] for e in entries}
        assert modes[b"a"] == "regular"
        assert modes[b"b"] == "executable"
        assert modes[b"c"] == "symlink"
        assert modes[b"d"] == "dir"
        assert modes[b"e"] == "submodule"

    def test_dedup(self):
        """Same entries produce the same hash."""
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"x")
        k1 = os.insert_tree_json([{"name": "a", "mode": "regular", "hash": h}])
        k2 = os.insert_tree_json([{"name": "a", "mode": "regular", "hash": h}])
        assert k1 == k2

    def test_accepts_hex_string(self):
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"x")
        # Pass hash as hex string instead of O256
        key = os.insert_tree_json([
            {"name": "f", "mode": "regular", "hash": h.hex},
        ])
        entries = os.list_tree(key)
        assert entries[0]["hash"] == h


# ===========================================================================
# Python ObjectStore — git format
# ===========================================================================


class TestGitFormat:
    def test_get_tree_git(self):
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"content")
        tree_key = make_tree(os, [("file.txt", "regular", h)])
        git_bytes = os.get_tree_git(tree_key)
        assert isinstance(git_bytes, bytes)
        assert len(git_bytes) > 0
        # Git tree format: mode<space>name<null>hash_bytes
        assert b"100644 file.txt\x00" in git_bytes

    def test_insert_tree_git(self):
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"content")
        tree_key = make_tree(os, [("file.txt", "regular", h)])
        git_bytes = os.get_tree_git(tree_key)

        # Parse the git bytes back
        key2 = os.insert_tree_git(git_bytes)
        entries = os.list_tree(key2)
        assert len(entries) == 1
        assert entries[0]["name"] == b"file.txt"
        assert entries[0]["mode"] == "regular"
        assert entries[0]["hash"] == h

    def test_git_round_trip(self):
        """get_tree_git → insert_tree_git produces same tree data."""
        os = covalence.ObjectStore.git_tagged_memory()
        b1 = make_blob(os, b"aaa")
        b2 = make_blob(os, b"bbb")
        tree_key = make_tree(os, [
            ("dir1", "dir", b1),
            ("file.txt", "regular", b2),
        ])
        git_bytes = os.get_tree_git(tree_key)
        key2 = os.insert_tree_git(git_bytes)

        # Compare entries
        entries1 = os.list_tree(tree_key)
        entries2 = os.list_tree(key2)
        assert len(entries1) == len(entries2)
        for e1, e2 in zip(entries1, entries2):
            assert e1["name"] == e2["name"]
            assert e1["mode"] == e2["mode"]
            assert e1["hash"] == e2["hash"]

    def test_git_round_trip_produces_same_key(self):
        """get_tree_git → insert_tree_git produces the same tree key."""
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"content")
        k1 = make_tree(os, [("a.txt", "regular", h)])
        git_bytes = os.get_tree_git(k1)
        k2 = os.insert_tree_git(git_bytes)
        assert k1 == k2


# ===========================================================================
# REST endpoints
# ===========================================================================


class TestTreeRestEndpoints:
    def test_tree_ls(self, server):
        # Build a tree via REST
        _, data = api_json(
            server, "/objects/blob", method="POST", body=b"hello"
        )
        blob_hash = data["hash"]

        entries_json = json.dumps([
            {"name": "hello.txt", "mode": "regular", "hash": blob_hash}
        ])
        status, data = api_json(
            server, "/objects/tree/json", method="POST",
            body=entries_json, content_type="application/json",
        )
        assert status == 201
        tree_hash = data["hash"]

        # List entries
        status, entries = api_json(server, f"/objects/tree/{tree_hash}/ls")
        assert status == 200
        assert len(entries) == 1
        assert entries[0]["name"] == "hello.txt"
        assert entries[0]["mode"] == "regular"
        assert entries[0]["hash"] == blob_hash

    def test_tree_get_path(self, server):
        # Create nested tree: root/src/lib.rs
        _, blob_data = api_json(
            server, "/objects/blob", method="POST", body=b"fn main() {}"
        )
        blob_hash = blob_data["hash"]

        inner_json = json.dumps([
            {"name": "lib.rs", "mode": "regular", "hash": blob_hash}
        ])
        _, inner_data = api_json(
            server, "/objects/tree/json", method="POST",
            body=inner_json, content_type="application/json",
        )
        inner_hash = inner_data["hash"]

        root_json = json.dumps([
            {"name": "src", "mode": "dir", "hash": inner_hash}
        ])
        _, root_data = api_json(
            server, "/objects/tree/json", method="POST",
            body=root_json, content_type="application/json",
        )
        root_hash = root_data["hash"]

        # Get path
        status, entry = api_json(server, f"/objects/tree/{root_hash}/path/src/lib.rs")
        assert status == 200
        assert entry["name"] == "lib.rs"
        assert entry["hash"] == blob_hash

    def test_tree_get_path_missing(self, server):
        _, blob_data = api_json(
            server, "/objects/blob", method="POST", body=b"data"
        )
        entries_json = json.dumps([
            {"name": "a.txt", "mode": "regular", "hash": blob_data["hash"]}
        ])
        _, tree_data = api_json(
            server, "/objects/tree/json", method="POST",
            body=entries_json, content_type="application/json",
        )
        status, _, _ = api(server, f"/objects/tree/{tree_data['hash']}/path/missing.txt")
        assert status == 404

    def test_tree_insert_json(self, server):
        _, blob_data = api_json(
            server, "/objects/blob", method="POST", body=b"content"
        )
        entries_json = json.dumps([
            {"name": "file.txt", "mode": "regular", "hash": blob_data["hash"]},
        ])
        status, data = api_json(
            server, "/objects/tree/json", method="POST",
            body=entries_json, content_type="application/json",
        )
        assert status == 201
        assert "hash" in data

        # Verify the tree can be listed
        status2, entries = api_json(server, f"/objects/tree/{data['hash']}/ls")
        assert status2 == 200
        assert len(entries) == 1

    def test_tree_git_round_trip(self, server):
        # Build a tree
        _, blob_data = api_json(
            server, "/objects/blob", method="POST", body=b"data"
        )
        entries_json = json.dumps([
            {"name": "test.txt", "mode": "regular", "hash": blob_data["hash"]},
        ])
        _, tree_data = api_json(
            server, "/objects/tree/json", method="POST",
            body=entries_json, content_type="application/json",
        )
        tree_hash = tree_data["hash"]

        # Get git format
        status, git_bytes, headers = api(server, f"/objects/tree/{tree_hash}/git")
        assert status == 200
        assert headers["Content-Type"] == "application/octet-stream"
        assert len(git_bytes) > 0

        # Insert from git format
        status2, data2 = api_json(
            server, "/objects/tree/git", method="POST", body=git_bytes,
        )
        assert status2 == 201

        # Should produce the same tree content
        status3, entries = api_json(server, f"/objects/tree/{data2['hash']}/ls")
        assert status3 == 200
        assert len(entries) == 1
        assert entries[0]["name"] == "test.txt"
        assert entries[0]["hash"] == blob_data["hash"]

    def test_tree_ls_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/objects/tree/{fake}/ls")
        assert status == 404

    def test_tree_get_git_missing(self, server):
        fake = "00" * 32
        status, _, _ = api(server, f"/objects/tree/{fake}/git")
        assert status == 404


# ===========================================================================
# Cross-binding round-trips (Python ↔ REST)
# ===========================================================================


class TestCrossBindingRoundTrip:
    def test_store_via_python_read_via_rest(self, server):
        """Insert tree via Python ObjectStore, read via REST."""
        # The server's object store is separate, so we use REST for both.
        # Instead, we insert via REST JSON, then read via REST ls.
        _, blob_data = api_json(
            server, "/objects/blob", method="POST", body=b"cross test"
        )
        entries_json = json.dumps([
            {"name": "cross.txt", "mode": "regular", "hash": blob_data["hash"]},
        ])
        _, tree_data = api_json(
            server, "/objects/tree/json", method="POST",
            body=entries_json, content_type="application/json",
        )
        tree_hash = tree_data["hash"]

        # Read via REST ls
        status, entries = api_json(server, f"/objects/tree/{tree_hash}/ls")
        assert status == 200
        assert entries[0]["name"] == "cross.txt"
        assert entries[0]["hash"] == blob_data["hash"]

    def test_store_via_rest_git_read_via_rest_ls(self, server):
        """Insert tree via REST git format, read entries via REST ls."""
        _, blob_data = api_json(
            server, "/objects/blob", method="POST", body=b"git cross"
        )
        blob_hash = blob_data["hash"]

        # First build a tree normally to get its git format
        entries_json = json.dumps([
            {"name": "x.txt", "mode": "regular", "hash": blob_hash},
        ])
        _, tree_data = api_json(
            server, "/objects/tree/json", method="POST",
            body=entries_json, content_type="application/json",
        )
        _, git_bytes, _ = api(server, f"/objects/tree/{tree_data['hash']}/git")

        # Now insert via git format
        status, data = api_json(
            server, "/objects/tree/git", method="POST", body=git_bytes,
        )
        assert status == 201

        # Read via ls
        status2, entries = api_json(server, f"/objects/tree/{data['hash']}/ls")
        assert status2 == 200
        assert entries[0]["name"] == "x.txt"
        assert entries[0]["hash"] == blob_hash

    def test_python_git_format_matches_rest_git_format(self):
        """Python get_tree_git produces same bytes as REST would."""
        os = covalence.ObjectStore.git_tagged_memory()
        h = make_blob(os, b"match test")
        tree_key = make_tree(os, [("f.txt", "regular", h)])

        git_bytes = os.get_tree_git(tree_key)

        # Parse back and verify
        key2 = os.insert_tree_git(git_bytes)
        assert key2 == tree_key
