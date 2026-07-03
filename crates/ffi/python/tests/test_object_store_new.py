"""Tests for ObjectStore (git_tagged and keyed modes)."""

import pytest

import covalence


# ===========================================================================
# Git-tagged mode
# ===========================================================================


class TestGitTaggedMemory:
    """ObjectStore.git_tagged_memory() — git-style header-prefixed storage."""

    def test_construction(self):
        os = covalence.ObjectStore.git_tagged_memory()
        assert repr(os) == "ObjectStore(git_tagged)"

    def test_blob_round_trip(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_blob(b"hello")
        assert isinstance(key, covalence.O256)
        assert os.get_blob(key) == b"hello"

    def test_tree_round_trip(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_tree(b"tree bytes")
        assert isinstance(key, covalence.O256)
        assert os.get_tree(key) == b"tree bytes"

    def test_different_types_different_keys(self):
        os = covalence.ObjectStore.git_tagged_memory()
        k_blob = os.insert_blob(b"same data")
        k_tree = os.insert_tree(b"same data")
        assert k_blob != k_tree

    def test_kind_mismatch_tree_as_blob(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_tree(b"tree data")
        with pytest.raises(RuntimeError, match="mismatch"):
            os.get_blob(key)

    def test_kind_mismatch_blob_as_tree(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_blob(b"blob data")
        with pytest.raises(RuntimeError, match="mismatch"):
            os.get_tree(key)

    def test_get_missing_blob(self):
        os = covalence.ObjectStore.git_tagged_memory()
        missing = covalence.O256.blob(b"nope")
        assert os.get_blob(missing) is None

    def test_get_missing_tree(self):
        os = covalence.ObjectStore.git_tagged_memory()
        missing = covalence.O256.blob(b"nope")
        assert os.get_tree(missing) is None

    def test_contains(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_blob(b"data")
        assert os.contains(key)
        assert key in os
        missing = covalence.O256.blob(b"nope")
        assert not os.contains(missing)
        assert missing not in os

    def test_contains_tree(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_tree(b"tree")
        assert os.contains(key)

    def test_get_any_blob(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_blob(b"hello")
        result = os.get_any(key)
        assert result is not None
        kind, data = result
        assert kind == "blob"
        assert data == b"hello"

    def test_get_any_tree(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_tree(b"tree data")
        kind, data = os.get_any(key)
        assert kind == "tree"
        assert data == b"tree data"

    def test_get_any_missing(self):
        os = covalence.ObjectStore.git_tagged_memory()
        missing = covalence.O256.blob(b"nope")
        assert os.get_any(missing) is None

    def test_insert_any_blob(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_any("blob", b"any blob")
        assert os.get_blob(key) == b"any blob"

    def test_insert_any_tree(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_any("tree", b"any tree")
        assert os.get_tree(key) == b"any tree"

    def test_insert_any_commit(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_any("commit", b"commit data")
        kind, data = os.get_any(key)
        assert kind == "commit"
        assert data == b"commit data"

    def test_insert_any_bad_kind(self):
        os = covalence.ObjectStore.git_tagged_memory()
        with pytest.raises(RuntimeError, match="unknown"):
            os.insert_any("widget", b"data")

    def test_insert_any_matches_typed_insert(self):
        os = covalence.ObjectStore.git_tagged_memory()
        k1 = os.insert_blob(b"data")
        k2 = os.insert_any("blob", b"data")
        assert k1 == k2

    def test_get_blob_by_hex(self):
        os = covalence.ObjectStore.git_tagged_memory()
        key = os.insert_blob(b"hex test")
        assert os.get_blob(key.hex) == b"hex test"


class TestGitTaggedFromTaggedStore:
    """ObjectStore.git_tagged(tagged_store) — wrapping an existing TaggedStore."""

    def test_shared_with_tagged_store(self):
        ts = covalence.TaggedStore.memory()
        os = covalence.ObjectStore.git_tagged(ts)

        # Insert via ObjectStore
        key = os.insert_blob(b"shared")
        # Visible via TaggedStore
        assert ts.get(key) == b"shared"
        assert ts.get_tag(key) == "blob"

    def test_insert_tree_visible_in_tagged_store(self):
        ts = covalence.TaggedStore.memory()
        os = covalence.ObjectStore.git_tagged(ts)

        key = os.insert_tree(b"tree data")
        assert ts.get_repr(key) == b"tree data"
        assert ts.get_tag(key) == "tree"
        # TaggedStore.get returns None for non-blobs
        assert ts.get(key) is None


# ===========================================================================
# Keyed mode (covalence-native)
# ===========================================================================


class TestKeyedMemory:
    """ObjectStore.keyed_memory() — BLAKE3 keyed hash for trees, plain for blobs."""

    def test_construction(self):
        os = covalence.ObjectStore.keyed_memory()
        assert repr(os) == "ObjectStore(keyed)"

    def test_blob_round_trip(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_blob(b"hello")
        assert isinstance(key, covalence.O256)
        assert os.get_blob(key) == b"hello"

    def test_tree_round_trip(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_tree(b"tree bytes")
        assert isinstance(key, covalence.O256)
        assert os.get_tree(key) == b"tree bytes"

    def test_different_types_different_keys(self):
        os = covalence.ObjectStore.keyed_memory()
        k_blob = os.insert_blob(b"same data")
        k_tree = os.insert_tree(b"same data")
        assert k_blob != k_tree

    def test_blob_key_is_content_hash(self):
        """Blob keys are plain O256::blob(data) — same as Store.insert."""
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_blob(b"data")
        expected = covalence.O256.blob(b"data")
        assert key == expected

    def test_tree_key_is_keyed_hash(self):
        """Tree keys use BLAKE3 keyed hashing — different from blob keys."""
        os = covalence.ObjectStore.keyed_memory()
        blob_key = os.insert_blob(b"data")
        tree_key = os.insert_tree(b"data")
        # Tree key is keyed hash, not content hash
        assert tree_key != blob_key
        assert tree_key != covalence.O256.blob(b"data")

    def test_kind_mismatch_tree_as_blob(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_tree(b"tree data")
        with pytest.raises(RuntimeError, match="mismatch"):
            os.get_blob(key)

    def test_kind_mismatch_blob_as_tree(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_blob(b"blob data")
        with pytest.raises(RuntimeError, match="mismatch"):
            os.get_tree(key)

    def test_get_missing_blob(self):
        os = covalence.ObjectStore.keyed_memory()
        missing = covalence.O256.blob(b"nope")
        assert os.get_blob(missing) is None

    def test_get_missing_tree(self):
        os = covalence.ObjectStore.keyed_memory()
        missing = covalence.O256.blob(b"nope")
        assert os.get_tree(missing) is None

    def test_contains_blob(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_blob(b"data")
        assert os.contains(key)
        assert key in os

    def test_contains_tree(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_tree(b"tree")
        assert os.contains(key)
        assert key in os

    def test_contains_missing(self):
        os = covalence.ObjectStore.keyed_memory()
        missing = covalence.O256.blob(b"nope")
        assert not os.contains(missing)

    def test_get_any_blob(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_blob(b"hello")
        kind, data = os.get_any(key)
        assert kind == "blob"
        assert data == b"hello"

    def test_get_any_tree(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_tree(b"tree data")
        kind, data = os.get_any(key)
        assert kind == "tree"
        assert data == b"tree data"

    def test_get_any_missing(self):
        os = covalence.ObjectStore.keyed_memory()
        missing = covalence.O256.blob(b"nope")
        assert os.get_any(missing) is None

    def test_insert_any_blob(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_any("blob", b"any blob")
        assert os.get_blob(key) == b"any blob"

    def test_insert_any_tree(self):
        os = covalence.ObjectStore.keyed_memory()
        key = os.insert_any("tree", b"any tree")
        assert os.get_tree(key) == b"any tree"

    def test_insert_any_unsupported_kind(self):
        os = covalence.ObjectStore.keyed_memory()
        with pytest.raises(RuntimeError, match="unsupported"):
            os.insert_any("commit", b"data")

    def test_dedup_blob(self):
        os = covalence.ObjectStore.keyed_memory()
        k1 = os.insert_blob(b"same")
        k2 = os.insert_blob(b"same")
        assert k1 == k2

    def test_dedup_tree(self):
        os = covalence.ObjectStore.keyed_memory()
        k1 = os.insert_tree(b"same")
        k2 = os.insert_tree(b"same")
        assert k1 == k2
