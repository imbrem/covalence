"""Tests for TaggedStore (GitPrefixStore-backed tagged content store)."""

import covalence


# ---------------------------------------------------------------------------
# Construction
# ---------------------------------------------------------------------------


def test_memory_constructor():
    s = covalence.TaggedStore.memory()
    assert len(s) == 0


def test_git_prefix_wraps_store():
    inner = covalence.Store.memory()
    s = covalence.TaggedStore.git_prefix(inner)
    assert len(s) == 0


# ---------------------------------------------------------------------------
# Blob operations (ContentStore interface)
# ---------------------------------------------------------------------------


def test_insert_get_blob():
    s = covalence.TaggedStore.memory()
    key = s.insert(b"hello")
    assert isinstance(key, covalence.O256)
    assert s.get(key) == b"hello"


def test_put_get_blob():
    s = covalence.TaggedStore.memory()
    key = s.insert(b"data")
    # put under same key is idempotent
    s.put(key, b"data")
    assert s.get(key) == b"data"


def test_get_missing():
    s = covalence.TaggedStore.memory()
    missing = covalence.O256.blob(b"nope")
    assert s.get(missing) is None


def test_contains():
    s = covalence.TaggedStore.memory()
    key = s.insert(b"abc")
    assert s.contains(key)
    assert key in s
    missing = covalence.O256.blob(b"nope")
    assert not s.contains(missing)
    assert missing not in s


def test_len():
    s = covalence.TaggedStore.memory()
    assert len(s) == 0
    s.insert(b"a")
    assert len(s) == 1
    s.insert(b"b")
    assert len(s) == 2


def test_dedup():
    s = covalence.TaggedStore.memory()
    h1 = s.insert(b"same")
    h2 = s.insert(b"same")
    assert h1 == h2
    assert len(s) == 1


def test_get_by_hex():
    s = covalence.TaggedStore.memory()
    key = s.insert(b"hex-test")
    assert s.get(key.hex) == b"hex-test"


# ---------------------------------------------------------------------------
# Tagged operations
# ---------------------------------------------------------------------------


def test_insert_tagged_blob_matches_insert():
    s = covalence.TaggedStore.memory()
    k1 = s.insert(b"data")
    k2 = s.insert_tagged("blob", b"data")
    assert k1 == k2


def test_insert_tagged_tree():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("tree", b"tree payload")
    assert isinstance(key, covalence.O256)

    # get_repr strips header unconditionally
    assert s.get_repr(key) == b"tree payload"

    # get returns None (not a blob)
    assert s.get(key) is None


def test_insert_tagged_commit():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("commit", b"commit data")
    assert s.get_repr(key) == b"commit data"
    assert s.get(key) is None


def test_insert_tagged_tag():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("tag", b"tag data")
    assert s.get_repr(key) == b"tag data"
    assert s.get(key) is None


def test_get_tag():
    s = covalence.TaggedStore.memory()

    blob_key = s.insert(b"blob data")
    assert s.get_tag(blob_key) == "blob"

    tree_key = s.insert_tagged("tree", b"tree data")
    assert s.get_tag(tree_key) == "tree"

    commit_key = s.insert_tagged("commit", b"commit data")
    assert s.get_tag(commit_key) == "commit"


def test_get_tag_missing():
    s = covalence.TaggedStore.memory()
    missing = covalence.O256.blob(b"nope")
    assert s.get_tag(missing) is None


def test_get_repr_works_for_all_types():
    s = covalence.TaggedStore.memory()
    k_blob = s.insert(b"B")
    k_tree = s.insert_tagged("tree", b"T")
    k_tag = s.insert_tagged("tag", b"G")

    assert s.get_repr(k_blob) == b"B"
    assert s.get_repr(k_tree) == b"T"
    assert s.get_repr(k_tag) == b"G"


def test_get_repr_missing():
    s = covalence.TaggedStore.memory()
    missing = covalence.O256.blob(b"nope")
    assert s.get_repr(missing) is None


def test_different_types_different_keys():
    s = covalence.TaggedStore.memory()
    k_blob = s.insert_tagged("blob", b"same data")
    k_tree = s.insert_tagged("tree", b"same data")
    assert k_blob != k_tree


# ---------------------------------------------------------------------------
# get_repr_with / get_tag_with (type validation)
# ---------------------------------------------------------------------------


def test_get_repr_with_correct_type():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("tree", b"data")
    assert s.get_repr_with("tree", key) == b"data"


def test_get_repr_with_wrong_type():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("tree", b"data")
    assert s.get_repr_with("blob", key) is None


def test_get_tag_with_correct_type():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("commit", b"data")
    assert s.get_tag_with("commit", key) == "commit"


def test_get_tag_with_wrong_type():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("commit", b"data")
    assert s.get_tag_with("tag", key) is None


# ---------------------------------------------------------------------------
# Forward compatibility — unknown types
# ---------------------------------------------------------------------------


def test_unknown_type():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("widget", b"payload")

    assert s.get_tag(key) == "widget"
    assert s.get_repr(key) == b"payload"
    assert s.get(key) is None  # not a blob


# ---------------------------------------------------------------------------
# contains sees all types
# ---------------------------------------------------------------------------


def test_contains_sees_non_blob():
    s = covalence.TaggedStore.memory()
    key = s.insert_tagged("tree", b"tree data")
    assert s.contains(key)
    assert key in s


# ---------------------------------------------------------------------------
# Shared visibility: wrapping a Store
# ---------------------------------------------------------------------------


def test_shared_inner_store():
    """Data stored via TaggedStore's inner store is visible as prefixed bytes."""
    inner = covalence.Store.memory()
    tagged = covalence.TaggedStore.git_prefix(inner)

    # Insert via tagged store
    key = tagged.insert(b"hello")

    # Inner store sees the git-prefixed bytes
    raw = inner.get(key)
    assert raw == b"blob 5\0hello"


def test_shared_tagged_and_plain():
    """TaggedStore and inner Store share the same underlying storage."""
    inner = covalence.Store.memory()
    tagged = covalence.TaggedStore.git_prefix(inner)

    # Insert via tagged
    blob_key = tagged.insert(b"shared")
    tree_key = tagged.insert_tagged("tree", b"shared tree")

    # Both keys exist in the inner store (as prefixed data)
    assert inner.get(blob_key) is not None
    assert inner.get(tree_key) is not None

    # Inner store count matches tagged store count
    assert len(inner) == len(tagged)


# ---------------------------------------------------------------------------
# repr
# ---------------------------------------------------------------------------


def test_repr():
    s = covalence.TaggedStore.memory()
    assert "0 objects" in repr(s)
    s.insert(b"a")
    assert "1 objects" in repr(s)
