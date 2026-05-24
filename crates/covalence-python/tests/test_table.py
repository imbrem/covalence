"""Tests for RowSchema, TableBuilder, and DirectoryBuilder."""

import pytest

import covalence


# ---------------------------------------------------------------------------
# RowSchema
# ---------------------------------------------------------------------------

def test_row_schema_blob_only():
    schema = covalence.RowSchema(["blob"])
    assert len(schema) == 1
    assert "blob" in repr(schema)


def test_row_schema_mixed():
    schema = covalence.RowSchema(["blob", ("ref", 1), ("dep", 1)])
    assert len(schema) == 3
    r = repr(schema)
    assert "blob" in r
    assert "ref" in r
    assert "dep" in r


def test_row_schema_empty():
    schema = covalence.RowSchema([])
    assert len(schema) == 0


def test_row_schema_bad_string():
    with pytest.raises(ValueError, match="unknown field type string"):
        covalence.RowSchema(["invalid"])


def test_row_schema_bad_tuple_type():
    with pytest.raises(ValueError, match="unknown field type"):
        covalence.RowSchema([("unknown", 1)])


def test_row_schema_bad_item_type():
    with pytest.raises(TypeError):
        covalence.RowSchema([42])


# ---------------------------------------------------------------------------
# TableBuilder — round-trip
# ---------------------------------------------------------------------------

def test_table_builder_roundtrip():
    schema = covalence.RowSchema(["blob", ("ref", 1), ("dep", 1)])
    builder = covalence.TableBuilder(schema)

    ref_hash = covalence.O256.blob(b"ref-value")
    dep_hash = covalence.O256.blob(b"dep-value")
    builder.push_ref(ref_hash)
    builder.push_dep(dep_hash)
    builder.push_row([b"hello.txt", b"\x00", b"\x00"])

    blob = builder.build()
    assert isinstance(blob, bytes)
    assert len(blob) > 0

    parsed = covalence.TableBuilder.parse(blob)
    assert parsed["num_entries"] == 1
    assert len(parsed["refs"]) >= 1
    assert len(parsed["deps"]) >= 1
    assert len(parsed["rows"]) == 1

    row = parsed["rows"][0]
    assert row[0] == b"hello.txt"


def test_table_builder_multiple_rows():
    schema = covalence.RowSchema(["blob"])
    builder = covalence.TableBuilder(schema)
    builder.push_row([b"row1"])
    builder.push_row([b"row2"])
    builder.push_row([b"row3"])

    blob = builder.build()
    parsed = covalence.TableBuilder.parse(blob)
    assert parsed["num_entries"] == 3
    names = [row[0] for row in parsed["rows"]]
    assert names == [b"row1", b"row2", b"row3"]


def test_table_builder_empty():
    schema = covalence.RowSchema(["blob"])
    builder = covalence.TableBuilder(schema)
    blob = builder.build()
    parsed = covalence.TableBuilder.parse(blob)
    assert parsed["num_entries"] == 0
    assert parsed["rows"] == []


def test_table_builder_hex_ref():
    """push_ref / push_dep accept hex strings."""
    schema = covalence.RowSchema(["blob"])
    builder = covalence.TableBuilder(schema)
    h = covalence.O256.blob(b"test")
    builder.push_ref(h.hex)
    builder.push_dep(h.hex)
    blob = builder.build()
    parsed = covalence.TableBuilder.parse(blob)
    assert len(parsed["refs"]) >= 1
    assert len(parsed["deps"]) >= 1


def test_table_builder_schema_preserved():
    """Parsed schema matches the original field specs."""
    schema = covalence.RowSchema(["blob", ("ref", 1), ("dep", 1)])
    builder = covalence.TableBuilder(schema)
    builder.push_ref(covalence.O256.blob(b"r"))
    builder.push_dep(covalence.O256.blob(b"d"))
    builder.push_row([b"data", b"\x00", b"\x00"])

    blob = builder.build()
    parsed = covalence.TableBuilder.parse(blob)
    assert parsed["schema"][0] == "blob"
    assert parsed["schema"][1][0] == "ref"
    assert parsed["schema"][2][0] == "dep"


# ---------------------------------------------------------------------------
# DirectoryBuilder — round-trip
# ---------------------------------------------------------------------------

def test_directory_builder_roundtrip():
    db = covalence.DirectoryBuilder()
    child_a = covalence.O256.blob(b"a_content")
    child_src = covalence.O256.blob(b"src_content")

    db.push("hello.txt", "blob", child_a)
    db.push("src", "dir", child_src)

    blob = db.build()
    assert isinstance(blob, bytes)
    assert len(blob) > 0

    parsed = covalence.DirectoryBuilder.parse(blob)
    assert parsed["num_entries"] == 2

    rows = parsed["rows"]
    assert len(rows) == 2

    # Check first row
    r0 = rows[0]
    assert r0["name"] == b"hello.txt"
    assert r0["mode"] == "blob"
    assert r0["child"] == child_a

    # Check second row
    r1 = rows[1]
    assert r1["name"] == b"src"
    assert r1["mode"] == "dir"
    assert r1["child"] == child_src


def test_directory_builder_empty():
    db = covalence.DirectoryBuilder()
    blob = db.build()
    parsed = covalence.DirectoryBuilder.parse(blob)
    assert parsed["num_entries"] == 0
    assert parsed["rows"] == []


def test_directory_builder_bytes_name():
    """push() accepts bytes names too."""
    db = covalence.DirectoryBuilder()
    child = covalence.O256.blob(b"data")
    db.push(b"binary-name", "blob", child)
    blob = db.build()
    parsed = covalence.DirectoryBuilder.parse(blob)
    assert parsed["rows"][0]["name"] == b"binary-name"


def test_directory_builder_hex_child():
    """push() accepts hex string for child hash."""
    db = covalence.DirectoryBuilder()
    child = covalence.O256.blob(b"data")
    db.push("file.txt", "blob", child.hex)
    blob = db.build()
    parsed = covalence.DirectoryBuilder.parse(blob)
    assert parsed["rows"][0]["child"] == child


def test_directory_builder_bad_mode():
    db = covalence.DirectoryBuilder()
    child = covalence.O256.blob(b"data")
    with pytest.raises(ValueError, match="unknown mode"):
        db.push("file.txt", "symlink", child)


def test_directory_builder_deps_are_children():
    """Each child hash appears in the deps list."""
    db = covalence.DirectoryBuilder()
    child_a = covalence.O256.blob(b"a")
    child_b = covalence.O256.blob(b"b")
    db.push("a.txt", "blob", child_a)
    db.push("b.txt", "blob", child_b)
    blob = db.build()
    parsed = covalence.DirectoryBuilder.parse(blob)
    dep_set = set(str(d) for d in parsed["deps"])
    assert str(child_a) in dep_set
    assert str(child_b) in dep_set


def test_directory_builder_many_entries():
    """Stress test with more entries."""
    db = covalence.DirectoryBuilder()
    for i in range(50):
        child = covalence.O256.blob(f"content-{i}".encode())
        mode = "dir" if i % 5 == 0 else "blob"
        db.push(f"entry-{i:03d}", mode, child)

    blob = db.build()
    parsed = covalence.DirectoryBuilder.parse(blob)
    assert parsed["num_entries"] == 50
    assert len(parsed["rows"]) == 50
