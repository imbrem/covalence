"""Tests for SExp and PySExp (S-expression parsing and manipulation)."""

import covalence


# ---------------------------------------------------------------------------
# Parsing — Covalence dialect
# ---------------------------------------------------------------------------

def test_parse_atom():
    result = covalence.SExp.parse("foo")
    assert len(result) == 1
    assert result[0].is_symbol()
    assert result[0].symbol_name == "foo"


def test_parse_string():
    result = covalence.SExp.parse('"hello world"')
    assert len(result) == 1
    assert result[0].is_string()
    assert result[0].string_bytes == b"hello world"
    assert result[0].string_format == ""


def test_parse_list():
    result = covalence.SExp.parse("(+ 1 2)")
    assert len(result) == 1
    assert result[0].is_list()
    assert len(result[0]) == 3
    assert result[0][0].symbol_name == "+"
    assert result[0][1].symbol_name == "1"
    assert result[0][2].symbol_name == "2"


def test_parse_format_prefix():
    result = covalence.SExp.parse('b"data"')
    assert len(result) == 1
    assert result[0].is_string()
    assert result[0].string_bytes == b"data"
    assert result[0].string_format == "b"


def test_parse_custom_format_prefix():
    result = covalence.SExp.parse('json"hello"')
    assert len(result) == 1
    assert result[0].is_string()
    assert result[0].string_bytes == b"hello"
    assert result[0].string_format == "json"


def test_parse_hex_escape():
    result = covalence.SExp.parse(r'b"\xFF\x00"')
    assert len(result) == 1
    assert result[0].string_bytes == bytes([0xFF, 0x00])


def test_parse_multiple():
    result = covalence.SExp.parse("(set-logic QF_LIA)\n(check-sat)")
    assert len(result) == 2


# ---------------------------------------------------------------------------
# Parsing — SMT-LIB dialect
# ---------------------------------------------------------------------------

def test_parse_smt():
    result = covalence.SExp.parse("; comment\nfoo", dialect="smt")
    assert len(result) == 1
    assert result[0].symbol_name == "foo"


def test_parse_smt_function():
    result = covalence.parse_sexp_smt("; comment\nfoo")
    assert len(result) == 1
    assert result[0].symbol_name == "foo"


# ---------------------------------------------------------------------------
# Parsing — WAT dialect
# ---------------------------------------------------------------------------

def test_parse_wat():
    result = covalence.SExp.parse(";; comment\n(module)", dialect="wat")
    assert len(result) == 1
    assert result[0].is_list()
    assert result[0][0].symbol_name == "module"


def test_parse_wat_function():
    result = covalence.parse_sexp_wat(";; comment\n(module)")
    assert len(result) == 1


# ---------------------------------------------------------------------------
# Constructors
# ---------------------------------------------------------------------------

def test_symbol_constructor():
    s = covalence.SExp.symbol("hello")
    assert s.is_symbol()
    assert s.symbol_name == "hello"
    assert not s.is_list()
    assert not s.is_string()


def test_string_constructor():
    s = covalence.SExp.string(b"data", format="b")
    assert s.is_string()
    assert s.string_bytes == b"data"
    assert s.string_format == "b"


def test_string_default_format():
    s = covalence.SExp.string(b"hello")
    assert s.string_format == ""


def test_list_constructor():
    lst = covalence.SExp.list([
        covalence.SExp.symbol("+"),
        covalence.SExp.symbol("1"),
        covalence.SExp.symbol("2"),
    ])
    assert lst.is_list()
    assert len(lst) == 3
    assert lst[0].symbol_name == "+"


# ---------------------------------------------------------------------------
# Accessors
# ---------------------------------------------------------------------------

def test_children():
    result = covalence.SExp.parse("(a b c)")
    children = result[0].children
    assert children is not None
    assert len(children) == 3
    assert children[0].symbol_name == "a"


def test_atom_has_no_children():
    s = covalence.SExp.symbol("x")
    assert s.children is None


def test_negative_index():
    result = covalence.SExp.parse("(a b c)")
    assert result[0][-1].symbol_name == "c"
    assert result[0][-2].symbol_name == "b"


# ---------------------------------------------------------------------------
# Pretty-printing + roundtrip
# ---------------------------------------------------------------------------

def test_prettyprint():
    s = covalence.SExp.parse("(+ 1 2)")
    assert str(s[0]) == "(+ 1 2)"


def test_prettyprint_method():
    s = covalence.SExp.symbol("hello")
    assert s.prettyprint() == "hello"


def test_roundtrip():
    inputs = [
        "(set-logic QF_LIA)",
        "(assert (= (+ x 1) 2))",
        '"hello world"',
        '(set-info :source "test")',
    ]
    for inp in inputs:
        parsed = covalence.SExp.parse(inp)
        output = parsed[0].prettyprint()
        reparsed = covalence.SExp.parse(output)
        assert parsed[0] == reparsed[0], f"roundtrip failed for {inp!r}"


# ---------------------------------------------------------------------------
# Equality
# ---------------------------------------------------------------------------

def test_equality():
    a = covalence.SExp.symbol("foo")
    b = covalence.SExp.symbol("foo")
    c = covalence.SExp.symbol("bar")
    assert a == b
    assert a != c


def test_list_equality():
    a = covalence.SExp.parse("(+ 1 2)")[0]
    b = covalence.SExp.parse("(+ 1 2)")[0]
    assert a == b


# ---------------------------------------------------------------------------
# map() — SExp → PySExp
# ---------------------------------------------------------------------------

def test_map_symbols_to_strings():
    sexp = covalence.SExp.parse("(hello world)")[0]
    result = sexp.map(lambda atom: atom.symbol_name.upper() if atom.is_symbol() else atom)
    assert result.is_list()
    assert result[0].value == "HELLO"
    assert result[1].value == "WORLD"


def test_to_py():
    sexp = covalence.SExp.parse('(hello "world")')[0]
    result = sexp.to_py()
    assert result.is_list()
    assert result[0].value == "hello"
    assert result[1].value == b"world"


# ---------------------------------------------------------------------------
# PySExp
# ---------------------------------------------------------------------------

def test_pysexp_atom():
    a = covalence.PySExp.atom(42)
    assert a.is_atom()
    assert not a.is_list()
    assert a.value == 42


def test_pysexp_list():
    lst = covalence.PySExp.list([
        covalence.PySExp.atom("x"),
        covalence.PySExp.atom("y"),
    ])
    assert lst.is_list()
    assert len(lst) == 2
    assert lst[0].value == "x"
    assert lst[1].value == "y"


def test_pysexp_children():
    lst = covalence.PySExp.list([
        covalence.PySExp.atom(1),
        covalence.PySExp.atom(2),
    ])
    children = lst.children
    assert children is not None
    assert len(children) == 2


def test_pysexp_atom_no_children():
    a = covalence.PySExp.atom("x")
    assert a.children is None
    assert a.value == "x"


def test_pysexp_map():
    lst = covalence.PySExp.list([
        covalence.PySExp.atom(1),
        covalence.PySExp.atom(2),
        covalence.PySExp.atom(3),
    ])
    doubled = lst.map(lambda x: x * 2)
    assert doubled[0].value == 2
    assert doubled[1].value == 4
    assert doubled[2].value == 6


def test_pysexp_repr():
    a = covalence.PySExp.atom(42)
    assert "42" in repr(a)


# ---------------------------------------------------------------------------
# parse_sexp / parse_sexp_smt / parse_sexp_wat functions
# ---------------------------------------------------------------------------

def test_parse_sexp_function():
    result = covalence.parse_sexp("(+ 1 2)")
    assert len(result) == 1
    assert result[0].is_list()


def test_parse_error():
    try:
        covalence.SExp.parse("(unclosed")
        assert False, "should have raised ValueError"
    except ValueError as e:
        assert "unclosed" in str(e).lower()
