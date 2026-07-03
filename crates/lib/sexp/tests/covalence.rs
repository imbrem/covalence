use covalence_sexp::{SExp, parse};

#[test]
fn double_semicolon_line_comment() {
    assert_eq!(parse(";; comment\nfoo").unwrap(), vec![SExp::symbol("foo")]);
}

#[test]
fn block_comment() {
    assert_eq!(
        parse("(; block comment ;) foo").unwrap(),
        vec![SExp::symbol("foo")]
    );
}

#[test]
fn nested_block_comment() {
    assert_eq!(
        parse("(; outer (; inner ;) still outer ;) foo").unwrap(),
        vec![SExp::symbol("foo")]
    );
}

#[test]
fn block_comment_in_list() {
    assert_eq!(
        parse("(a (;comment;) b)").unwrap(),
        vec![SExp::List(vec![SExp::symbol("a"), SExp::symbol("b"),])]
    );
}

#[test]
fn bare_string_is_bytes() {
    assert_eq!(
        parse(r#""hello""#).unwrap(),
        vec![SExp::string("", b"hello".as_slice())]
    );
}

#[test]
fn byte_prefix_string() {
    assert_eq!(
        parse(r#"b"data""#).unwrap(),
        vec![SExp::string("b", b"data".as_slice())]
    );
}

#[test]
fn byte_string_hex_x_escape() {
    assert_eq!(
        parse(r#"b"\xFF\x00""#).unwrap(),
        vec![SExp::string("b", vec![0xFF, 0x00])]
    );
}

#[test]
fn byte_string_direct_hex() {
    assert_eq!(
        parse(r#"b"\FF\00""#).unwrap(),
        vec![SExp::string("b", vec![0xFF, 0x00])]
    );
}

#[test]
fn quoted_symbol_with_pipes() {
    assert_eq!(
        parse(r#"|my\|piped\|symbol|"#).unwrap(),
        vec![SExp::symbol("my|piped|symbol")]
    );
}

#[test]
fn quoted_symbol_with_escaped_backslash() {
    assert_eq!(
        parse(r#"|back\\slash|"#).unwrap(),
        vec![SExp::symbol("back\\slash")]
    );
}

#[test]
fn single_semicolon_not_comment() {
    // In Covalence, ; alone is NOT a comment start — it's an atom delimiter
    // but not a valid token start, so it's a parse error.
    assert!(parse(";foo").is_err());
}

#[test]
fn semicolon_stops_atom() {
    // ; is always an atom delimiter, so foo;;comment parses correctly
    assert_eq!(
        parse("foo;;comment\nbar").unwrap(),
        vec![SExp::symbol("foo"), SExp::symbol("bar")]
    );
}

#[test]
fn block_comment_multiline() {
    let input = "(;\n  This is a\n  multi-line\n  block comment\n;)\n(ok)";
    let result = parse(input).unwrap();
    assert_eq!(result, vec![SExp::List(vec![SExp::symbol("ok")])]);
}

#[test]
fn covalence_superset_of_smt() {
    // These expressions are valid in both Covalence and SMT-LIB
    let inputs = [
        "(set-logic QF_LIA)",
        "(declare-fun x () Int)",
        "(assert (= (+ x 1) 2))",
        r#"(set-info :source "test")"#,
        "|quoted symbol|",
    ];
    for input in inputs {
        assert!(parse(input).is_ok(), "failed to parse: {input}");
    }
}

#[test]
fn format_prefix_custom() {
    // Any atom before " becomes a format prefix
    assert_eq!(
        parse(r#"json"hello""#).unwrap(),
        vec![SExp::string("json", b"hello".as_slice())]
    );
}
