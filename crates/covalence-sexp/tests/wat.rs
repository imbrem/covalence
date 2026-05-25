use covalence_sexp::{Bytes, SExp, parse_wat};

#[test]
fn double_semicolon_comment() {
    assert_eq!(
        parse_wat(";; comment\n(module)").unwrap(),
        vec![SExp::List(vec![SExp::Atom("module".into())])]
    );
}

#[test]
fn block_comment() {
    assert_eq!(
        parse_wat("(; comment ;)(module)").unwrap(),
        vec![SExp::List(vec![SExp::Atom("module".into())])]
    );
}

#[test]
fn string_is_bytestring() {
    assert_eq!(
        parse_wat(r#""hello""#).unwrap(),
        vec![SExp::ByteString(Bytes::from_static(b"hello"))]
    );
}

#[test]
fn dollar_ident() {
    assert_eq!(
        parse_wat("$func_name").unwrap(),
        vec![SExp::Atom("$func_name".into())]
    );
}

#[test]
fn no_quoted_symbols() {
    // |...| is not a quoted symbol in WAT — | is a regular atom character
    assert_eq!(
        parse_wat("|foo|").unwrap(),
        vec![SExp::Atom("|foo|".into())]
    );
}

#[test]
fn no_byte_prefix() {
    // b"..." not supported in WAT; b is an atom, "data" is a bytestring
    let result = parse_wat(r#"b"data""#).unwrap();
    assert_eq!(result[0], SExp::Atom("b".into()));
    assert_eq!(result[1], SExp::ByteString(Bytes::from_static(b"data")));
}

#[test]
fn wat_module() {
    let input = "(module (func $add (param i32 i32) (result i32)))";
    let result = parse_wat(input).unwrap();
    assert_eq!(result.len(), 1);
    match &result[0] {
        SExp::List(items) => {
            assert_eq!(items[0], SExp::Atom("module".into()));
        }
        _ => panic!("expected list"),
    }
}

#[test]
fn nested_block_comment() {
    assert_eq!(
        parse_wat("(; outer (; nested ;) end ;)(module)").unwrap(),
        vec![SExp::List(vec![SExp::Atom("module".into())])]
    );
}

#[test]
fn byte_string_hex_escape() {
    // WAT strings use \hh for hex bytes
    assert_eq!(
        parse_wat(r#""\00\FF""#).unwrap(),
        vec![SExp::ByteString(Bytes::from_static(&[0x00, 0xFF]))]
    );
}
