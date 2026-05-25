use covalence_sexp::{SExp, parse_wat};

#[test]
fn double_semicolon_comment() {
    assert_eq!(
        parse_wat(";; comment\n(module)").unwrap(),
        vec![SExp::List(vec![SExp::symbol("module")])]
    );
}

#[test]
fn block_comment() {
    assert_eq!(
        parse_wat("(; comment ;)(module)").unwrap(),
        vec![SExp::List(vec![SExp::symbol("module")])]
    );
}

#[test]
fn string_is_bytes() {
    assert_eq!(
        parse_wat(r#""hello""#).unwrap(),
        vec![SExp::string("", b"hello".as_slice())]
    );
}

#[test]
fn dollar_ident() {
    assert_eq!(
        parse_wat("$func_name").unwrap(),
        vec![SExp::symbol("$func_name")]
    );
}

#[test]
fn no_quoted_symbols() {
    // |...| is not a quoted symbol in WAT — | is a regular atom character
    assert_eq!(parse_wat("|foo|").unwrap(), vec![SExp::symbol("|foo|")]);
}

#[test]
fn b_prefix_becomes_format() {
    // b"..." not specially handled in WAT; b becomes format prefix
    let result = parse_wat(r#"b"data""#).unwrap();
    assert_eq!(result[0], SExp::string("b", b"data".as_slice()));
}

#[test]
fn wat_module() {
    let input = "(module (func $add (param i32 i32) (result i32)))";
    let result = parse_wat(input).unwrap();
    assert_eq!(result.len(), 1);
    match &result[0] {
        SExp::List(items) => {
            assert_eq!(items[0], SExp::symbol("module"));
        }
        _ => panic!("expected list"),
    }
}

#[test]
fn nested_block_comment() {
    assert_eq!(
        parse_wat("(; outer (; nested ;) end ;)(module)").unwrap(),
        vec![SExp::List(vec![SExp::symbol("module")])]
    );
}

#[test]
fn byte_string_hex_escape() {
    // WAT strings use \hh for hex bytes
    assert_eq!(
        parse_wat(r#""\00\FF""#).unwrap(),
        vec![SExp::string("", vec![0x00, 0xFF])]
    );
}
