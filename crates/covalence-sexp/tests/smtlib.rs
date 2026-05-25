use covalence_sexp::{SExp, parse_smt};

#[test]
fn semicolon_line_comment() {
    assert_eq!(
        parse_smt("; comment\nfoo").unwrap(),
        vec![SExp::Atom("foo".into())]
    );
}

#[test]
fn comment_in_list() {
    assert_eq!(
        parse_smt("(a ; comment\nb)").unwrap(),
        vec![SExp::List(vec![
            SExp::Atom("a".into()),
            SExp::Atom("b".into()),
        ])]
    );
}

#[test]
fn quoted_symbol() {
    assert_eq!(
        parse_smt("|hello world|").unwrap(),
        vec![SExp::QuotedSymbol("hello world".into())]
    );
}

#[test]
fn string_is_utf8() {
    assert_eq!(
        parse_smt(r#""hello""#).unwrap(),
        vec![SExp::String("hello".into())]
    );
}

#[test]
fn no_byte_prefix() {
    // b"..." is not supported in SMT-LIB; 'b' parses as atom, '"..."' as string
    let result = parse_smt(r#"b"data""#).unwrap();
    assert_eq!(result.len(), 2);
    assert_eq!(result[0], SExp::Atom("b".into()));
    assert_eq!(result[1], SExp::String("data".into()));
}

#[test]
fn empty_with_comment() {
    assert_eq!(parse_smt("").unwrap(), vec![]);
    assert_eq!(parse_smt("; just a comment\n").unwrap(), vec![]);
}

#[test]
fn no_block_comments() {
    // In SMT-LIB, (; is not a block comment: ( opens a list, ; starts a line comment
    // that consumes the rest of the line, leaving an unclosed paren.
    assert!(parse_smt("(; foo ;)").is_err());
}

#[test]
fn quoted_symbol_with_escaped_pipe() {
    assert_eq!(
        parse_smt(r#"|my\|piped\|symbol|"#).unwrap(),
        vec![SExp::QuotedSymbol("my|piped|symbol".into())]
    );
}

#[test]
fn full_smt_problem() {
    let input = "\
; Simple integer problem
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= (+ x 1) 2))
(check-sat)
(exit)";
    let result = parse_smt(input).unwrap();
    assert_eq!(result.len(), 5);
}
