use covalence_sexp::{SExp, parse};

#[test]
fn unicode_atom() {
    assert_eq!(parse("λ").unwrap(), vec![SExp::Atom("λ".into())]);
    assert_eq!(parse("∀x").unwrap(), vec![SExp::Atom("∀x".into())]);
}

#[test]
fn mixed_sigils() {
    assert_eq!(
        parse("$x ^y @z").unwrap(),
        vec![
            SExp::Atom("$x".into()),
            SExp::Atom("^y".into()),
            SExp::Atom("@z".into()),
        ]
    );
}

#[test]
fn colon_keyword() {
    assert_eq!(
        parse(":status").unwrap(),
        vec![SExp::Atom(":status".into())]
    );
}

#[test]
fn operators() {
    assert_eq!(parse("+ - * /").unwrap().len(), 4);
}

#[test]
fn arrow() {
    assert_eq!(parse("->").unwrap(), vec![SExp::Atom("->".into())]);
    assert_eq!(parse("=>").unwrap(), vec![SExp::Atom("=>".into())]);
}

#[test]
fn hash_in_atom() {
    assert_eq!(parse("#t").unwrap(), vec![SExp::Atom("#t".into())]);
    assert_eq!(parse("#f").unwrap(), vec![SExp::Atom("#f".into())]);
}

#[test]
fn pipe_in_wat_atoms() {
    // In WAT dialect, | is not a delimiter so it's a regular atom char
    let result = covalence_sexp::parse_wat("|foo|").unwrap();
    assert_eq!(result, vec![SExp::Atom("|foo|".into())]);
}

#[test]
fn question_bang_atoms() {
    assert_eq!(parse("null?").unwrap(), vec![SExp::Atom("null?".into())]);
    assert_eq!(parse("set!").unwrap(), vec![SExp::Atom("set!".into())]);
}

#[test]
fn tilde_atom() {
    assert_eq!(parse("~x").unwrap(), vec![SExp::Atom("~x".into())]);
}

#[test]
fn pipe_in_quoted_symbol() {
    // Pipes can be included in quoted symbols via \| escape
    assert_eq!(
        parse(r"|a\|b|").unwrap(),
        vec![SExp::QuotedSymbol("a|b".into())]
    );
}
