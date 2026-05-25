use covalence_sexp::{SExp, parse};

#[test]
fn unicode_atom() {
    assert_eq!(parse("λ").unwrap(), vec![SExp::symbol("λ")]);
    assert_eq!(parse("∀x").unwrap(), vec![SExp::symbol("∀x")]);
}

#[test]
fn mixed_sigils() {
    assert_eq!(
        parse("$x ^y @z").unwrap(),
        vec![SExp::symbol("$x"), SExp::symbol("^y"), SExp::symbol("@z"),]
    );
}

#[test]
fn colon_keyword() {
    assert_eq!(parse(":status").unwrap(), vec![SExp::symbol(":status")]);
}

#[test]
fn operators() {
    assert_eq!(parse("+ - * /").unwrap().len(), 4);
}

#[test]
fn arrow() {
    assert_eq!(parse("->").unwrap(), vec![SExp::symbol("->")]);
    assert_eq!(parse("=>").unwrap(), vec![SExp::symbol("=>")]);
}

#[test]
fn hash_in_atom() {
    assert_eq!(parse("#t").unwrap(), vec![SExp::symbol("#t")]);
    assert_eq!(parse("#f").unwrap(), vec![SExp::symbol("#f")]);
}

#[test]
fn pipe_in_wat_atoms() {
    // In WAT dialect, | is not a delimiter so it's a regular atom char
    let result = covalence_sexp::parse_wat("|foo|").unwrap();
    assert_eq!(result, vec![SExp::symbol("|foo|")]);
}

#[test]
fn question_bang_atoms() {
    assert_eq!(parse("null?").unwrap(), vec![SExp::symbol("null?")]);
    assert_eq!(parse("set!").unwrap(), vec![SExp::symbol("set!")]);
}

#[test]
fn tilde_atom() {
    assert_eq!(parse("~x").unwrap(), vec![SExp::symbol("~x")]);
}

#[test]
fn pipe_in_quoted_symbol() {
    // Pipes can be included in quoted symbols via \| escape
    assert_eq!(parse(r"|a\|b|").unwrap(), vec![SExp::symbol("a|b")]);
}
