use covalence_sexp::{SExp, parse};

#[test]
fn dollar_sigil() {
    assert_eq!(parse("$x").unwrap(), vec![SExp::symbol("$x")]);
}

#[test]
fn caret_sigil() {
    assert_eq!(parse("^y").unwrap(), vec![SExp::symbol("^y")]);
}

#[test]
fn quote_sigil() {
    assert_eq!(parse("'q").unwrap(), vec![SExp::symbol("'q")]);
}

#[test]
fn at_sign() {
    assert_eq!(parse("@custom").unwrap(), vec![SExp::symbol("@custom")]);
}

#[test]
fn sigils_in_list() {
    assert_eq!(
        parse("($push ^pop 'quote)").unwrap(),
        vec![SExp::List(vec![
            SExp::symbol("$push"),
            SExp::symbol("^pop"),
            SExp::symbol("'quote"),
        ])]
    );
}

#[test]
fn arrow_atom() {
    assert_eq!(parse("->").unwrap(), vec![SExp::symbol("->")]);
}

#[test]
fn plus_atom() {
    assert_eq!(parse("+").unwrap(), vec![SExp::symbol("+")]);
}
