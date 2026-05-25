use covalence_sexp::{SExp, parse};

#[test]
fn dollar_sigil() {
    assert_eq!(parse("$x").unwrap(), vec![SExp::Atom("$x".into())]);
}

#[test]
fn caret_sigil() {
    assert_eq!(parse("^y").unwrap(), vec![SExp::Atom("^y".into())]);
}

#[test]
fn quote_sigil() {
    assert_eq!(parse("'q").unwrap(), vec![SExp::Atom("'q".into())]);
}

#[test]
fn at_sign() {
    assert_eq!(
        parse("@custom").unwrap(),
        vec![SExp::Atom("@custom".into())]
    );
}

#[test]
fn sigils_in_list() {
    assert_eq!(
        parse("($push ^pop 'quote)").unwrap(),
        vec![SExp::List(vec![
            SExp::Atom("$push".into()),
            SExp::Atom("^pop".into()),
            SExp::Atom("'quote".into()),
        ])]
    );
}

#[test]
fn arrow_atom() {
    assert_eq!(parse("->").unwrap(), vec![SExp::Atom("->".into())]);
}

#[test]
fn plus_atom() {
    assert_eq!(parse("+").unwrap(), vec![SExp::Atom("+".into())]);
}
