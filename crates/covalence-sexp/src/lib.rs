mod builder;
pub mod dialect;
mod parser;
mod pretty;
mod types;
mod visitor;

pub use builder::{DefaultBuilder, SExpBuilder, TreeBuilder};
pub use dialect::{CovalenceDialect, Dialect, SmtLibDialect, WatDialect};
pub use parser::parse_with;
pub use pretty::prettyprint;
pub use types::{Bytes, ParseError, SExp, StringKind};
pub use visitor::SExpVisitor;

/// Parse S-expressions using the Covalence dialect (default).
///
/// `;;` line comments, `(; ;)` block comments, `"..."` → String,
/// `b"..."` → ByteString, `|...|` quoted symbols.
pub fn parse(input: &str) -> Result<Vec<SExp>, ParseError> {
    parse_dialect(input, CovalenceDialect)
}

/// Parse S-expressions using the SMT-LIB dialect.
///
/// `;` line comments, `"..."` → String, `|...|` quoted symbols.
pub fn parse_smt(input: &str) -> Result<Vec<SExp>, ParseError> {
    parse_dialect(input, SmtLibDialect)
}

/// Parse S-expressions using the WAT dialect.
///
/// `;;` line comments, `(; ;)` block comments, `"..."` → ByteString.
pub fn parse_wat(input: &str) -> Result<Vec<SExp>, ParseError> {
    parse_dialect(input, WatDialect)
}

fn parse_dialect<D: Dialect>(input: &str, dialect: D) -> Result<Vec<SExp>, ParseError> {
    let mut visitor = TreeBuilder::new(DefaultBuilder, dialect);
    parse_with(input, &mut visitor)?;
    Ok(visitor.into_results())
}

/// Compute (line, col) from byte offset in source text (0-based).
pub fn offset_to_line_col(text: &str, offset: usize) -> (u32, u32) {
    let mut line = 0u32;
    let mut col = 0u32;
    for (i, b) in text.bytes().enumerate() {
        if i == offset {
            return (line, col);
        }
        if b == b'\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
    }
    (line, col)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(input: &str) -> String {
        let sexps = parse(input).unwrap();
        let mut buf = Vec::new();
        prettyprint(&sexps, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn parse_atom() {
        assert_eq!(parse("foo").unwrap(), vec![SExp::Atom("foo".into())]);
    }

    #[test]
    fn parse_keyword() {
        assert_eq!(parse(":key").unwrap(), vec![SExp::Atom(":key".into())]);
    }

    #[test]
    fn parse_numeral() {
        assert_eq!(parse("42").unwrap(), vec![SExp::Atom("42".into())]);
    }

    #[test]
    fn parse_string_basic() {
        assert_eq!(
            parse(r#""hello world""#).unwrap(),
            vec![SExp::String("hello world".into())]
        );
    }

    #[test]
    fn parse_string_escapes() {
        assert_eq!(
            parse(r#""a\"b\\c""#).unwrap(),
            vec![SExp::String("a\"b\\c".into())]
        );
        assert_eq!(
            parse(r#""line\nbreak""#).unwrap(),
            vec![SExp::String("line\nbreak".into())]
        );
    }

    #[test]
    fn parse_quoted_symbol_basic() {
        assert_eq!(
            parse("|hello world|").unwrap(),
            vec![SExp::QuotedSymbol("hello world".into())]
        );
    }

    #[test]
    fn parse_empty_list() {
        assert_eq!(parse("()").unwrap(), vec![SExp::List(vec![])]);
    }

    #[test]
    fn parse_simple_list() {
        assert_eq!(
            parse("(+ 1 2)").unwrap(),
            vec![SExp::List(vec![
                SExp::Atom("+".into()),
                SExp::Atom("1".into()),
                SExp::Atom("2".into()),
            ])]
        );
    }

    #[test]
    fn parse_nested_list() {
        assert_eq!(
            parse("(assert (= x 0))").unwrap(),
            vec![SExp::List(vec![
                SExp::Atom("assert".into()),
                SExp::List(vec![
                    SExp::Atom("=".into()),
                    SExp::Atom("x".into()),
                    SExp::Atom("0".into()),
                ]),
            ])]
        );
    }

    #[test]
    fn parse_comments_double_semicolon() {
        assert_eq!(
            parse(";; comment\nfoo").unwrap(),
            vec![SExp::Atom("foo".into())]
        );
        assert_eq!(
            parse("(a ;; comment\nb)").unwrap(),
            vec![SExp::List(vec![
                SExp::Atom("a".into()),
                SExp::Atom("b".into()),
            ])]
        );
    }

    #[test]
    fn parse_multiple_top_level() {
        let result = parse("(set-logic QF_LIA)\n(check-sat)").unwrap();
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn error_unclosed_paren() {
        assert!(parse("(foo").is_err());
    }

    #[test]
    fn error_unexpected_close() {
        assert!(parse(")").is_err());
    }

    #[test]
    fn error_unterminated_string() {
        assert!(parse("\"hello").is_err());
    }

    #[test]
    fn prettyprint_atom() {
        assert_eq!(fmt("foo"), "foo");
    }

    #[test]
    fn prettyprint_string() {
        assert_eq!(fmt(r#""hello""#), r#""hello""#);
    }

    #[test]
    fn prettyprint_simple_list() {
        assert_eq!(fmt("(+ 1 2)"), "(+ 1 2)");
    }

    #[test]
    fn prettyprint_nested() {
        assert_eq!(fmt("(assert (= x 0))"), "(assert (= x 0))");
    }

    #[test]
    fn prettyprint_multiple() {
        assert_eq!(
            fmt("(set-logic QF_LIA)\n(check-sat)"),
            "(set-logic QF_LIA)\n(check-sat)"
        );
    }

    #[test]
    fn prettyprint_long_list_breaks() {
        let input = "(this-is-a-very-long-command with many arguments that should definitely exceed the eighty character line width limit)";
        let output = fmt(input);
        assert!(output.contains('\n'), "long list should break: {output}");
    }

    #[test]
    fn roundtrip() {
        let inputs = [
            "(set-logic QF_LIA)",
            "(declare-fun x () Int)",
            "(assert (= (+ x 1) 2))",
            "(check-sat)",
            "(exit)",
            r#"(set-info :source "test")"#,
            "(assert (not (= |foo bar| 0)))",
        ];
        for input in inputs {
            let parsed = parse(input).unwrap();
            let mut buf = Vec::new();
            prettyprint(&parsed, &mut buf).unwrap();
            let output = String::from_utf8(buf).unwrap();
            let reparsed = parse(&output)
                .unwrap_or_else(|e| panic!("failed to reparse {input:?}: {e}\noutput: {output:?}"));
            assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
        }
    }

    #[test]
    fn offset_to_line_col_basic() {
        let text = "abc\ndef\nghi";
        assert_eq!(offset_to_line_col(text, 0), (0, 0));
        assert_eq!(offset_to_line_col(text, 3), (0, 3));
        assert_eq!(offset_to_line_col(text, 4), (1, 0));
        assert_eq!(offset_to_line_col(text, 8), (2, 0));
    }

    #[test]
    fn atom_stops_at_pipe() {
        assert_eq!(
            parse("foo|bar|").unwrap(),
            vec![SExp::Atom("foo".into()), SExp::QuotedSymbol("bar".into()),]
        );
    }

    #[test]
    fn roundtrip_control_chars() {
        let inputs = [
            r#""\a\b\f\v""#,
            r#""\n\t\r""#,
            r#""hello\"world""#,
            r#""back\\slash""#,
        ];
        for input in inputs {
            let parsed = parse(input).unwrap();
            let mut buf = Vec::new();
            prettyprint(&parsed, &mut buf).unwrap();
            let output = String::from_utf8(buf).unwrap();
            let reparsed = parse(&output)
                .unwrap_or_else(|e| panic!("failed to reparse {input:?}: {e}\noutput: {output:?}"));
            assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
        }
    }

    #[test]
    fn parse_empty() {
        assert_eq!(parse("").unwrap(), vec![]);
        assert_eq!(parse("  \n  ").unwrap(), vec![]);
        assert_eq!(parse(";; just a comment\n").unwrap(), vec![]);
    }
}
