mod builder;
pub mod dialect;
mod parser;
mod pretty;
mod types;
mod visitor;

pub use builder::{DefaultBuilder, SExpBuilder, TreeBuilder};
pub use dialect::{CovalenceDialect, Dialect, EgglogDialect, SmtLibDialect, WatDialect};
pub use parser::{parse_prefix_with, parse_with};
pub use pretty::prettyprint;
pub use types::{Atom, Bytes, ParseError, SExp, SExpr};
pub use visitor::SExpVisitor;

/// Parse S-expressions using the Covalence dialect (default).
///
/// `;;` line comments, `(; ;)` block comments, `"..."` → Str(format=""),
/// `b"..."` → Str(format="b"), `|...|` quoted symbols.
pub fn parse(input: &str) -> Result<Vec<SExpr>, ParseError> {
    parse_dialect(input, CovalenceDialect)
}

/// Parse one Covalence-dialect S-expression, returning it and the byte offset
/// immediately after the value.
pub fn parse_prefix(input: &str) -> Result<(SExpr, usize), ParseError> {
    let mut visitor = TreeBuilder::new(DefaultBuilder, CovalenceDialect);
    let consumed = parse_prefix_with(input, &mut visitor)?;
    let mut results = visitor.into_results();
    debug_assert_eq!(results.len(), 1);
    Ok((results.remove(0), consumed))
}

/// Parse S-expressions using the SMT-LIB dialect.
///
/// `;` line comments, `"..."` → Str(format=""), `|...|` quoted symbols.
pub fn parse_smt(input: &str) -> Result<Vec<SExpr>, ParseError> {
    parse_dialect(input, SmtLibDialect)
}

/// Parse S-expressions using the WAT dialect.
///
/// `;;` line comments, `(; ;)` block comments, `"..."` → Str(format="").
pub fn parse_wat(input: &str) -> Result<Vec<SExpr>, ParseError> {
    parse_dialect(input, WatDialect)
}

/// Parse S-expressions using the egglog dialect.
///
/// `;` line comments, `"..."` → Str(format=""), no `|…|` quoted symbols.
/// See [`EgglogDialect`] for details.
pub fn parse_egglog(input: &str) -> Result<Vec<SExpr>, ParseError> {
    parse_dialect(input, EgglogDialect)
}

fn parse_dialect<D: Dialect>(input: &str, dialect: D) -> Result<Vec<SExpr>, ParseError> {
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
        assert_eq!(parse("foo").unwrap(), vec![SExp::symbol("foo")]);
    }

    #[test]
    fn parse_keyword() {
        assert_eq!(parse(":key").unwrap(), vec![SExp::symbol(":key")]);
    }

    #[test]
    fn parse_numeral() {
        assert_eq!(parse("42").unwrap(), vec![SExp::symbol("42")]);
    }

    #[test]
    fn parse_string_basic() {
        assert_eq!(
            parse(r#""hello world""#).unwrap(),
            vec![SExp::string("", b"hello world".as_slice())]
        );
    }

    #[test]
    fn parse_string_escapes() {
        assert_eq!(
            parse(r#""a\"b\\c""#).unwrap(),
            vec![SExp::string("", b"a\"b\\c".as_slice())]
        );
        assert_eq!(
            parse(r#""line\nbreak""#).unwrap(),
            vec![SExp::string("", b"line\nbreak".as_slice())]
        );
    }

    #[test]
    fn parse_quoted_symbol_basic() {
        // Quoted symbols are now folded into Symbol
        assert_eq!(
            parse("|hello world|").unwrap(),
            vec![SExp::symbol("hello world")]
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
                SExp::symbol("+"),
                SExp::symbol("1"),
                SExp::symbol("2"),
            ])]
        );
    }

    #[test]
    fn parse_nested_list() {
        assert_eq!(
            parse("(assert (= x 0))").unwrap(),
            vec![SExp::List(vec![
                SExp::symbol("assert"),
                SExp::List(vec![
                    SExp::symbol("="),
                    SExp::symbol("x"),
                    SExp::symbol("0"),
                ]),
            ])]
        );
    }

    #[test]
    fn parse_comments_double_semicolon() {
        assert_eq!(parse(";; comment\nfoo").unwrap(), vec![SExp::symbol("foo")]);
        assert_eq!(
            parse("(a ;; comment\nb)").unwrap(),
            vec![SExp::List(vec![SExp::symbol("a"), SExp::symbol("b"),])]
        );
    }

    #[test]
    fn parse_multiple_top_level() {
        let result = parse("(set-logic QF_LIA)\n(check-sat)").unwrap();
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn parse_prefix_stops_before_trailing_source() {
        let (value, consumed) = parse_prefix("  (a (b c)) tail").unwrap();
        assert_eq!(
            value,
            SExp::List(vec![
                SExp::symbol("a"),
                SExp::List(vec![SExp::symbol("b"), SExp::symbol("c")])
            ])
        );
        assert_eq!(&"  (a (b c)) tail"[consumed..], " tail");
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
            vec![SExp::symbol("foo"), SExp::symbol("bar")]
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

    #[test]
    fn map_transforms_atoms() {
        let sexp = SExp::List(vec![
            SExp::symbol("hello"),
            SExp::string("", b"world".as_slice()),
        ]);
        let mapped = sexp.map(&mut |atom| match atom {
            Atom::Symbol(s) => s.to_uppercase(),
            Atom::Str { bytes, .. } => String::from_utf8_lossy(&bytes).to_string(),
        });
        assert_eq!(
            mapped,
            SExp::List(vec![
                SExp::Atom("HELLO".to_string()),
                SExp::Atom("world".to_string()),
            ])
        );
    }

    #[test]
    fn parse_egglog_single_semicolon_comment() {
        // egglog uses single `;` for comments (unlike CovalenceDialect's `;;`).
        assert_eq!(
            parse_egglog("; this is a comment\n(sort Math)").unwrap(),
            vec![SExp::List(
                vec![SExp::symbol("sort"), SExp::symbol("Math"),]
            )]
        );
    }

    #[test]
    fn parse_egglog_no_quoted_symbols() {
        // egglog doesn't reserve `|…|` — pipes are ordinary atom chars,
        // so `|foo|` parses as a single 5-char symbol rather than the
        // CovalenceDialect / SmtLibDialect interpretation of "the symbol
        // foo".
        assert_eq!(parse_egglog("|foo|").unwrap(), vec![SExp::symbol("|foo|")]);
    }

    #[test]
    fn parse_egglog_kebab_and_punct_idents() {
        // egglog identifiers freely mix kebab-case and operator chars.
        assert_eq!(
            parse_egglog("(rewrite (+ a b) (+ b a))").unwrap(),
            vec![SExp::List(vec![
                SExp::symbol("rewrite"),
                SExp::List(vec![
                    SExp::symbol("+"),
                    SExp::symbol("a"),
                    SExp::symbol("b"),
                ]),
                SExp::List(vec![
                    SExp::symbol("+"),
                    SExp::symbol("b"),
                    SExp::symbol("a"),
                ]),
            ])]
        );
    }

    #[test]
    fn format_prefix_parsing() {
        // b"data" → Str { format: "b", bytes: b"data" }
        assert_eq!(
            parse(r#"b"data""#).unwrap(),
            vec![SExp::string("b", b"data".as_slice())]
        );
        // json"hello" → Str { format: "json", bytes: b"hello" }
        assert_eq!(
            parse(r#"json"hello""#).unwrap(),
            vec![SExp::string("json", b"hello".as_slice())]
        );
    }
}
