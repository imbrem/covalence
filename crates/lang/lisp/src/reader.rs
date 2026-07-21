//! The reader — a thin wrapper over [`covalence_sexp::parse`].
//!
//! Materializes the [`SExpr`] tree (the simplest correct thing). The
//! event-driven fold-to-`Term` path (`SExpBuilder` / `TreeBuilder`) is a
//! future allocation optimization; see the generated open-work index.

use covalence_sexp::{ParseError, SExpr, parse};
use covalence_sexpr_api::SExprSyntax;

/// Fold the parser's proper-list surface tree into an abstract S-expression
/// representation.
///
/// This adapter lives in the language layer so the low-level parser never
/// depends on `covalence-sexpr-api`. `atom` selects the dialect's payload
/// interpretation; list structure is lowered solely through the abstract
/// `nil`/`cons` capabilities.
pub fn lower_with<A>(
    api: &A,
    sexpr: &SExpr,
    atom: &impl Fn(&covalence_sexp::Atom) -> Result<A::Payload, A::Error>,
) -> Result<A::Value, A::Error>
where
    A: SExprSyntax + ?Sized,
{
    match sexpr {
        SExpr::Atom(value) => api.atom(atom(value)?),
        SExpr::List(items) => {
            let mut result = api.nil();
            for item in items.iter().rev() {
                let head = lower_with(api, item, atom)?;
                result = api.cons(head, result)?;
            }
            Ok(result)
        }
    }
}

/// Parse `src` into a sequence of top-level S-expressions.
pub fn read(src: &str) -> Result<Vec<SExpr>, ParseError> {
    parse(src)
}

/// Parse Scheme source, expanding quote, quasiquote, and unquote reader forms.
pub fn read_scheme(src: &str) -> Result<Vec<SExpr>, ParseError> {
    let normalized = LispSurface::new(src, ReaderDialect::Scheme).normalize()?;
    parse(&normalized)
}

/// Parse an **ACL2 book source** into its top-level forms.
///
/// The ACL2 surface pass expands `'x` to `(quote x)`, skips nested `#|…|#`
/// comments, and folds unescaped symbols to lowercase (the spelling used by
/// the evaluator). Strings and `|escaped symbols|` retain their contents.
/// The resulting source is parsed with the SMT-LIB trivia dialect, which also
/// provides ACL2's single-`;` line comments.
pub fn read_book(src: &str) -> Result<Vec<SExpr>, ParseError> {
    let normalized = LispSurface::new(src, ReaderDialect::Acl2).normalize()?;
    covalence_sexp::parse_smt(&normalized)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReaderDialect {
    Scheme,
    Acl2,
}

/// Lisp reader syntax that does not belong in the shared S-expression parser.
struct LispSurface<'a> {
    src: &'a str,
    pos: usize,
    out: String,
    dialect: ReaderDialect,
}

impl<'a> LispSurface<'a> {
    fn new(src: &'a str, dialect: ReaderDialect) -> Self {
        Self {
            src,
            pos: 0,
            out: String::with_capacity(src.len()),
            dialect,
        }
    }

    fn normalize(mut self) -> Result<String, ParseError> {
        self.trivia()?;
        while self.pos < self.src.len() {
            self.form()?;
            self.trivia()?;
        }
        Ok(self.out)
    }

    fn form(&mut self) -> Result<(), ParseError> {
        let Some(byte) = self.peek() else {
            return Err(self.error("expected form"));
        };
        if self.dialect == ReaderDialect::Acl2 && self.rest().starts_with("#\\") {
            return self.character_literal();
        }
        if self.dialect == ReaderDialect::Acl2 && self.rest().starts_with("#.") {
            self.reader_macro("sharp-dot", 2)?;
            return Ok(());
        }
        match byte {
            b'\'' => self.reader_macro("quote", 1)?,
            b'`' => self.reader_macro("quasiquote", 1)?,
            b',' => {
                let (name, width) = if self.rest().starts_with(",@") {
                    ("unquote-splicing", 2)
                } else {
                    ("unquote", 1)
                };
                self.reader_macro(name, width)?;
            }
            b'(' => {
                self.pos += 1;
                self.out.push('(');
                self.trivia()?;
                while self.peek() != Some(b')') {
                    if self.pos == self.src.len() {
                        return Err(self.error("unclosed '('"));
                    }
                    self.form()?;
                    self.trivia()?;
                }
                self.pos += 1;
                self.out.push(')');
            }
            b')' => return Err(self.error("unexpected ')'")),
            b'"' => self.delimited(b'"', true)?,
            b'|' => self.delimited(b'|', true)?,
            _ => self.atom(),
        }
        Ok(())
    }

    fn character_literal(&mut self) -> Result<(), ParseError> {
        let start = self.pos;
        self.pos += 2;
        if self.pos == self.src.len() {
            return Err(ParseError {
                offset: start,
                message: "incomplete #\\ character literal".into(),
            });
        }
        let value_start = self.pos;
        let first = self.rest().chars().next().expect("not at eof");
        if first.is_ascii_whitespace()
            || matches!(first, '(' | ')' | ';' | '"' | '|' | '\'' | '`' | ',')
        {
            self.pos += first.len_utf8();
        } else {
            while let Some(ch) = self.rest().chars().next() {
                if ch.is_ascii_whitespace() || matches!(ch, '(' | ')' | ';' | '"') {
                    break;
                }
                self.pos += ch.len_utf8();
            }
        }
        let value = &self.src[value_start..self.pos];
        self.out.push('|');
        self.out.push_str("#\\\\");
        for ch in value.chars() {
            if matches!(ch, '|' | '\\') {
                self.out.push('\\');
            }
            self.out.push(ch);
        }
        self.out.push('|');
        Ok(())
    }

    fn reader_macro(&mut self, name: &str, width: usize) -> Result<(), ParseError> {
        self.pos += width;
        self.out.push('(');
        self.out.push_str(name);
        self.out.push(' ');
        self.trivia()?;
        if self.pos == self.src.len() {
            return Err(self.error(format!("{name} without a following form")));
        }
        self.form()?;
        self.out.push(')');
        Ok(())
    }

    fn trivia(&mut self) -> Result<(), ParseError> {
        loop {
            while self.peek().is_some_and(|byte| byte.is_ascii_whitespace()) {
                self.out.push(self.src.as_bytes()[self.pos] as char);
                self.pos += 1;
            }
            if self.peek() == Some(b';') {
                while let Some(byte) = self.peek() {
                    self.pos += 1;
                    if byte == b'\n' {
                        self.out.push('\n');
                        break;
                    }
                }
                continue;
            }
            if self.rest().starts_with("#|") {
                let start = self.pos;
                self.pos += 2;
                let mut depth = 1usize;
                while depth != 0 {
                    if self.pos == self.src.len() {
                        return Err(ParseError {
                            offset: start,
                            message: "unterminated #| block comment".into(),
                        });
                    }
                    if self.rest().starts_with("#|") {
                        self.pos += 2;
                        depth += 1;
                    } else if self.rest().starts_with("|#") {
                        self.pos += 2;
                        depth -= 1;
                    } else {
                        if self.peek() == Some(b'\n') {
                            self.out.push('\n');
                        }
                        self.advance_char();
                    }
                }
                self.out.push(' ');
                continue;
            }
            return Ok(());
        }
    }

    fn atom(&mut self) {
        let start = self.pos;
        while let Some(byte) = self.peek() {
            if byte.is_ascii_whitespace()
                || matches!(byte, b'(' | b')' | b';' | b'"' | b'|' | b'\'' | b'`' | b',')
                || self.rest().starts_with("#|")
            {
                break;
            }
            self.advance_char();
        }
        let atom = &self.src[start..self.pos];
        match self.dialect {
            ReaderDialect::Scheme => self.out.push_str(atom),
            ReaderDialect::Acl2 => {
                if let Some(decimal) = acl2_radix_integer(atom) {
                    self.out.push_str(&decimal);
                } else {
                    for ch in atom.chars() {
                        self.out.extend(ch.to_lowercase());
                    }
                }
            }
        }
    }

    fn delimited(&mut self, delimiter: u8, escaped: bool) -> Result<(), ParseError> {
        let start = self.pos;
        self.out.push(delimiter as char);
        self.pos += 1;
        while let Some(byte) = self.peek() {
            let ch = self.rest().chars().next().expect("not at eof");
            self.out.push(ch);
            self.pos += ch.len_utf8();
            if escaped && byte == b'\\' {
                let Some(next) = self.rest().chars().next() else {
                    return Err(ParseError {
                        offset: start,
                        message: "unterminated escape".into(),
                    });
                };
                if self.dialect == ReaderDialect::Acl2
                    && delimiter == b'"'
                    && !matches!(next, '"' | '\\')
                {
                    // Common Lisp's backslash quotes exactly the next
                    // character.  Do not pass it through to the shared
                    // string parser, where e.g. `\0` starts a hex escape and
                    // `\n` denotes a newline instead of the literal `n`.
                    self.out.pop();
                }
                self.out.push(next);
                self.pos += next.len_utf8();
            } else if byte == delimiter {
                return Ok(());
            }
        }
        Err(ParseError {
            offset: start,
            message: if delimiter == b'"' {
                "unterminated string"
            } else {
                "unterminated escaped symbol"
            }
            .into(),
        })
    }

    fn peek(&self) -> Option<u8> {
        self.src.as_bytes().get(self.pos).copied()
    }

    fn rest(&self) -> &str {
        &self.src[self.pos..]
    }

    fn advance_char(&mut self) {
        self.pos += self.rest().chars().next().expect("not at eof").len_utf8();
    }

    fn error(&self, message: impl Into<String>) -> ParseError {
        ParseError {
            offset: self.pos,
            message: message.into(),
        }
    }
}

/// Convert ACL2/Common Lisp `#b`, `#o`, and `#x` integer tokens, plus x86isa's
/// underscore-tolerant `#u[bodx]` tokens, to evaluator decimal spelling.
fn acl2_radix_integer(atom: &str) -> Option<String> {
    let bytes = atom.as_bytes();
    if bytes.len() < 3 || bytes[0] != b'#' {
        return None;
    }
    let (radix_byte, prefix_len) = if bytes[1].eq_ignore_ascii_case(&b'u') {
        (*bytes.get(2)?, 3)
    } else {
        (bytes[1], 2)
    };
    let radix = match radix_byte.to_ascii_lowercase() {
        b'b' => 2,
        b'd' => 10,
        b'o' => 8,
        b'x' => 16,
        _ => return None,
    };
    let mut digits = &atom[prefix_len..];
    let negative = digits.starts_with('-');
    if negative || digits.starts_with('+') {
        digits = &digits[1..];
    }
    if digits.is_empty() {
        return None;
    }
    let mut decimal_digits = vec![0u8];
    let mut saw_digit = false;
    for digit in digits.chars().filter(|digit| *digit != '_') {
        let digit = digit.to_digit(radix)?;
        saw_digit = true;
        let mut carry = digit;
        for decimal_digit in &mut decimal_digits {
            let value = u32::from(*decimal_digit) * radix + carry;
            *decimal_digit = (value % 10) as u8;
            carry = value / 10;
        }
        while carry != 0 {
            decimal_digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    if !saw_digit {
        return None;
    }
    let mut decimal = String::with_capacity(decimal_digits.len() + usize::from(negative));
    if negative && decimal_digits.iter().any(|digit| *digit != 0) {
        decimal.push('-');
    }
    decimal.extend(
        decimal_digits
            .into_iter()
            .rev()
            .map(|digit| char::from(b'0' + digit)),
    );
    Some(decimal)
}

// TODO(cov:acl2.reader.dispatch-macros, major): Support remaining ACL2 sharp
// dispatch forms used by community books, especially feature conditionals and
// package-installed reader macros other than x86isa's integer #u forms.

/// Parse `src` expecting exactly one top-level S-expression (one REPL cell).
pub fn read_one(src: &str) -> Result<SExpr, ReadError> {
    exactly_one(read(src).map_err(ReadError::Parse)?)
}

/// Read exactly one Scheme form with standard quote reader abbreviations.
pub fn read_scheme_one(src: &str) -> Result<SExpr, ReadError> {
    exactly_one(read_scheme(src).map_err(ReadError::Parse)?)
}

/// Read exactly one ACL2 form with Common Lisp reader normalization.
pub fn read_book_one(src: &str) -> Result<SExpr, ReadError> {
    exactly_one(read_book(src).map_err(ReadError::Parse)?)
}

fn exactly_one(mut forms: Vec<SExpr>) -> Result<SExpr, ReadError> {
    match forms.len() {
        1 => Ok(forms.pop().expect("len checked")),
        n => Err(ReadError::Arity(n)),
    }
}

/// A single-form read error.
#[derive(Debug, thiserror::Error)]
pub enum ReadError {
    /// The S-expression parser failed.
    #[error(transparent)]
    Parse(ParseError),
    /// Expected exactly one top-level form, found `n`.
    #[error("expected exactly one top-level form, found {0}")]
    Arity(usize),
}

#[cfg(test)]
mod tests {
    use covalence_sexpr_api::{Free, FreeSExpr};

    use super::*;

    #[test]
    fn parsed_proper_lists_lower_through_the_abstract_api() {
        let parsed = read_one("(a (b))").unwrap();
        let lowered = lower_with(&Free::<String>::new(), &parsed, &|atom| match atom {
            covalence_sexp::Atom::Symbol(value) => Ok(value.to_string()),
            covalence_sexp::Atom::Str { .. } => unreachable!(),
        })
        .unwrap();

        assert_eq!(
            lowered,
            FreeSExpr::Cons(
                Box::new(FreeSExpr::Atom("a".into())),
                Box::new(FreeSExpr::Cons(
                    Box::new(FreeSExpr::Cons(
                        Box::new(FreeSExpr::Atom("b".into())),
                        Box::new(FreeSExpr::Nil),
                    )),
                    Box::new(FreeSExpr::Nil),
                )),
            )
        );
    }

    #[test]
    fn scheme_reader_expands_quote_family_without_acl2_case_folding() {
        assert_eq!(
            read_scheme_one("`(Keep ,value ,@rest)").unwrap(),
            SExpr::list(vec![
                SExpr::symbol("quasiquote"),
                SExpr::list(vec![
                    SExpr::symbol("Keep"),
                    SExpr::list(vec![SExpr::symbol("unquote"), SExpr::symbol("value")]),
                    SExpr::list(vec![
                        SExpr::symbol("unquote-splicing"),
                        SExpr::symbol("rest"),
                    ]),
                ]),
            ])
        );
        assert_eq!(
            read_scheme_one("'MixedCase").unwrap(),
            SExpr::list(vec![SExpr::symbol("quote"), SExpr::symbol("MixedCase")])
        );
    }

    #[test]
    fn one_form_acl2_reader_applies_book_normalization() {
        assert_eq!(
            read_book_one("'MixedCase").unwrap(),
            SExpr::list(vec![SExpr::symbol("quote"), SExpr::symbol("mixedcase")])
        );
    }

    #[test]
    fn acl2_book_expands_quote_and_folds_unescaped_symbols() {
        assert_eq!(
            read_book("'Foo '(BAR |KeepCaseλ| \"String λ\")").unwrap(),
            vec![
                SExpr::list(vec![SExpr::symbol("quote"), SExpr::symbol("foo")]),
                SExpr::list(vec![
                    SExpr::symbol("quote"),
                    SExpr::list(vec![
                        SExpr::symbol("bar"),
                        SExpr::symbol("KeepCaseλ"),
                        SExpr::string("", "String λ"),
                    ]),
                ]),
            ]
        );
    }

    #[test]
    fn acl2_book_skips_nested_block_and_line_comments() {
        assert_eq!(
            read_book("#| outer\n #| nested |# still outer |#\n(DEFUN F (X) ; rest\n 'X)").unwrap(),
            vec![SExpr::list(vec![
                SExpr::symbol("defun"),
                SExpr::symbol("f"),
                SExpr::list(vec![SExpr::symbol("x")]),
                SExpr::list(vec![SExpr::symbol("quote"), SExpr::symbol("x")]),
            ])]
        );
    }

    #[test]
    fn acl2_book_reports_unterminated_block_comment() {
        let error = read_book("(foo) #| never closed").unwrap_err();
        assert_eq!(error.offset, 6);
        assert!(error.message.contains("unterminated #|"));
    }

    #[test]
    fn acl2_book_expands_quasiquote_and_unquotes() {
        assert_eq!(
            read_book("`(A ,B ,@C)").unwrap(),
            vec![SExpr::list(vec![
                SExpr::symbol("quasiquote"),
                SExpr::list(vec![
                    SExpr::symbol("a"),
                    SExpr::list(vec![SExpr::symbol("unquote"), SExpr::symbol("b")]),
                    SExpr::list(vec![SExpr::symbol("unquote-splicing"), SExpr::symbol("c"),]),
                ]),
            ])]
        );
    }

    #[test]
    fn acl2_book_keeps_delimiter_character_literals_atomic() {
        assert_eq!(
            read_book(r#"(list #\) #\( #\" #\; #\Space)"#).unwrap(),
            vec![SExpr::list(vec![
                SExpr::symbol("list"),
                SExpr::symbol("#\\)"),
                SExpr::symbol("#\\("),
                SExpr::symbol("#\\\""),
                SExpr::symbol("#\\;"),
                SExpr::symbol("#\\Space"),
            ])]
        );
    }

    #[test]
    fn acl2_book_uses_common_lisp_string_escapes() {
        assert_eq!(
            read_book(r#""\0 \( \n \" \\""#).unwrap(),
            vec![SExpr::string("", b"0 ( n \" \\".as_slice())]
        );
    }

    #[test]
    fn acl2_book_expands_sharp_dot_and_normalizes_radix_integers() {
        assert_eq!(
            read_book("(list #.*Width* #xF0 #b0011 #o17 X86ISA::RGFI :LOGIC #ux0F #-x)").unwrap(),
            vec![SExpr::list(vec![
                SExpr::symbol("list"),
                SExpr::list(vec![SExpr::symbol("sharp-dot"), SExpr::symbol("*width*"),]),
                SExpr::symbol("240"),
                SExpr::symbol("3"),
                SExpr::symbol("15"),
                SExpr::symbol("x86isa::rgfi"),
                SExpr::symbol(":logic"),
                SExpr::symbol("15"),
                SExpr::symbol("#-x"),
            ])]
        );
    }

    /// Run with `ACL2_CORPUS_DIR=/path/to/community-books cargo test
    /// -p covalence-lisp acl2_community_books_parse -- --ignored --nocapture`.
    #[test]
    #[ignore = "requires a separately downloaded ACL2 community-books corpus"]
    fn acl2_community_books_parse() {
        fn collect(dir: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
            for entry in std::fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    collect(&path, files);
                } else if matches!(
                    path.extension().and_then(|ext| ext.to_str()),
                    Some("lisp" | "lsp")
                ) {
                    files.push(path);
                }
            }
        }

        let root = std::env::var_os("ACL2_CORPUS_DIR")
            .expect("set ACL2_CORPUS_DIR to the community-books root");
        let mut files = Vec::new();
        collect(std::path::Path::new(&root), &mut files);
        files.sort();
        let mut failures = Vec::new();
        for path in &files {
            let source = std::fs::read_to_string(path).unwrap();
            if let Err(error) = read_book(&source) {
                failures.push((path.clone(), error));
            }
        }
        for (path, error) in &failures {
            eprintln!("{}: {error}", path.display());
        }
        let passed = files.len() - failures.len();
        eprintln!(
            "ACL2 reader corpus: {passed}/{} files parsed ({:?} failures)",
            files.len(),
            failures.len()
        );
        assert!(
            passed * 100 >= files.len() * 95,
            "only {passed}/{} ACL2 source files parsed ({} failures)",
            files.len(),
            failures.len(),
        );
    }
}
