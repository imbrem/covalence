//! Parser for the `$( $t ... $)` *typesetting* comment.
//!
//! Metamath databases carry an optional typesetting section — a single
//! `$( $t ... $)` comment (or a few) containing `htmldef` / `althtmldef` /
//! `latexdef` statements that map each math token to a GIF/Unicode/LaTeX
//! rendering, plus presentation commands (`htmltitle`, `htmlcss`, …). This is
//! how the Metamath Proof Explorer typesets formulas.
//!
//! The grammar of the `$t` body is *not* the whitespace-tokenised `.mm` grammar:
//! string literals may contain spaces and are delimited by `"` or `'` (a literal
//! delimiter is escaped by doubling it), `/* ... */` comments are allowed, and
//! each statement ends in `;`. We extract the raw `(kind, token, value)` triples;
//! decoding the HTML/LaTeX value to display text is left to the consumer (it is a
//! presentation concern, not a Metamath one).
//!
//! Per the Metamath spec a comment cannot contain the token `$)`, so the `$t`
//! block is always cleanly delimited.

/// One typesetting definition: e.g. `althtmldef "->" as " &rarr; ";` →
/// `{ kind: "althtmldef", token: "->", value: " &rarr; " }`. The `value` is the
/// raw replacement string (HTML or LaTeX), un-decoded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typedef {
    /// `"htmldef"`, `"althtmldef"`, or `"latexdef"`.
    pub kind: String,
    /// The math token being defined.
    pub token: String,
    /// The raw replacement string (concatenated if it was split across literals).
    pub value: String,
}

/// Parse every `htmldef` / `althtmldef` / `latexdef` in the source's `$t`
/// typesetting comment(s). Returns them in source order (a later definition for
/// the same `(kind, token)` overrides an earlier one — callers building a map
/// should let the last win).
pub fn parse_typesetting(src: &str) -> Vec<Typedef> {
    let mut defs = Vec::new();
    for (start, end) in typesetting_spans(src) {
        let body = strip_c_comments(&src[start..end]);
        parse_body(&body, &mut defs);
    }
    defs
}

/// Byte spans (inside `src`) of each `$t` comment's body — the text strictly
/// between the `$t` marker and the closing `$)`.
fn typesetting_spans(src: &str) -> Vec<(usize, usize)> {
    let toks = tokens_with_pos(src);
    let mut spans = Vec::new();
    let mut i = 0;
    while i < toks.len() {
        if toks[i].0 == "$(" {
            // Find the matching `$)` (comments can't nest / contain `$)`).
            let is_t = i + 1 < toks.len() && toks[i + 1].0 == "$t";
            let mut j = i + 1;
            while j < toks.len() && toks[j].0 != "$)" {
                j += 1;
            }
            if is_t && j < toks.len() {
                spans.push((toks[i + 1].2, toks[j].1));
            }
            i = j + 1;
        } else {
            i += 1;
        }
    }
    spans
}

/// Whitespace-delimited tokens with their `(text, start, end)` byte positions.
fn tokens_with_pos(src: &str) -> Vec<(&str, usize, usize)> {
    let b = src.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        while i < b.len() && b[i].is_ascii_whitespace() {
            i += 1;
        }
        if i >= b.len() {
            break;
        }
        let start = i;
        while i < b.len() && !b[i].is_ascii_whitespace() {
            i += 1;
        }
        out.push((&src[start..i], start, i));
    }
    out
}

/// Replace `/* ... */` comments with a single space (non-nesting, per the `$t`
/// grammar). **String-aware**: a `/*` inside a quoted string literal is *not* a
/// comment — set.mm has `htmlexturl '…/mpests/*.html'` where `/*` is a URL glob,
/// and treating it as a comment would eat across the closing quote and desync
/// every following definition.
fn strip_c_comments(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    let mut quote: Option<char> = None;
    while i < n {
        let c = chars[i];
        if let Some(q) = quote {
            out.push(c);
            if c == q {
                // A doubled delimiter is an escaped literal — stay in the string.
                if i + 1 < n && chars[i + 1] == q {
                    out.push(q);
                    i += 2;
                    continue;
                }
                quote = None;
            }
            i += 1;
        } else if c == '/' && i + 1 < n && chars[i + 1] == '*' {
            i += 2;
            while i + 1 < n && !(chars[i] == '*' && chars[i + 1] == '/') {
                i += 1;
            }
            i = (i + 2).min(n); // skip the closing `*/` (or run to end if unterminated)
            out.push(' ');
        } else {
            if c == '"' || c == '\'' {
                quote = Some(c);
            }
            out.push(c);
            i += 1;
        }
    }
    out
}

/// A cursor over a typesetting body (already comment-stripped).
struct Scanner {
    c: Vec<char>,
    i: usize,
}

impl Scanner {
    fn skip_ws(&mut self) {
        while self.i < self.c.len() && self.c[self.i].is_whitespace() {
            self.i += 1;
        }
    }

    /// Read a bare word — up to the next whitespace, quote, `;`, or `+`.
    fn bare_word(&mut self) -> String {
        let start = self.i;
        while self.i < self.c.len() {
            let ch = self.c[self.i];
            if ch.is_whitespace() || ch == '"' || ch == '\'' || ch == ';' || ch == '+' {
                break;
            }
            self.i += 1;
        }
        self.c[start..self.i].iter().collect()
    }

    /// Read a quoted string at the cursor (delimiter `"` or `'`; a literal
    /// delimiter is escaped by doubling it). Assumes the cursor is on the quote.
    fn read_string(&mut self) -> String {
        let q = self.c[self.i];
        self.i += 1;
        let mut out = String::new();
        while self.i < self.c.len() {
            let ch = self.c[self.i];
            if ch == q {
                if self.i + 1 < self.c.len() && self.c[self.i + 1] == q {
                    out.push(q);
                    self.i += 2;
                    continue;
                }
                self.i += 1;
                return out;
            }
            out.push(ch);
            self.i += 1;
        }
        out // unterminated — return what we have
    }
}

/// Parse statements from one comment body, pushing recognised defs.
fn parse_body(body: &str, defs: &mut Vec<Typedef>) {
    let mut sc = Scanner {
        c: body.chars().collect(),
        i: 0,
    };
    let n = sc.c.len();
    while sc.i < n {
        sc.skip_ws();
        if sc.i >= n {
            break;
        }
        // Statements are `<command> ... ;`; the command is the leading bare word.
        let cmd = sc.bare_word();
        if cmd.is_empty() {
            sc.i += 1; // stray punctuation outside a string; advance to make progress
            continue;
        }
        let mut token: Option<String> = None;
        let mut value = String::new();
        let mut as_seen = false;
        loop {
            sc.skip_ws();
            if sc.i >= n {
                break;
            }
            let ch = sc.c[sc.i];
            if ch == ';' {
                sc.i += 1;
                break;
            } else if ch == '"' || ch == '\'' {
                let s = sc.read_string();
                if as_seen {
                    value.push_str(&s);
                } else if token.is_none() {
                    token = Some(s);
                }
            } else if ch == '+' {
                sc.i += 1; // string-concatenation operator
            } else {
                let w = sc.bare_word();
                if w.is_empty() {
                    sc.i += 1;
                } else if w == "as" {
                    as_seen = true;
                }
            }
        }
        if matches!(cmd.as_str(), "htmldef" | "althtmldef" | "latexdef") {
            if let Some(tok) = token {
                defs.push(Typedef {
                    kind: cmd,
                    token: tok,
                    value,
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_basic_defs() {
        let src = r#"
$c -> ( ) $.
$( $t
  /* a comment */
  htmldef "(" as "(";
  althtmldef "->" as " &rarr; ";
  althtmldef "-." as '&not; ';
  althtmldef "ph" as
      '<SPAN CLASS=wff STYLE="color:blue">&#x1D711;</SPAN>';
  htmltitle "Should Be Ignored; has a semicolon in string";
$)
"#;
        let defs = parse_typesetting(src);
        let alt: std::collections::HashMap<_, _> = defs
            .iter()
            .filter(|d| d.kind == "althtmldef")
            .map(|d| (d.token.as_str(), d.value.as_str()))
            .collect();
        assert_eq!(alt.get("->"), Some(&" &rarr; "));
        assert_eq!(alt.get("-."), Some(&"&not; "));
        assert_eq!(
            alt.get("ph"),
            Some(&r#"<SPAN CLASS=wff STYLE="color:blue">&#x1D711;</SPAN>"#)
        );
        // htmldef "(" parsed; htmltitle (no `as`) ignored as a def.
        assert!(defs.iter().any(|d| d.kind == "htmldef" && d.token == "("));
        assert!(!defs.iter().any(|d| d.token.starts_with("Should")));
    }

    #[test]
    fn slash_star_in_string_is_not_a_comment() {
        // Regression: set.mm's `htmlexturl '…/mpests/*.html'` contains `/*`
        // inside a string. A naive comment stripper eats to the next `*/`
        // (a `*******/` banner), desyncing every following def — here the `->`.
        let src = r#"
$( $t
  htmlexturl '<A HREF="http://x.org/mpests/*.html">link</A>';
  /******* Symbol definitions *******/
  htmldef "(" as "<IMG SRC='lp.gif'>";
  althtmldef "->" as " &rarr; ";
$)
"#;
        let defs = parse_typesetting(src);
        assert!(
            defs.iter().any(|d| d.kind == "althtmldef" && d.token == "->"),
            "the `->` def was swallowed by a fake comment: {:?}",
            defs.iter().map(|d| &d.token).collect::<Vec<_>>()
        );
    }

    #[test]
    fn no_typesetting_section() {
        assert!(parse_typesetting("$c a $. $( ordinary comment $)").is_empty());
    }
}
