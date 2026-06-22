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

use covalence_parse::winnow::{
    ModalResult, Parser,
    ascii::{multispace0, multispace1},
    combinator::{alt, opt},
    token::{rest, take_until, take_while},
};

/// Parse every `htmldef` / `althtmldef` / `latexdef` in the source's `$t`
/// typesetting comment(s). Returns them in source order (a later definition for
/// the same `(kind, token)` overrides an earlier one — callers building a map
/// should let the last win).
pub fn parse_typesetting(src: &str) -> Vec<Typedef> {
    let mut input = src;
    let mut defs = Vec::new();
    // Walk `$( ... $)` comments one at a time; parse the body of `$t` ones.
    while let Ok(body) = next_t_body.parse_next(&mut input) {
        if let Some(body) = body {
            collect_defs(body, &mut defs);
        }
    }
    defs
}

/// Advance to the next `$( ... $)` comment, consuming it. Returns its body iff
/// it is a `$t` typesetting comment. Errors once no more `$(` remain (which ends
/// the walk). Robust by construction: each call consumes a whole comment, so a
/// `$(`/`$)` *inside* a comment is part of its body, never a fresh opener — and
/// `$(` never appears in non-comment `.mm` content (no `$` in math tokens).
fn next_t_body<'s>(input: &mut &'s str) -> ModalResult<Option<&'s str>> {
    (take_until(0.., "$("), "$(").parse_next(input)?;
    multispace0(input)?;
    let is_t = opt(("$t", multispace1)).parse_next(input)?.is_some();
    let body = alt((take_until(0.., "$)"), rest)).parse_next(input)?;
    opt("$)").parse_next(input)?;
    Ok(is_t.then_some(body))
}

/// Parse the statements of one `$t` body, collecting the def statements.
fn collect_defs(body: &str, defs: &mut Vec<Typedef>) {
    let mut input = body;
    while skip_ws(&mut input).is_ok() && !input.is_empty() {
        match statement.parse_next(&mut input) {
            Ok(Some(def)) => defs.push(def),
            Ok(None) => {}      // a non-def command (htmltitle, htmlcss, …)
            Err(_) => break,    // malformed — stop this body
        }
    }
}

/// One `<command> <item>* ;` statement. Yields a [`Typedef`] iff the command is
/// `htmldef`/`althtmldef`/`latexdef`. Items are quoted strings (the first, before
/// `as`, is the token; those after `as` concatenate into the value), the `as`
/// keyword, and `+` concatenation operators.
fn statement(input: &mut &str) -> ModalResult<Option<Typedef>> {
    let cmd = bare_word(input)?.to_string();
    let mut token: Option<String> = None;
    let mut value = String::new();
    let mut as_seen = false;
    loop {
        skip_ws(input)?;
        if input.is_empty() || opt(';').parse_next(input)?.is_some() {
            break;
        }
        if let Some(s) = opt(alt((quoted('"'), quoted('\'')))).parse_next(input)? {
            if as_seen {
                value.push_str(&s);
            } else if token.is_none() {
                token = Some(s);
            }
        } else if opt('+').parse_next(input)?.is_some() {
            // string-concatenation operator
        } else if bare_word(input)? == "as" {
            as_seen = true;
        }
    }
    Ok(matches!(cmd.as_str(), "htmldef" | "althtmldef" | "latexdef")
        .then(|| token.map(|t| Typedef { kind: cmd, token: t, value }))
        .flatten())
}

/// Skip whitespace and `/* ... */` block comments. Because string literals are
/// parsed *explicitly* elsewhere, a `/*` inside a string is never seen here — so
/// set.mm's `htmlexturl '…/mpests/*.html'` (a URL glob) is not mistaken for a
/// comment (the bug that desynced the old hand-written stripper).
fn skip_ws(input: &mut &str) -> ModalResult<()> {
    loop {
        multispace0(input)?;
        if opt(("/*", alt((take_until(0.., "*/"), rest)), opt("*/")))
            .parse_next(input)?
            .is_none()
        {
            return Ok(());
        }
    }
}

/// A bare word: a run of non-whitespace, non-quote, non-`;`, non-`+` characters.
fn bare_word<'s>(input: &mut &'s str) -> ModalResult<&'s str> {
    take_while(1.., |c: char| {
        !c.is_whitespace() && !matches!(c, '"' | '\'' | ';' | '+')
    })
    .parse_next(input)
}

/// A string literal delimited by `q` (`"` or `'`), where a literal delimiter is
/// escaped by doubling it (`""` → `"`).
fn quoted(q: char) -> impl FnMut(&mut &str) -> ModalResult<String> {
    move |input: &mut &str| {
        let mut delim = q; // `char: Parser` needs `&mut self`
        delim.parse_next(input)?; // opening delimiter
        let mut out = String::new();
        loop {
            out.push_str(take_while(0.., |c: char| c != q).parse_next(input)?);
            delim.parse_next(input)?; // delimiter (closing, or first of an escaped pair)
            if opt(delim).parse_next(input)?.is_some() {
                out.push(q);
            } else {
                return Ok(out);
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
