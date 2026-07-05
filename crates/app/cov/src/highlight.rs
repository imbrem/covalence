//! S-expression syntax highlighting with ANSI escape codes.

use std::borrow::Cow;

// ANSI color codes
const RESET: &str = "\x1b[0m";
const BLUE: &str = "\x1b[94m"; // keywords
const GREEN: &str = "\x1b[92m"; // strings
const ORANGE: &str = "\x1b[33m"; // numbers, hashes
const PURPLE: &str = "\x1b[35m"; // $variables
const DIM: &str = "\x1b[2m"; // parens, comments
const ITALIC: &str = "\x1b[3m"; // comments

const KEYWORDS: &[&str] = &[
    // WAT component-model structural keywords
    "module",
    "component",
    "import",
    "export",
    "func",
    "param",
    "result",
    "type",
    "instance",
    "core",
    "canon",
    "lift",
    "lower",
    "memory",
    "table",
    "global",
    "elem",
    "data",
    "start",
    "local",
    "alias",
    // REPL commands
    "store",
    "help",
    "parse-module",
    "parse-component",
    "decide",
];

fn is_keyword(s: &str) -> bool {
    KEYWORDS.contains(&s)
}

/// Highlight an S-expression string with ANSI escape codes.
pub fn highlight_sexp(text: &str) -> String {
    let mut out = String::with_capacity(text.len() * 2);
    let bytes = text.as_bytes();
    let mut i = 0;

    while i < bytes.len() {
        let ch = bytes[i];
        match ch {
            b';' => {
                // Comment: rest of line
                let end = memchr::memchr(b'\n', &bytes[i..])
                    .map(|p| i + p)
                    .unwrap_or(bytes.len());
                out.push_str(DIM);
                out.push_str(ITALIC);
                out.push_str(&text[i..end]);
                out.push_str(RESET);
                i = end;
            }
            b'|' => {
                // Quoted symbol |...|
                let end = memchr::memchr(b'|', &bytes[i + 1..])
                    .map(|p| i + 1 + p + 1)
                    .unwrap_or(bytes.len());
                out.push_str(DIM);
                out.push_str(&text[i..end]);
                out.push_str(RESET);
                i = end;
            }
            b'"' => {
                // String literal
                let mut end = i + 1;
                while end < bytes.len() && bytes[end] != b'"' {
                    if bytes[end] == b'\\' {
                        end += 1;
                    }
                    end += 1;
                }
                if end < bytes.len() {
                    end += 1;
                }
                out.push_str(GREEN);
                out.push_str(&text[i..end]);
                out.push_str(RESET);
                i = end;
            }
            b'(' | b')' => {
                out.push_str(DIM);
                out.push(ch as char);
                out.push_str(RESET);
                i += 1;
            }
            _ if ch.is_ascii_whitespace() => {
                out.push(ch as char);
                i += 1;
            }
            _ => {
                // Atom: read until delimiter
                let mut end = i;
                while end < bytes.len()
                    && !matches!(
                        bytes[end],
                        b' ' | b'\t' | b'\n' | b'\r' | b'(' | b')' | b'"' | b';' | b'|'
                    )
                {
                    end += 1;
                }
                let atom = &text[i..end];
                if is_keyword(atom) {
                    out.push_str(BLUE);
                } else if atom.starts_with('$') {
                    out.push_str(PURPLE);
                } else if
                // Hashes (64 hex chars) and numeric literals are both
                // rendered orange today; keep them as one merged arm.
                (atom.len() == 64 && atom.chars().all(|c| c.is_ascii_hexdigit()))
                    || atom.starts_with('-')
                    || atom.as_bytes()[0].is_ascii_digit()
                    || atom.starts_with("0x")
                {
                    out.push_str(ORANGE);
                } else {
                    out.push_str(atom);
                    i = end;
                    continue;
                }
                out.push_str(atom);
                out.push_str(RESET);
                i = end;
            }
        }
    }
    out
}

/// Determine if output text looks like code (S-expression or hashes) vs. prose.
pub fn is_code_output(text: &str) -> bool {
    let trimmed = text.trim();
    if trimmed.is_empty() {
        return false;
    }
    let lines: Vec<&str> = trimmed.lines().collect();
    // All lines are 64-char hex hashes
    if lines
        .iter()
        .all(|l| l.trim().len() == 64 && l.trim().chars().all(|c| c.is_ascii_hexdigit()))
    {
        return true;
    }
    // S-expression block: first line starts with (, last line ends with )
    let first = lines[0].trim_start();
    let last = lines[lines.len() - 1].trim_end();
    if first.starts_with('(') && last.ends_with(')') {
        // Exclude help-style: "(cmd args)   description text"
        // Check if first line has content after the top-level sexp closes
        let mut depth = 0i32;
        let mut in_str = false;
        let mut escaped = false;
        for (idx, ch) in first.char_indices() {
            if escaped {
                escaped = false;
                continue;
            }
            if in_str {
                if ch == '\\' {
                    escaped = true;
                } else if ch == '"' {
                    in_str = false;
                }
                continue;
            }
            match ch {
                '"' => in_str = true,
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        let rest = first[idx + 1..].trim();
                        if !rest.is_empty() && !rest.starts_with('(') && !rest.starts_with(';') {
                            return false;
                        }
                        break;
                    }
                }
                _ => {}
            }
        }
        return true;
    }
    false
}

/// Highlight output text: only applies highlighting if it looks like code.
pub fn highlight_output(text: &str, color: bool) -> Cow<'_, str> {
    if !color || !is_code_output(text) {
        return Cow::Borrowed(text);
    }
    Cow::Owned(highlight_sexp(text))
}

/// Rustyline helper that provides input syntax highlighting.
pub struct SexpHelper {
    pub color: bool,
}

impl rustyline::Helper for SexpHelper {}
impl rustyline::completion::Completer for SexpHelper {
    type Candidate = String;
}
impl rustyline::hint::Hinter for SexpHelper {
    type Hint = String;
}
impl rustyline::validate::Validator for SexpHelper {}

impl rustyline::highlight::Highlighter for SexpHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> Cow<'l, str> {
        if self.color && !line.is_empty() {
            Cow::Owned(highlight_sexp(line))
        } else {
            Cow::Borrowed(line)
        }
    }

    fn highlight_char(
        &self,
        _line: &str,
        _pos: usize,
        _kind: rustyline::highlight::CmdKind,
    ) -> bool {
        self.color
    }
}
