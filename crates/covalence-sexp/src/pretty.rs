use std::io;

use pretty::{Arena, DocAllocator, DocBuilder};

use crate::SExp;

const DEFAULT_WIDTH: usize = 80;
const INDENT: isize = 2;

/// Pretty-print a sequence of S-expressions.
pub fn prettyprint(sexps: &[SExp], writer: &mut dyn io::Write) -> io::Result<()> {
    let arena = Arena::<()>::new();
    let docs: Vec<_> = sexps.iter().map(|s| sexp_to_doc(&arena, s)).collect();
    if docs.is_empty() {
        return Ok(());
    }
    let doc = arena.intersperse(docs, arena.hardline());
    doc.1.render(DEFAULT_WIDTH, writer)
}

fn sexp_to_doc<'a>(arena: &'a Arena<'a>, sexp: &SExp) -> DocBuilder<'a, Arena<'a>> {
    match sexp {
        SExp::Atom(s) => arena.text(s.to_string()),
        SExp::String(s) => arena.text(format!("\"{}\"", escape_string(s))),
        SExp::ByteString(bytes) => arena.text(format!("b\"{}\"", escape_bytes(bytes))),
        SExp::QuotedSymbol(s) => arena.text(format!("|{}|", escape_quoted_symbol(s))),
        SExp::List(items) => {
            if items.is_empty() {
                return arena.text("()");
            }
            let elems: Vec<_> = items.iter().map(|s| sexp_to_doc(arena, s)).collect();
            let sep = arena.line();
            arena
                .text("(")
                .append(
                    arena
                        .line_()
                        .append(arena.intersperse(elems, sep))
                        .nest(INDENT),
                )
                .append(arena.line_())
                .append(arena.text(")"))
                .group()
        }
    }
}

fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\x07' => out.push_str("\\a"),
            '\x08' => out.push_str("\\b"),
            '\x0c' => out.push_str("\\f"),
            '\x0b' => out.push_str("\\v"),
            c => out.push(c),
        }
    }
    out
}

fn escape_bytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &b in bytes {
        if b == b'"' {
            out.push_str("\\\"");
        } else if b == b'\\' {
            out.push_str("\\\\");
        } else if b.is_ascii_graphic() || b == b' ' {
            out.push(b as char);
        } else {
            out.push_str(&format!("\\x{b:02x}"));
        }
    }
    out
}

fn escape_quoted_symbol(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '|' => out.push_str("\\|"),
            '\\' => out.push_str("\\\\"),
            c => out.push(c),
        }
    }
    out
}
