use std::io;

use pretty::{Arena, DocAllocator, DocBuilder};

use crate::Atom;
use crate::SExpr;

const DEFAULT_WIDTH: usize = 80;
const INDENT: isize = 2;

/// Pretty-print a sequence of S-expressions.
pub fn prettyprint(sexps: &[SExpr], writer: &mut dyn io::Write) -> io::Result<()> {
    let arena = Arena::<()>::new();
    let docs: Vec<_> = sexps.iter().map(|s| sexp_to_doc(&arena, s)).collect();
    if docs.is_empty() {
        return Ok(());
    }
    let doc = arena.intersperse(docs, arena.hardline());
    doc.1.render(DEFAULT_WIDTH, writer)
}

fn sexp_to_doc<'a>(arena: &'a Arena<'a>, sexp: &SExpr) -> DocBuilder<'a, Arena<'a>> {
    match sexp {
        SExpr::Atom(atom) => match atom {
            Atom::Symbol(s) => {
                if needs_quoting(s) {
                    arena.text(format!("|{}|", escape_quoted_symbol(s)))
                } else {
                    arena.text(s.to_string())
                }
            }
            Atom::Str { format, bytes } => {
                arena.text(format!("{}\"{}\"", format, escape_bytes(bytes)))
            }
        },
        SExpr::List(items) => {
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

/// Check if a symbol needs quoting with `|...|`.
fn needs_quoting(s: &str) -> bool {
    s.is_empty()
        || s.bytes()
            .any(|b| b.is_ascii_whitespace() || matches!(b, b'(' | b')' | b';' | b'"' | b'|'))
}

fn escape_bytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &b in bytes {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            0x07 => out.push_str("\\a"),
            0x08 => out.push_str("\\b"),
            0x0c => out.push_str("\\f"),
            0x0b => out.push_str("\\v"),
            b if b.is_ascii_graphic() || b == b' ' => out.push(b as char),
            b => out.push_str(&format!("\\x{b:02x}")),
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
