use std::io;

use ion_rs::{Element, IonType, Sequence, Struct, Value};
use pretty::{Arena, DocAllocator, DocBuilder};

const DEFAULT_WIDTH: usize = 80;
const INDENT: isize = 2;

/// Pretty-print a sequence of Ion elements to the given writer.
pub fn prettyprint(ast: &Sequence, writer: &mut dyn io::Write) -> io::Result<()> {
    let arena = Arena::<()>::new();
    let docs: Vec<_> = ast.iter().map(|elem| element_to_doc(&arena, elem)).collect();
    if docs.is_empty() {
        return Ok(());
    }
    let doc = arena.intersperse(docs, arena.hardline());
    doc.1.render(DEFAULT_WIDTH, writer)
}

fn element_to_doc<'a>(arena: &'a Arena<'a>, elem: &Element) -> DocBuilder<'a, Arena<'a>> {
    let value_doc = value_to_doc(arena, elem);
    let mut doc = arena.nil();
    for ann in elem.annotations() {
        if let Some(text) = ann.text() {
            doc = doc
                .append(symbol_to_doc(arena, text))
                .append(arena.text("::"));
        }
    }
    doc.append(value_doc)
}

fn value_to_doc<'a>(arena: &'a Arena<'a>, elem: &Element) -> DocBuilder<'a, Arena<'a>> {
    match elem.value() {
        Value::Null(ion_type) => arena.text(null_text(*ion_type)),
        Value::Bool(b) => arena.text(if *b { "true" } else { "false" }),
        Value::Int(i) => arena.text(i.to_string()),
        Value::Float(f) => float_to_doc(arena, *f),
        Value::Decimal(d) => arena.text(d.to_string()),
        Value::Timestamp(t) => arena.text(t.to_string()),
        Value::Symbol(s) => match s.text() {
            Some(text) => symbol_to_doc(arena, text),
            None => arena.text("$0"),
        },
        Value::String(s) => arena.text(format!("\"{}\"", escape_string(s.text()))),
        Value::Blob(b) => arena.text(format!("{{ {} }}", base64_encode(b.as_ref()))),
        Value::Clob(c) => arena.text(format!("{{ \"{}\" }}", escape_clob(c.as_ref()))),
        Value::List(seq) => list_to_doc(arena, seq),
        Value::SExp(seq) => sexp_to_doc(arena, seq),
        Value::Struct(s) => struct_to_doc(arena, s),
    }
}

fn null_text(ion_type: IonType) -> &'static str {
    match ion_type {
        IonType::Null => "null",
        IonType::Bool => "null.bool",
        IonType::Int => "null.int",
        IonType::Float => "null.float",
        IonType::Decimal => "null.decimal",
        IonType::Timestamp => "null.timestamp",
        IonType::Symbol => "null.symbol",
        IonType::String => "null.string",
        IonType::Clob => "null.clob",
        IonType::Blob => "null.blob",
        IonType::List => "null.list",
        IonType::SExp => "null.sexp",
        IonType::Struct => "null.struct",
    }
}

fn float_to_doc<'a>(arena: &'a Arena<'a>, f: f64) -> DocBuilder<'a, Arena<'a>> {
    if f.is_nan() {
        arena.text("nan")
    } else if f == f64::INFINITY {
        arena.text("+inf")
    } else if f == f64::NEG_INFINITY {
        arena.text("-inf")
    } else {
        arena.text(format!("{:e}", f))
    }
}

fn needs_quoting(text: &str) -> bool {
    if text.is_empty() {
        return true;
    }
    match text {
        "null" | "true" | "false" | "nan" => return true,
        _ => {}
    }
    let mut chars = text.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' || c == '$' => {}
        _ => return true,
    }
    for c in chars {
        if !c.is_ascii_alphanumeric() && c != '_' && c != '$' {
            return true;
        }
    }
    false
}

fn symbol_to_doc<'a>(arena: &'a Arena<'a>, text: &str) -> DocBuilder<'a, Arena<'a>> {
    if needs_quoting(text) {
        arena.text(format!("'{}'", escape_symbol(text)))
    } else {
        arena.text(text.to_owned())
    }
}

fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_control() => {
                for byte in c.to_string().bytes() {
                    out.push_str(&format!("\\x{:02x}", byte));
                }
            }
            c => out.push(c),
        }
    }
    out
}

fn escape_symbol(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\'' => out.push_str("\\'"),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c => out.push(c),
        }
    }
    out
}

fn escape_clob(data: &[u8]) -> String {
    let mut out = String::new();
    for &b in data {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0 => out.push_str("\\0"),
            b if b.is_ascii_graphic() || b == b' ' => out.push(b as char),
            b => out.push_str(&format!("\\x{:02x}", b)),
        }
    }
    out
}

fn base64_encode(data: &[u8]) -> String {
    const CHARS: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut result = String::with_capacity((data.len() + 2) / 3 * 4);
    for chunk in data.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = chunk.get(1).copied().unwrap_or(0) as u32;
        let b2 = chunk.get(2).copied().unwrap_or(0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        result.push(CHARS[((n >> 18) & 63) as usize] as char);
        result.push(CHARS[((n >> 12) & 63) as usize] as char);
        if chunk.len() > 1 {
            result.push(CHARS[((n >> 6) & 63) as usize] as char);
        } else {
            result.push('=');
        }
        if chunk.len() > 2 {
            result.push(CHARS[(n & 63) as usize] as char);
        } else {
            result.push('=');
        }
    }
    result
}

fn list_to_doc<'a>(arena: &'a Arena<'a>, seq: &Sequence) -> DocBuilder<'a, Arena<'a>> {
    if seq.is_empty() {
        return arena.text("[]");
    }
    let elems: Vec<_> = seq.iter().map(|e| element_to_doc(arena, e)).collect();
    let sep = arena.text(",").append(arena.line());
    arena
        .text("[")
        .append(
            arena
                .line_()
                .append(arena.intersperse(elems, sep))
                .nest(INDENT),
        )
        .append(arena.line_())
        .append(arena.text("]"))
        .group()
}

fn sexp_to_doc<'a>(arena: &'a Arena<'a>, seq: &Sequence) -> DocBuilder<'a, Arena<'a>> {
    if seq.is_empty() {
        return arena.text("()");
    }
    let elems: Vec<_> = seq.iter().map(|e| element_to_doc(arena, e)).collect();
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

fn struct_to_doc<'a>(arena: &'a Arena<'a>, s: &Struct) -> DocBuilder<'a, Arena<'a>> {
    if s.is_empty() {
        return arena.text("{}");
    }
    let fields: Vec<_> = s
        .fields()
        .map(|(name, value)| {
            let name_doc = match name.text() {
                Some(text) => symbol_to_doc(arena, text),
                None => arena.text("$0"),
            };
            name_doc
                .append(arena.text(":"))
                .append(arena.text(" "))
                .append(element_to_doc(arena, value))
        })
        .collect();
    let sep = arena.text(",").append(arena.line());
    arena
        .text("{")
        .append(
            arena
                .line()
                .append(arena.intersperse(fields, sep))
                .nest(INDENT),
        )
        .append(arena.line())
        .append(arena.text("}"))
        .group()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ion_rs::Element;

    fn format(input: &str) -> String {
        let seq = Element::read_all(input.as_bytes()).unwrap();
        let mut buf = Vec::new();
        prettyprint(&seq, &mut buf).unwrap();
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn scalars() {
        assert_eq!(format("null"), "null");
        assert_eq!(format("null.int"), "null.int");
        assert_eq!(format("true"), "true");
        assert_eq!(format("false"), "false");
        assert_eq!(format("42"), "42");
        assert_eq!(format("\"hello\""), "\"hello\"");
    }

    #[test]
    fn symbols() {
        assert_eq!(format("foo"), "foo");
        assert_eq!(format("'hello world'"), "'hello world'");
        assert_eq!(format("'null'"), "'null'");
        assert_eq!(format("'true'"), "'true'");
    }

    #[test]
    fn simple_struct() {
        assert_eq!(format("{ a: 1, b: 2 }"), "{ a: 1, b: 2 }");
    }

    #[test]
    fn simple_list() {
        assert_eq!(format("[1, 2, 3]"), "[1, 2, 3]");
    }

    #[test]
    fn simple_sexp() {
        assert_eq!(format("(+ 1 2)"), "('+' 1 2)");
        assert_eq!(format("(foo 1 2)"), "(foo 1 2)");
    }

    #[test]
    fn empty_containers() {
        assert_eq!(format("[]"), "[]");
        assert_eq!(format("()"), "()");
        assert_eq!(format("{}"), "{}");
    }

    #[test]
    fn annotations() {
        assert_eq!(format("foo::42"), "foo::42");
        assert_eq!(format("foo::bar::42"), "foo::bar::42");
    }

    #[test]
    fn nested_struct_breaks() {
        let input = "{ alpha: 1, bravo: 2, charlie: 3, delta: 4, echo: 5, foxtrot: 6, golf: 7, hotel: 8 }";
        let output = format(input);
        assert!(output.contains('\n'), "long struct should break across lines: {output}");
    }

    #[test]
    fn multiple_top_level() {
        assert_eq!(format("1 2 3"), "1\n2\n3");
    }

    #[test]
    fn empty_input() {
        assert_eq!(format(""), "");
    }
}
