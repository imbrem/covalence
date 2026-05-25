use covalence_parse::winnow::{Parser, token::take_while};

use crate::types::{ParseError, StringKind};
use crate::visitor::SExpVisitor;

/// Parse S-expressions from `input`, dispatching events to `visitor`.
pub fn parse_with<V: SExpVisitor>(input: &str, visitor: &mut V) -> Result<(), ParseError> {
    let original = input;
    let mut stream: &str = input;
    let mut depth = 0u32;

    loop {
        visitor.parse_trivia(&mut stream);
        if stream.is_empty() {
            if depth > 0 {
                return Err(ParseError {
                    offset: original.len(),
                    message: "unclosed '('".into(),
                });
            }
            break;
        }

        let offset = original.len() - stream.len();
        let b = stream.as_bytes()[0];

        match b {
            b'(' => {
                stream = &stream[1..];
                visitor.open_list();
                depth += 1;
            }
            b')' => {
                if depth == 0 {
                    return Err(ParseError {
                        offset,
                        message: "unexpected ')'".into(),
                    });
                }
                stream = &stream[1..];
                visitor.close_list();
                depth -= 1;
            }
            b'"' => {
                parse_string_token(&mut stream, visitor, original)?;
            }
            b'b' if visitor.supports_byte_prefix()
                && stream.len() > 1
                && stream.as_bytes()[1] == b'"' =>
            {
                stream = &stream[1..]; // skip 'b'
                parse_bytestring_token(&mut stream, visitor, original)?;
            }
            _ if Some(b) == visitor.quoted_symbol_delim() => {
                parse_quoted_symbol_token(&mut stream, visitor, original)?;
            }
            _ => {
                parse_atom_token(&mut stream, visitor, original)?;
            }
        }
    }

    Ok(())
}

fn parse_string_token<V: SExpVisitor>(
    stream: &mut &str,
    visitor: &mut V,
    original: &str,
) -> Result<(), ParseError> {
    let start = original.len() - stream.len();
    *stream = &stream[1..]; // skip opening '"'
    match visitor.bare_string_kind() {
        StringKind::String => {
            let s = parse_utf8_string_body(stream, start)?;
            visitor.string(&s);
        }
        StringKind::ByteString => {
            let bytes = parse_byte_string_body(stream, start)?;
            visitor.bytestring(&bytes);
        }
    }
    Ok(())
}

fn parse_bytestring_token<V: SExpVisitor>(
    stream: &mut &str,
    visitor: &mut V,
    original: &str,
) -> Result<(), ParseError> {
    let start = original.len() - stream.len();
    *stream = &stream[1..]; // skip opening '"'
    let bytes = parse_byte_string_body(stream, start)?;
    visitor.bytestring(&bytes);
    Ok(())
}

fn parse_utf8_string_body(stream: &mut &str, start: usize) -> Result<String, ParseError> {
    let mut s = String::new();
    loop {
        if stream.is_empty() {
            return Err(ParseError {
                offset: start,
                message: "unterminated string".into(),
            });
        }
        match stream.as_bytes()[0] {
            b'"' => {
                *stream = &stream[1..];
                return Ok(s);
            }
            b'\\' => {
                *stream = &stream[1..];
                parse_string_escape(stream, &mut s, start)?;
            }
            _ => {
                let c = stream.chars().next().unwrap();
                s.push(c);
                *stream = &stream[c.len_utf8()..];
            }
        }
    }
}

fn parse_string_escape(
    stream: &mut &str,
    out: &mut String,
    start: usize,
) -> Result<(), ParseError> {
    if stream.is_empty() {
        return Err(ParseError {
            offset: start,
            message: "unterminated string escape".into(),
        });
    }
    let b = stream.as_bytes()[0];
    *stream = &stream[1..];
    match b {
        b'\\' => out.push('\\'),
        b'"' => out.push('"'),
        b'n' => out.push('\n'),
        b't' => out.push('\t'),
        b'r' => out.push('\r'),
        b'a' => out.push('\x07'),
        b'b' => out.push('\x08'),
        b'f' => out.push('\x0c'),
        b'v' => out.push('\x0b'),
        b'x' => {
            let c = parse_hex_char(stream, 2, start)?;
            out.push(c);
        }
        b'u' => {
            if stream.starts_with('{') {
                *stream = &stream[1..];
                let c = parse_hex_char_until_brace(stream, start)?;
                out.push(c);
            } else {
                let c = parse_hex_char(stream, 4, start)?;
                out.push(c);
            }
        }
        b'U' => {
            let c = parse_hex_char(stream, 8, start)?;
            out.push(c);
        }
        other => {
            // Permissive: keep backslash + char
            out.push('\\');
            out.push(other as char);
        }
    }
    Ok(())
}

fn parse_hex_char(stream: &mut &str, digits: usize, start: usize) -> Result<char, ParseError> {
    let mut n: u32 = 0;
    for _ in 0..digits {
        let b = stream
            .as_bytes()
            .first()
            .filter(|b| b.is_ascii_hexdigit())
            .ok_or_else(|| ParseError {
                offset: start,
                message: "invalid hex escape".into(),
            })?;
        n = n * 16 + hex_val(*b);
        *stream = &stream[1..];
    }
    char::from_u32(n).ok_or_else(|| ParseError {
        offset: start,
        message: format!("invalid unicode codepoint: U+{n:04X}"),
    })
}

fn parse_hex_char_until_brace(stream: &mut &str, start: usize) -> Result<char, ParseError> {
    let mut n: u32 = 0;
    let mut count = 0;
    loop {
        if stream.is_empty() {
            return Err(ParseError {
                offset: start,
                message: "invalid \\u{...} escape".into(),
            });
        }
        let b = stream.as_bytes()[0];
        if b == b'}' {
            *stream = &stream[1..];
            if count == 0 {
                return Err(ParseError {
                    offset: start,
                    message: "empty \\u{} escape".into(),
                });
            }
            return char::from_u32(n).ok_or_else(|| ParseError {
                offset: start,
                message: format!("invalid unicode codepoint: U+{n:04X}"),
            });
        }
        if !b.is_ascii_hexdigit() {
            return Err(ParseError {
                offset: start,
                message: "invalid \\u{...} escape".into(),
            });
        }
        n = n * 16 + hex_val(b);
        count += 1;
        *stream = &stream[1..];
    }
}

fn hex_val(b: u8) -> u32 {
    match b {
        b'0'..=b'9' => (b - b'0') as u32,
        b'a'..=b'f' => (b - b'a' + 10) as u32,
        b'A'..=b'F' => (b - b'A' + 10) as u32,
        _ => unreachable!(),
    }
}

fn parse_byte_string_body(stream: &mut &str, start: usize) -> Result<Vec<u8>, ParseError> {
    let mut bytes = Vec::new();
    loop {
        if stream.is_empty() {
            return Err(ParseError {
                offset: start,
                message: "unterminated string".into(),
            });
        }
        match stream.as_bytes()[0] {
            b'"' => {
                *stream = &stream[1..];
                return Ok(bytes);
            }
            b'\\' => {
                *stream = &stream[1..];
                parse_byte_escape(stream, &mut bytes, start)?;
            }
            _ => {
                let c = stream.chars().next().unwrap();
                let mut buf = [0u8; 4];
                let encoded = c.encode_utf8(&mut buf);
                bytes.extend_from_slice(encoded.as_bytes());
                *stream = &stream[c.len_utf8()..];
            }
        }
    }
}

fn parse_byte_escape(stream: &mut &str, out: &mut Vec<u8>, start: usize) -> Result<(), ParseError> {
    if stream.is_empty() {
        return Err(ParseError {
            offset: start,
            message: "unterminated string escape".into(),
        });
    }
    let b = stream.as_bytes()[0];
    *stream = &stream[1..];
    match b {
        b'\\' => out.push(b'\\'),
        b'"' => out.push(b'"'),
        b'n' => out.push(b'\n'),
        b't' => out.push(b'\t'),
        b'r' => out.push(b'\r'),
        b'a' => out.push(0x07),
        b'b' => out.push(0x08),
        b'f' => out.push(0x0c),
        b'v' => out.push(0x0b),
        b'x' => {
            let byte = parse_hex_byte(stream, start)?;
            out.push(byte);
        }
        // Direct hex escape: \hh (two hex digits without prefix)
        _ if b.is_ascii_hexdigit() => {
            let second = stream
                .as_bytes()
                .first()
                .filter(|b| b.is_ascii_hexdigit())
                .ok_or_else(|| ParseError {
                    offset: start,
                    message: "invalid hex escape in bytestring".into(),
                })?;
            let byte = hex_val(b) as u8 * 16 + hex_val(*second) as u8;
            *stream = &stream[1..];
            out.push(byte);
        }
        other => {
            // Permissive: keep backslash + byte
            out.push(b'\\');
            out.push(other);
        }
    }
    Ok(())
}

fn parse_hex_byte(stream: &mut &str, start: usize) -> Result<u8, ParseError> {
    if stream.len() < 2 {
        return Err(ParseError {
            offset: start,
            message: "invalid \\x escape".into(),
        });
    }
    let hi = stream.as_bytes()[0];
    let lo = stream.as_bytes()[1];
    if !hi.is_ascii_hexdigit() || !lo.is_ascii_hexdigit() {
        return Err(ParseError {
            offset: start,
            message: "invalid \\x escape".into(),
        });
    }
    *stream = &stream[2..];
    Ok(hex_val(hi) as u8 * 16 + hex_val(lo) as u8)
}

fn parse_quoted_symbol_token<V: SExpVisitor>(
    stream: &mut &str,
    visitor: &mut V,
    original: &str,
) -> Result<(), ParseError> {
    let start = original.len() - stream.len();
    let delim = visitor.quoted_symbol_delim().unwrap();
    *stream = &stream[1..]; // skip opening delimiter
    let mut s = String::new();
    loop {
        if stream.is_empty() {
            return Err(ParseError {
                offset: start,
                message: "unterminated quoted symbol".into(),
            });
        }
        let b = stream.as_bytes()[0];
        if b == delim {
            *stream = &stream[1..];
            visitor.quoted_symbol(&s);
            return Ok(());
        }
        if b == b'\\' {
            *stream = &stream[1..];
            if stream.is_empty() {
                return Err(ParseError {
                    offset: start,
                    message: "unterminated quoted symbol".into(),
                });
            }
            let next = stream.as_bytes()[0];
            if next == delim {
                // \| → literal |
                s.push(delim as char);
                *stream = &stream[1..];
            } else if next == b'\\' {
                // \\ → literal \
                s.push('\\');
                *stream = &stream[1..];
            } else {
                // Permissive: keep backslash + char
                s.push('\\');
                let c = stream.chars().next().unwrap();
                s.push(c);
                *stream = &stream[c.len_utf8()..];
            }
        } else {
            let c = stream.chars().next().unwrap();
            s.push(c);
            *stream = &stream[c.len_utf8()..];
        }
    }
}

fn parse_atom_token<V: SExpVisitor>(
    stream: &mut &str,
    visitor: &mut V,
    original: &str,
) -> Result<(), ParseError> {
    let qsd = visitor.quoted_symbol_delim();
    let text: &str = take_while(1.., move |c: char| {
        if !c.is_ascii() {
            return true;
        }
        let b = c as u8;
        !b.is_ascii_whitespace() && !matches!(b, b'(' | b')' | b';' | b'"') && Some(b) != qsd
    })
    .parse_next(stream)
    .map_err(
        |_: covalence_parse::winnow::error::ErrMode<
            covalence_parse::winnow::error::ContextError,
        >| {
            ParseError {
                offset: original.len() - stream.len(),
                message: "expected atom".into(),
            }
        },
    )?;

    visitor.atom(text);
    Ok(())
}
