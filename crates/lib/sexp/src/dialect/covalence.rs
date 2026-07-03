use super::Dialect;

/// Covalence dialect: `;;` line comments, `(; ;)` nested block comments,
/// `"..."` → Str(format=""), `b"..."` → Str(format="b"), `|...|` quoted symbols.
pub struct CovalenceDialect;

impl Dialect for CovalenceDialect {
    fn parse_trivia(&self, input: &mut &str) {
        parse_wat_trivia(input);
    }

    fn quoted_symbol_delim(&self) -> Option<u8> {
        Some(b'|')
    }
}

/// Shared trivia parser for WAT-style comments (`;;` line, `(; ;)` block).
pub(crate) fn parse_wat_trivia(input: &mut &str) {
    loop {
        skip_whitespace(input);
        if input.starts_with(";;") {
            skip_line(input);
            continue;
        }
        if input.starts_with("(;") {
            skip_block_comment(input);
            continue;
        }
        break;
    }
}

fn skip_whitespace(input: &mut &str) {
    let n = input
        .as_bytes()
        .iter()
        .position(|b| !b.is_ascii_whitespace())
        .unwrap_or(input.len());
    *input = &input[n..];
}

fn skip_line(input: &mut &str) {
    match input.find('\n') {
        Some(pos) => *input = &input[pos + 1..],
        None => *input = "",
    }
}

/// Skip a `(; ... ;)` block comment, handling nesting.
fn skip_block_comment(input: &mut &str) {
    *input = &input[2..]; // skip "(;"
    let mut depth = 1u32;
    while depth > 0 && !input.is_empty() {
        if input.starts_with("(;") {
            *input = &input[2..];
            depth += 1;
        } else if input.starts_with(";)") {
            *input = &input[2..];
            depth -= 1;
        } else {
            let c = input.chars().next().unwrap();
            *input = &input[c.len_utf8()..];
        }
    }
}
