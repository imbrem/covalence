use super::Dialect;

/// SMT-LIB dialect: `;` line comments, `|...|` quoted symbols, `"..."` → Str(format="").
pub struct SmtLibDialect;

impl Dialect for SmtLibDialect {
    fn parse_trivia(&self, input: &mut &str) {
        loop {
            skip_whitespace(input);
            if input.starts_with(';') {
                skip_line(input);
            } else {
                break;
            }
        }
    }

    fn quoted_symbol_delim(&self) -> Option<u8> {
        Some(b'|')
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
