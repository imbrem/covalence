use super::Dialect;

/// Egglog dialect: `;` line comments, `"..."` → Str(format=""), no quoted
/// symbols.
///
/// Mirrors egglog 2.0's surface syntax exactly — see
/// [`egglog/src/ast/parse.rs`](https://github.com/egraphs-good/egglog/blob/main/src/ast/parse.rs).
/// Egglog identifiers are bare symbols (kebab-case is conventional but
/// `+`/`*`/`-` etc. are also legal); there is no `|…|` form.
pub struct EgglogDialect;

impl Dialect for EgglogDialect {
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
        None
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
