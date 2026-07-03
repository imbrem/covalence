use super::Dialect;
use super::covalence::parse_wat_trivia;

/// WAT dialect: `;;` line comments, `(; ;)` nested block comments,
/// `"..."` → Str(format=""), no `|...|`.
pub struct WatDialect;

impl Dialect for WatDialect {
    fn parse_trivia(&self, input: &mut &str) {
        parse_wat_trivia(input);
    }

    fn quoted_symbol_delim(&self) -> Option<u8> {
        None
    }
}
