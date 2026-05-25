use super::Dialect;
use super::covalence::parse_wat_trivia;
use crate::StringKind;

/// WAT dialect: `;;` line comments, `(; ;)` nested block comments,
/// `"..."` → ByteString, no `b"..."`, no `|...|`.
pub struct WatDialect;

impl Dialect for WatDialect {
    fn parse_trivia(&self, input: &mut &str) {
        parse_wat_trivia(input);
    }

    fn quoted_symbol_delim(&self) -> Option<u8> {
        None
    }

    fn bare_string_kind(&self) -> StringKind {
        StringKind::ByteString
    }

    fn supports_byte_prefix(&self) -> bool {
        false
    }
}
