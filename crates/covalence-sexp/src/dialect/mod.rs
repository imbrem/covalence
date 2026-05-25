pub mod covalence;
pub mod smtlib;
pub mod wat;

use crate::StringKind;

pub use covalence::CovalenceDialect;
pub use smtlib::SmtLibDialect;
pub use wat::WatDialect;

/// Configuration for S-expression dialect differences.
pub trait Dialect {
    /// Parse and skip whitespace/comments.
    fn parse_trivia(&self, input: &mut &str);

    /// Delimiter for quoted symbols.
    fn quoted_symbol_delim(&self) -> Option<u8>;

    /// What a bare `"..."` produces.
    fn bare_string_kind(&self) -> StringKind;

    /// Whether `b"..."` prefix is supported.
    fn supports_byte_prefix(&self) -> bool;
}
