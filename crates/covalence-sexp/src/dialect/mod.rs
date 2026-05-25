pub mod covalence;
pub mod smtlib;
pub mod wat;

pub use covalence::CovalenceDialect;
pub use smtlib::SmtLibDialect;
pub use wat::WatDialect;

/// Configuration for S-expression dialect differences.
pub trait Dialect {
    /// Parse and skip whitespace/comments.
    fn parse_trivia(&self, input: &mut &str);

    /// Delimiter for quoted symbols.
    fn quoted_symbol_delim(&self) -> Option<u8>;
}
