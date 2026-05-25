pub use bytes::Bytes;
use smol_str::SmolStr;

/// A parsed S-expression, generic over the atom type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SExp<A> {
    /// An atom value.
    Atom(A),
    /// A parenthesized list of S-expressions.
    List(Vec<SExp<A>>),
}

/// Default atom type: symbols and string literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    /// Unquoted symbol, keyword, numeral, or quoted symbol `|...|`.
    /// Stored as-is (quoted symbols have delimiters stripped).
    Symbol(SmolStr),
    /// String literal: format prefix + raw bytes.
    /// `""` -> format="", `b""` -> format="b", `json""` -> format="json".
    Str { format: SmolStr, bytes: Bytes },
}

/// Convenience alias for `SExp<Atom>`.
pub type SExpr = SExp<Atom>;

impl<A> SExp<A> {
    /// Transform all atoms in this S-expression tree.
    pub fn map<B>(self, f: &mut impl FnMut(A) -> B) -> SExp<B> {
        match self {
            SExp::Atom(a) => SExp::Atom(f(a)),
            SExp::List(children) => SExp::List(children.into_iter().map(|c| c.map(f)).collect()),
        }
    }

    /// Transform all atoms by reference.
    pub fn map_ref<B>(&self, f: &mut impl FnMut(&A) -> B) -> SExp<B> {
        match self {
            SExp::Atom(a) => SExp::Atom(f(a)),
            SExp::List(children) => SExp::List(children.iter().map(|c| c.map_ref(f)).collect()),
        }
    }
}

impl SExp<Atom> {
    /// Create a symbol atom.
    pub fn symbol(s: impl Into<SmolStr>) -> Self {
        SExp::Atom(Atom::Symbol(s.into()))
    }

    /// Create a string literal atom.
    pub fn string(format: impl Into<SmolStr>, bytes: impl Into<Bytes>) -> Self {
        SExp::Atom(Atom::Str {
            format: format.into(),
            bytes: bytes.into(),
        })
    }

    /// Create a list.
    pub fn list(children: Vec<SExpr>) -> Self {
        SExp::List(children)
    }

    /// Get the symbol name if this is a symbol atom.
    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            SExp::Atom(Atom::Symbol(s)) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Get (format, bytes) if this is a string literal atom.
    pub fn as_str(&self) -> Option<(&str, &[u8])> {
        match self {
            SExp::Atom(Atom::Str { format, bytes }) => Some((format.as_str(), bytes)),
            _ => None,
        }
    }

    /// Get the children if this is a list.
    pub fn as_list(&self) -> Option<&[SExpr]> {
        match self {
            SExp::List(children) => Some(children),
            _ => None,
        }
    }
}

/// A parse error with byte offset.
#[derive(Debug, Clone, thiserror::Error)]
#[error("offset {offset}: {message}")]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}
