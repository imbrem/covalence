//! Stable identifiers for common applicative Lisp primitives.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LispPrimitive {
    Cons,
    Car,
    Cdr,
    Atom,
    Consp,
    Null,
    Not,
    Integer,
    Equal,
    Add,
    Subtract,
    Multiply,
    LessEqual,
    Append,
    Read,
    Write,
}

impl LispPrimitive {
    /// Number of operands accepted by this primitive.
    ///
    /// Surface forms such as `if` and `quote` are deliberately absent: they
    /// control evaluation and belong to a dialect's syntax, not its
    /// applicative primitive vocabulary.
    pub const fn arity(self) -> usize {
        match self {
            Self::Read => 0,
            Self::Car
            | Self::Cdr
            | Self::Atom
            | Self::Consp
            | Self::Null
            | Self::Not
            | Self::Integer
            | Self::Write => 1,
            Self::Cons
            | Self::Equal
            | Self::Add
            | Self::Subtract
            | Self::Multiply
            | Self::LessEqual
            | Self::Append => 2,
        }
    }

    /// Whether evaluation must be delegated to an effect handler.
    pub const fn is_effectful(self) -> bool {
        matches!(self, Self::Read | Self::Write)
    }

    /// Whether this primitive belongs to the exact-integer vocabulary.
    pub const fn is_numeric(self) -> bool {
        matches!(
            self,
            Self::Add | Self::Subtract | Self::Multiply | Self::LessEqual
        )
    }
}

#[cfg(test)]
mod tests {
    use super::LispPrimitive;

    #[test]
    fn primitive_metadata_is_structural_not_surface_policy() {
        assert_eq!(LispPrimitive::Read.arity(), 0);
        assert_eq!(LispPrimitive::Car.arity(), 1);
        assert_eq!(LispPrimitive::Cons.arity(), 2);
        assert!(LispPrimitive::Write.is_effectful());
        assert!(!LispPrimitive::Cons.is_effectful());
        assert!(LispPrimitive::Add.is_numeric());
        assert!(!LispPrimitive::Equal.is_numeric());
    }
}
