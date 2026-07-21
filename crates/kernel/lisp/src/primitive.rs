//! Stable identifiers for common applicative Lisp primitives.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LispPrimitive {
    Cons,
    Car,
    Cdr,
    Atom,
    Consp,
    Null,
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
