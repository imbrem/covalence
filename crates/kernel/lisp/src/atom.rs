//! Shared atoms for Lisp frontends that distinguish exact integers from text.

/// A representation-neutral Lisp atom vocabulary.
///
/// `I` is supplied by the numeric API or a concrete backend. Keeping it
/// generic prevents the Lisp waist from choosing one integer representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LispAtom<I> {
    Symbol(Vec<u8>),
    String { format: String, bytes: Vec<u8> },
    Integer(I),
}

impl<I> LispAtom<I> {
    pub fn symbol(name: impl AsRef<[u8]>) -> Self {
        Self::Symbol(name.as_ref().to_vec())
    }

    pub fn string(format: impl Into<String>, bytes: impl Into<Vec<u8>>) -> Self {
        Self::String {
            format: format.into(),
            bytes: bytes.into(),
        }
    }

    pub fn map_integer<J>(self, map: impl FnOnce(I) -> J) -> LispAtom<J> {
        match self {
            Self::Symbol(symbol) => LispAtom::Symbol(symbol),
            Self::String { format, bytes } => LispAtom::String { format, bytes },
            Self::Integer(integer) => LispAtom::Integer(map(integer)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_representation_changes_without_touching_text_atoms() {
        assert_eq!(
            LispAtom::Integer(7u8).map_integer(u16::from),
            LispAtom::Integer(7u16)
        );
        assert_eq!(
            LispAtom::<u8>::symbol("name").map_integer(u16::from),
            LispAtom::Symbol(b"name".to_vec())
        );
    }
}
