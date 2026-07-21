//! Shared atoms for Lisp frontends that distinguish exact integers from text.

/// A representation-neutral Lisp atom vocabulary.
///
/// `I` is supplied by the numeric API or a concrete backend. Keeping it
/// generic prevents the Lisp waist from choosing one integer representation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LispAtom<I, B = Vec<u8>, F = String> {
    Symbol(B),
    String { format: F, bytes: B },
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
}

impl<I, B, F> LispAtom<I, B, F> {
    pub fn map_integer<J>(self, map: impl FnOnce(I) -> J) -> LispAtom<J, B, F> {
        match self {
            Self::Symbol(symbol) => LispAtom::Symbol(symbol),
            Self::String { format, bytes } => LispAtom::String { format, bytes },
            Self::Integer(integer) => LispAtom::Integer(map(integer)),
        }
    }

    /// Change the byte and format-label representations without inspecting
    /// integer payloads.
    pub fn map_text<C, G>(
        self,
        mut map_bytes: impl FnMut(B) -> C,
        map_format: impl FnOnce(F) -> G,
    ) -> LispAtom<I, C, G> {
        match self {
            Self::Symbol(symbol) => LispAtom::Symbol(map_bytes(symbol)),
            Self::String { format, bytes } => LispAtom::String {
                format: map_format(format),
                bytes: map_bytes(bytes),
            },
            Self::Integer(integer) => LispAtom::Integer(integer),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_representation_changes_without_touching_text_atoms() {
        assert_eq!(
            LispAtom::<u8>::Integer(7u8).map_integer(u16::from),
            LispAtom::Integer(7u16)
        );
        assert_eq!(
            LispAtom::<u8>::symbol("name").map_integer(u16::from),
            LispAtom::Symbol(b"name".to_vec())
        );
    }

    #[test]
    fn text_representation_changes_without_touching_integers() {
        let atom = LispAtom::<u8>::string("utf-8", b"hello".to_vec());
        assert_eq!(
            atom.map_text(Box::<[u8]>::from, Box::<str>::from),
            LispAtom::<u8, Box<[u8]>, Box<str>>::String {
                format: Box::from("utf-8"),
                bytes: Box::from(&b"hello"[..]),
            }
        );
        assert_eq!(
            LispAtom::<u8>::Integer(7).map_text(Box::<[u8]>::from, Box::<str>::from),
            LispAtom::<u8, Box<[u8]>, Box<str>>::Integer(7)
        );
    }
}
