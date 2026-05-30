use std::sync::Arc;

use super::Name;

/// Universe level.
///
/// Lean's type theory uses a cumulative universe hierarchy.
/// `IMax(a, b)` is 0 when `b` evaluates to 0, otherwise `Max(a, b)` —
/// this is critical for Prop (universe 0) to be impredicative.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Level {
    /// Universe 0 (Prop).
    Zero,
    /// Successor universe: `u + 1`.
    Succ(Arc<Level>),
    /// Maximum of two universes: `max u v`.
    Max(Arc<Level>, Arc<Level>),
    /// Impredicative maximum: 0 if `rhs` is 0, otherwise `max lhs rhs`.
    IMax(Arc<Level>, Arc<Level>),
    /// Universe parameter (bound by declaration-level polymorphism).
    Param(Name),
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use smol_str::SmolStr;

    use super::*;

    #[test]
    fn zero() {
        let l = Level::Zero;
        assert_eq!(l, Level::Zero);
    }

    #[test]
    fn succ_chain() {
        // Type 2 = Succ(Succ(Zero))
        let l = Arc::new(Level::Succ(Arc::new(Level::Succ(Arc::new(Level::Zero)))));
        match l.as_ref() {
            Level::Succ(inner) => match inner.as_ref() {
                Level::Succ(inner2) => assert_eq!(*inner2.as_ref(), Level::Zero),
                _ => panic!("expected Succ"),
            },
            _ => panic!("expected Succ"),
        }
    }

    #[test]
    fn param() {
        let name = Name::Str(Arc::new(Name::Anon), SmolStr::new("u"));
        let l = Level::Param(name.clone());
        assert_eq!(l, Level::Param(name));
    }

    #[test]
    fn max_and_imax() {
        let zero = Arc::new(Level::Zero);
        let one = Arc::new(Level::Succ(zero.clone()));
        let m = Level::Max(zero.clone(), one.clone());
        let im = Level::IMax(zero.clone(), one.clone());
        assert_ne!(m, im);
    }
}
