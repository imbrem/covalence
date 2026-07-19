//! The **spec model**: plain-data descriptions of simple inductive types.
//!
//! A spec deliberately embeds *no* logic values beyond the external-sort
//! token `X` (usually instantiated at a logic's `Type`, or at a symbolic
//! sort name a backend resolves). It is `Clone`/`Eq`/`Hash` whenever `X`
//! is, closure-free, and order-preserving — so a spec can be serialized,
//! content-addressed, and compared, and constructors are index-addressable
//! (declaration order everywhere).

use smol_str::SmolStr;

use crate::error::SpecError;
use crate::fixpoint::FixpointSpec;
use crate::polynomial::{FieldSpec, PolynomialSpec, Position, VariantCase};

/// One argument position of a constructor.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ArgSort<X> {
    /// A direct recursive occurrence of the type being defined.
    Rec,
    /// A non-recursive argument of external sort `X` (the backend maps `X`
    /// to its logic's type).
    Ext(X),
}

impl<X> ArgSort<X> {
    /// Whether this is a recursive occurrence.
    pub fn is_rec(&self) -> bool {
        matches!(self, ArgSort::Rec)
    }

    /// Map the external sort, preserving `Rec`.
    pub fn map_ext<Y>(self, f: impl FnOnce(X) -> Y) -> ArgSort<Y> {
        match self {
            ArgSort::Rec => ArgSort::Rec,
            ArgSort::Ext(x) => ArgSort::Ext(f(x)),
        }
    }
}

/// A single constructor `C : A₁ → … → Aₙ → T`.
///
/// Argument names are **binder hints**: backends bind constructor arguments
/// by these names in generated theorems (freeness, induction clauses), so
/// readable names make the generated statements legible. They are also
/// **reserved**: a motive or step term passed to the bundle should not use
/// them as its own free-variable names (see [`crate::theory`]).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CtorSpec<X> {
    /// The constructor name (e.g. `"atom"`, `"scons"`).
    pub name: SmolStr,
    /// Binder-name hints + sorts, in declaration order.
    pub args: Vec<(SmolStr, ArgSort<X>)>,
}

impl<X> CtorSpec<X> {
    /// A constructor with the given argument signature.
    pub fn new(
        name: impl Into<SmolStr>,
        args: impl IntoIterator<Item = (impl Into<SmolStr>, ArgSort<X>)>,
    ) -> Self {
        CtorSpec {
            name: name.into(),
            args: args.into_iter().map(|(n, s)| (n.into(), s)).collect(),
        }
    }

    /// A nullary constructor (a constant of the inductive type).
    pub fn nullary(name: impl Into<SmolStr>) -> Self {
        CtorSpec {
            name: name.into(),
            args: Vec::new(),
        }
    }

    /// Number of arguments.
    pub fn arity(&self) -> usize {
        self.args.len()
    }

    /// The recursive argument positions, in order.
    pub fn rec_positions(&self) -> impl Iterator<Item = usize> + '_ {
        self.args
            .iter()
            .enumerate()
            .filter(|(_, (_, s))| s.is_rec())
            .map(|(i, _)| i)
    }

    /// Whether the constructor has any recursive argument.
    pub fn is_recursive(&self) -> bool {
        self.args.iter().any(|(_, s)| s.is_rec())
    }

    /// Map the external sorts, preserving structure.
    pub fn map_ext<Y>(self, mut f: impl FnMut(X) -> Y) -> CtorSpec<Y> {
        CtorSpec {
            name: self.name,
            args: self
                .args
                .into_iter()
                .map(|(n, s)| (n, s.map_ext(&mut f)))
                .collect(),
        }
    }
}

/// The spec of a simple inductive type: a name and a non-empty, ordered
/// list of constructors.
///
/// **Scope (v1):** single (no mutual blocks), non-indexed, strictly
/// positive, first-order, directly recursive (every recursive argument is
/// the type itself). Parameterized specs (`list α` with a spec-level
/// parameter), mutual/nested recursion, and indexed families are explicit
/// LATER scope — each lands as a new [`ArgSort`]/spec variant plus a
/// backend capability flag.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InductiveSpec<X> {
    /// The type's name (e.g. `"sexpr"`).
    pub name: SmolStr,
    /// The constructors, in declaration order.
    pub ctors: Vec<CtorSpec<X>>,
}

impl<X> InductiveSpec<X> {
    /// A spec from parts. Call [`validate`](Self::validate) before handing
    /// to a backend (backends validate too).
    pub fn new(name: impl Into<SmolStr>, ctors: Vec<CtorSpec<X>>) -> Self {
        InductiveSpec {
            name: name.into(),
            ctors,
        }
    }

    /// A pure enumeration: nullary constructors only.
    pub fn enum_of(
        name: impl Into<SmolStr>,
        ctor_names: impl IntoIterator<Item = impl Into<SmolStr>>,
    ) -> Self {
        InductiveSpec {
            name: name.into(),
            ctors: ctor_names.into_iter().map(CtorSpec::nullary).collect(),
        }
    }

    /// Number of constructors.
    pub fn arity(&self) -> usize {
        self.ctors.len()
    }

    /// Structural well-formedness: non-empty constructor list, non-empty
    /// distinct constructor names, distinct argument names within each
    /// constructor.
    pub fn validate(&self) -> Result<(), SpecError> {
        if self.ctors.is_empty() {
            return Err(SpecError::EmptySpec(self.name.clone()));
        }
        for (i, c) in self.ctors.iter().enumerate() {
            if c.name.is_empty() {
                return Err(SpecError::EmptyName { ctor: i });
            }
            if self.ctors[..i].iter().any(|d| d.name == c.name) {
                return Err(SpecError::DuplicateCtor(c.name.clone()));
            }
            for (j, (n, _)) in c.args.iter().enumerate() {
                if n.is_empty() {
                    return Err(SpecError::EmptyName { ctor: i });
                }
                if c.args[..j].iter().any(|(m, _)| m == n) {
                    return Err(SpecError::DuplicateArg {
                        ctor: c.name.clone(),
                        arg: n.clone(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Map the external sorts (e.g. resolve symbolic sort names to a
    /// logic's types), preserving all structure.
    pub fn map_ext<Y>(self, mut f: impl FnMut(X) -> Y) -> InductiveSpec<Y> {
        InductiveSpec {
            name: self.name,
            ctors: self.ctors.into_iter().map(|c| c.map_ext(&mut f)).collect(),
        }
    }

    /// View this legacy simple-inductive declaration as the general
    /// polynomial-functor fixpoint API.
    ///
    /// This is a structural conversion only: it does not choose a backend or
    /// change the membership-relativized theorem contract.
    pub fn into_fixpoint(self) -> FixpointSpec<X> {
        let name = self.name;
        let variants = self
            .ctors
            .into_iter()
            .map(|ctor| {
                VariantCase::new(
                    ctor.name,
                    ctor.args
                        .into_iter()
                        .map(|(name, sort)| {
                            let position = match sort {
                                ArgSort::Rec => Position::Var,
                                ArgSort::Ext(external) => Position::Param(external),
                            };
                            FieldSpec::new(name, position)
                        })
                        .collect(),
                )
            })
            .collect();
        FixpointSpec::new(name.clone(), PolynomialSpec::new(name, variants))
    }

    /// Build the compatibility simple-inductive form from a polynomial
    /// fixpoint declaration.
    pub fn from_fixpoint(spec: FixpointSpec<X>) -> Self {
        InductiveSpec {
            name: spec.name,
            ctors: spec
                .functor
                .variants
                .into_iter()
                .map(|variant| CtorSpec {
                    name: variant.name,
                    args: variant
                        .fields
                        .into_iter()
                        .map(|field| {
                            let sort = match field.position {
                                Position::Var => ArgSort::Rec,
                                Position::Param(external) => ArgSort::Ext(external),
                            };
                            (field.name, sort)
                        })
                        .collect(),
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sexpr_like() -> InductiveSpec<&'static str> {
        InductiveSpec::new(
            "sexpr",
            vec![
                CtorSpec::new("atom", [("b", ArgSort::Ext("bytes"))]),
                CtorSpec::nullary("snil"),
                CtorSpec::new("scons", [("h", ArgSort::Rec), ("t", ArgSort::Rec)]),
            ],
        )
    }

    #[test]
    fn spec_shape_queries() {
        let s = sexpr_like();
        assert!(s.validate().is_ok());
        assert_eq!(s.arity(), 3);
        assert!(!s.ctors[0].is_recursive());
        assert!(!s.ctors[1].is_recursive());
        assert!(s.ctors[2].is_recursive());
        assert_eq!(s.ctors[2].rec_positions().collect::<Vec<_>>(), vec![0, 1]);
        assert_eq!(s.ctors[0].rec_positions().count(), 0);
    }

    #[test]
    fn validate_rejects_duplicates_and_empties() {
        let empty: InductiveSpec<&str> = InductiveSpec::new("void", vec![]);
        assert!(matches!(empty.validate(), Err(SpecError::EmptySpec(_))));

        let dup = InductiveSpec::<&str>::enum_of("b", ["t", "t"]);
        assert!(matches!(dup.validate(), Err(SpecError::DuplicateCtor(_))));

        let dup_arg = InductiveSpec::new(
            "p",
            vec![CtorSpec::new(
                "mk",
                [("x", ArgSort::<&str>::Rec), ("x", ArgSort::Rec)],
            )],
        );
        assert!(matches!(
            dup_arg.validate(),
            Err(SpecError::DuplicateArg { .. })
        ));
    }

    #[test]
    fn map_ext_preserves_structure_and_eq_hash_work() {
        let s = sexpr_like();
        let t = s.clone().map_ext(|x| x.to_string());
        assert_eq!(t.ctors[0].args[0].1, ArgSort::Ext("bytes".to_string()));
        assert_eq!(t.ctors[2].args[0].1, ArgSort::Rec);
        // Eq/Hash: identical specs compare equal and hash equal.
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(sexpr_like());
        assert!(set.contains(&s));
    }

    #[test]
    fn polynomial_fixpoint_round_trip_preserves_legacy_spec() {
        let spec = sexpr_like();
        assert_eq!(
            InductiveSpec::from_fixpoint(spec.clone().into_fixpoint()),
            spec
        );
    }
}
