//! Theory state: sort algebra, type constructors, constants, and named axioms.

use std::collections::{HashMap, HashSet};

use smol_str::SmolStr;

use crate::types::*;

/// Sort algebra: tracks classes, subclass relations, and type constructor arities.
pub struct SortAlgebra {
    /// Known type classes.
    pub classes: HashSet<NameId>,
    /// Subclass relation: `(sub, super)` means `sub < super`.
    pub subclass: Vec<(NameId, NameId)>,
    /// Type constructor arities: `(tycon, arg_sorts, class)` means
    /// `tycon :: (s1, ..., sn) class`.
    pub arities: Vec<(NameId, Vec<Sort>, NameId)>,
}

impl SortAlgebra {
    pub fn new() -> Self {
        SortAlgebra {
            classes: HashSet::new(),
            subclass: Vec::new(),
            arities: Vec::new(),
        }
    }

    /// Add a new class to the sort algebra.
    pub fn add_class(&mut self, class: NameId) -> Result<(), PureError> {
        if !self.classes.insert(class) {
            return Err(PureError::ClassAlreadyDefined(class));
        }
        Ok(())
    }

    /// Add a subclass relation: `sub < super`.
    pub fn add_subclass(&mut self, sub: NameId, sup: NameId) -> Result<(), PureError> {
        if !self.classes.contains(&sub) {
            return Err(PureError::UnknownClass(sub));
        }
        if !self.classes.contains(&sup) {
            return Err(PureError::UnknownClass(sup));
        }
        self.subclass.push((sub, sup));
        Ok(())
    }

    /// Add an arity declaration: `tycon :: (s1, ..., sn) class`.
    pub fn add_arity(
        &mut self,
        tycon: NameId,
        arg_sorts: Vec<Sort>,
        class: NameId,
    ) -> Result<(), PureError> {
        if !self.classes.contains(&class) {
            return Err(PureError::UnknownClass(class));
        }
        self.arities.push((tycon, arg_sorts, class));
        Ok(())
    }

    /// Check if `sub` is a subclass of `sup` (reflexive, transitive closure).
    pub fn is_subclass(&self, sub: NameId, sup: NameId) -> bool {
        if sub == sup {
            return true;
        }
        let mut visited = HashSet::new();
        let mut stack = vec![sub];
        while let Some(current) = stack.pop() {
            if current == sup {
                return true;
            }
            if !visited.insert(current) {
                continue;
            }
            for &(s, p) in &self.subclass {
                if s == current {
                    stack.push(p);
                }
            }
        }
        false
    }
}

/// A theory: the accumulated state of definitions and axioms.
pub struct Theory {
    /// Sort algebra (classes, subclass relations, arities).
    pub sorts: SortAlgebra,
    /// Type constructor name → arity (number of type arguments).
    pub type_constructors: HashMap<NameId, usize>,
    /// Term constant name → most-general (polymorphic) type.
    pub constants: HashMap<NameId, TypId>,
    /// Named axioms (stored as theorem indices).
    pub axioms: HashMap<SmolStr, ThmId>,
}

impl Theory {
    pub fn new() -> Self {
        Theory {
            sorts: SortAlgebra::new(),
            type_constructors: HashMap::new(),
            constants: HashMap::new(),
            axioms: HashMap::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sort_algebra_add_class() {
        let mut sa = SortAlgebra::new();
        assert!(sa.add_class(10).is_ok());
        assert!(sa.add_class(10).is_err()); // duplicate
    }

    #[test]
    fn test_sort_algebra_subclass() {
        let mut sa = SortAlgebra::new();
        sa.add_class(10).unwrap();
        sa.add_class(11).unwrap();
        sa.add_class(12).unwrap();
        sa.add_subclass(10, 11).unwrap();
        sa.add_subclass(11, 12).unwrap();
        assert!(sa.is_subclass(10, 12)); // transitive
        assert!(sa.is_subclass(10, 10)); // reflexive
        assert!(!sa.is_subclass(12, 10)); // not reverse
    }

    #[test]
    fn test_sort_algebra_unknown_class() {
        let mut sa = SortAlgebra::new();
        assert!(sa.add_subclass(10, 11).is_err());
    }

    #[test]
    fn test_theory_new() {
        let theory = Theory::new();
        assert!(theory.type_constructors.is_empty());
        assert!(theory.constants.is_empty());
        assert!(theory.axioms.is_empty());
    }
}
