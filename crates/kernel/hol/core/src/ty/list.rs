//! `TypeList` — an ordered list of type arguments.
//!
//! A thin, opaque wrapper around `Vec<Type>` used everywhere a spec /
//! type-constructor carries its positional type arguments
//! (`TypeKind::Spec`, `TypeKind::Tycon`, `TermKind::Spec`, the
//! `abs`/`rep` coercions, …). Centralising the representation keeps
//! those sites uniform and lets the backing container change later.
//!
//! `TypeList` derefs to `[Type]`, so slice methods (`len`,
//! `is_empty`, `iter`, indexing, `==` against a slice) work directly.

use std::ops::Deref;

use super::ty::Type;

/// An ordered, immutable list of type arguments.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct TypeList(Vec<Type>);

impl TypeList {
    /// The empty list.
    pub fn new() -> Self {
        TypeList(Vec::new())
    }

    /// Borrow the arguments as a slice.
    pub fn as_slice(&self) -> &[Type] {
        &self.0
    }

    /// Consume into the backing `Vec`.
    pub fn into_vec(self) -> Vec<Type> {
        self.0
    }

    /// Iterate over the arguments.
    pub fn iter(&self) -> std::slice::Iter<'_, Type> {
        self.0.iter()
    }
}

impl Deref for TypeList {
    type Target = [Type];
    fn deref(&self) -> &[Type] {
        &self.0
    }
}

impl From<Vec<Type>> for TypeList {
    fn from(v: Vec<Type>) -> Self {
        TypeList(v)
    }
}

impl From<TypeList> for Vec<Type> {
    fn from(l: TypeList) -> Self {
        l.0
    }
}

impl FromIterator<Type> for TypeList {
    fn from_iter<I: IntoIterator<Item = Type>>(iter: I) -> Self {
        TypeList(iter.into_iter().collect())
    }
}

impl<'a> IntoIterator for &'a TypeList {
    type Item = &'a Type;
    type IntoIter = std::slice::Iter<'a, Type>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl IntoIterator for TypeList {
    type Item = Type;
    type IntoIter = std::vec::IntoIter<Type>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl std::fmt::Debug for TypeList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
