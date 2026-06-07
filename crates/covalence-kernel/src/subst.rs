//! Term / type substitutions carried by import edges.
//!
//! Each [`crate::arena::Import`] edge from arena `A` to source arena
//! `B` carries a [`TermSubst`] and a [`TypeSubst`] that map source
//! names (`StrId`s in `B`) to local refs in `A`. When the kernel
//! walks through a [`crate::term::TermDef::Foreign`] or
//! [`crate::ty::TypeDef::Foreign`] ref, unmapped names default to the
//! "epsilon of true" sentinel of the appropriate type — well-formed,
//! but trivially uninformative.
//!
//! Each entry's `name: StrId` is interpreted **against the source
//! arena's string table**, so a [`TermSubst`] / [`TypeSubst`] is
//! meaningful only relative to the specific source arena it was
//! created for.

use crate::id::StrId;
use crate::term::TermRef;
use crate::ty::TypeRef;

/// A finite map from source `StrId` (free-variable names) to local
/// `TermRef`s. Entries beyond the list are treated as unmapped.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TermSubst {
    pub entries: Vec<(StrId, TermRef)>,
}

impl TermSubst {
    /// Construct an empty substitution.
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Look up `name` in the substitution. Returns `None` if unmapped.
    pub fn lookup(&self, name: StrId) -> Option<TermRef> {
        self.entries
            .iter()
            .find_map(|(k, v)| (*k == name).then_some(*v))
    }
}

/// A finite map from source `StrId` (type-variable names) to local
/// `TypeRef`s. Entries beyond the list are treated as unmapped.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TypeSubst {
    pub entries: Vec<(StrId, TypeRef)>,
}

impl TypeSubst {
    /// Construct an empty substitution.
    pub fn empty() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Look up `name` in the substitution. Returns `None` if unmapped.
    pub fn lookup(&self, name: StrId) -> Option<TypeRef> {
        self.entries
            .iter()
            .find_map(|(k, v)| (*k == name).then_some(*v))
    }
}
