//! Literal facade — the single peripheral chokepoint for kernel literals.
//!
//! Everything outside `covalence-core` that needs to BUILD or RECOGNIZE a
//! concrete numeral/blob term goes through these helpers instead of the
//! kernel literal constructors / `TermKind` matchers. When the literal
//! `TermKind` variants are deleted (toHOL purge: `Int`/`Blob`/`SmallInt`
//! first, `Nat`/`Succ` and `Bool` behind maintainer checkpoints), only the
//! transitional [`Lit`] bridge in `covalence-core` flips its build/recognize
//! targets to the defined numeral/cons forms — consumers of this facade
//! never move again.
//!
//! The facade is untrusted convenience: it mints no theorems and carries no
//! soundness obligation.

use covalence_core::seam::Lit;
use covalence_core::{Term, TermKind};
use covalence_types::{Bytes, Int, Nat};

/// Build the concrete `nat` term for `n` (today the kernel `nat` literal).
pub fn mk_nat(n: impl Into<Nat>) -> Term {
    Lit::Nat(n.into()).to_term()
}

/// Build the concrete `int` term for `i` (today the kernel `int` literal).
pub fn mk_int(i: impl Into<Int>) -> Term {
    Lit::Int(i.into()).to_term()
}

/// Build the concrete `bytes` term for `b` (today the kernel blob literal).
pub fn mk_blob(b: impl Into<Bytes>) -> Term {
    Lit::Bytes(b.into()).to_term()
}

/// Recognize a concrete `nat` term, returning its value.
pub fn as_nat(t: &Term) -> Option<Nat> {
    match Lit::from_term(t)? {
        Lit::Nat(n) => Some(n),
        _ => None,
    }
}

/// Recognize a concrete `int` term, returning its value.
pub fn as_int(t: &Term) -> Option<Int> {
    match Lit::from_term(t)? {
        Lit::Int(i) => Some(i),
        _ => None,
    }
}

/// Recognize a concrete `bytes` term, returning its value.
pub fn as_blob(t: &Term) -> Option<Bytes> {
    match Lit::from_term(t)? {
        Lit::Bytes(b) => Some(b),
        _ => None,
    }
}

/// A short diagnostic name for a [`TermKind`] variant (error messages only).
///
/// Lives here so peripheral crates don't match the literal variants
/// themselves; the literal arms die with the variants.
pub fn kind_name(k: &TermKind) -> &'static str {
    match k {
        TermKind::Bound(_) => "bound",
        TermKind::Free(..) => "free",
        TermKind::Const(..) => "const",
        TermKind::App(..) => "app",
        TermKind::Abs(..) => "abs",
        TermKind::Blob(_) => "blob",
        TermKind::Nat(_) => "nat",
        TermKind::Int(_) => "int",
        TermKind::SmallInt(_) => "smallint",
        TermKind::Bool(_) => "bool",
        TermKind::Eq(_) => "eq",
        TermKind::Select(_) => "select",
        TermKind::Succ => "succ",
        TermKind::Spec(..) => "spec",
        TermKind::SpecAbs(..) => "specabs",
        TermKind::SpecRep(..) => "specrep",
        TermKind::FreshConst(..) => "fresh-const",
        TermKind::Def(_) => "def",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_through_the_facade() {
        let n = mk_nat(42u32);
        assert_eq!(as_nat(&n), Some(Nat::from_inner(42u32.into())));
        assert_eq!(as_int(&n), None);
        assert_eq!(as_blob(&n), None);

        let i = mk_int(-7i128);
        assert_eq!(as_int(&i), Some(Int::from(-7i128)));
        assert_eq!(as_nat(&i), None);

        let b = mk_blob(vec![1u8, 2, 3]);
        assert_eq!(as_blob(&b), Some(Bytes::from(vec![1u8, 2, 3])));
        assert_eq!(as_nat(&b), None);
    }

    #[test]
    fn recognizers_reject_non_literals() {
        let x = Term::free("x", covalence_core::Type::nat());
        assert_eq!(as_nat(&x), None);
        assert_eq!(as_int(&x), None);
        assert_eq!(as_blob(&x), None);
        assert_eq!(kind_name(x.kind()), "free");
    }
}
