//! [`Lit`] — native literal values, the argument currency of the
//! computation-certificate rules hosted in `covalence-hol-eval`.
//!
//! TRANSITIONAL (D3, dies with the kernel literal leaves): while
//! `TermKind::{Bool, Nat, Int, SmallInt, Blob}` exist, `Lit` is the one
//! native-value ↔ literal-leaf bridge. It stays in core because the literal
//! leaves (and their types) do; the certificate *rules* that consume it live
//! at the `CoreEval` tier in `covalence-hol-eval`. Reading/building literal
//! terms mints nothing.

use covalence_types::{Bytes, Int, Nat};

use crate::term::{SmallIntLiteral, Term, TermKind, Type};

/// A native literal value — the argument currency of the family certificate
/// rules. One variant per kernel literal kind (`Bool` / `Nat` / `Int` /
/// fixed-width `SmallInt` / `Bytes`).
///
/// TRANSITIONAL reify target: [`Lit::to_term`] builds today's kernel literal
/// leaves (`Term::nat_lit` & co.); at kernel-literal deletion the target
/// flips to the defined numeral/cons forms and callers don't move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lit {
    /// A `bool` literal (`TermKind::Bool`).
    Bool(bool),
    /// A natural-number literal (`TermKind::Nat`).
    Nat(Nat),
    /// An integer literal (`TermKind::Int`).
    Int(Int),
    /// A fixed-width integer literal (`TermKind::SmallInt`).
    Small(SmallIntLiteral),
    /// A bytestring literal (`TermKind::Blob`).
    Bytes(Bytes),
}

impl Lit {
    /// The kernel literal [`Term`] denoting this value (the transitional
    /// literal-numeral reify target).
    pub fn to_term(&self) -> Term {
        match self {
            Lit::Bool(b) => Term::bool_lit(*b),
            Lit::Nat(n) => Term::nat_lit(n.clone()),
            Lit::Int(i) => Term::int_lit(i.clone()),
            Lit::Small(l) => Term::small_int(*l),
            Lit::Bytes(b) => Term::blob(b.clone()),
        }
    }

    /// Read a literal leaf back off a [`Term`] — the (untrusted) recognizer
    /// counterpart of [`Lit::to_term`]. `None` for any non-literal.
    pub fn from_term(t: &Term) -> Option<Lit> {
        match t.kind() {
            TermKind::Bool(b) => Some(Lit::Bool(*b)),
            TermKind::Nat(n) => Some(Lit::Nat(n.clone())),
            TermKind::Int(i) => Some(Lit::Int(i.clone())),
            TermKind::SmallInt(l) => Some(Lit::Small(*l)),
            TermKind::Blob(b) => Some(Lit::Bytes(b.clone())),
            _ => None,
        }
    }

    /// The HOL type of this literal (the kernel's literal typing commitment).
    pub fn hol_type(&self) -> Type {
        match self {
            Lit::Bool(_) => Type::bool(),
            Lit::Nat(_) => Type::nat(),
            Lit::Int(_) => Type::int(),
            Lit::Small(l) => l.ty(),
            Lit::Bytes(_) => Type::bytes(),
        }
    }
}
