use std::sync::Arc;

use super::expr::Expr;
use super::name::Name;

/// Reducibility hint for definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u32),
}

/// Safety level of a declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Safety {
    Safe,
    Unsafe,
    Partial,
}

/// Kind of quotient declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// Axiom declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub is_unsafe: bool,
}

/// Definition declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefnInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub value: Arc<Expr>,
    pub hints: ReducibilityHint,
    pub safety: Safety,
    pub all: Vec<Name>,
}

/// Theorem declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThmInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub value: Arc<Expr>,
    pub all: Vec<Name>,
}

/// Opaque declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpaqueInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub value: Arc<Expr>,
    pub is_unsafe: bool,
    pub all: Vec<Name>,
}

/// Quotient declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub kind: QuotKind,
}

/// Inductive type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub num_params: u32,
    pub num_indices: u32,
    pub all: Vec<Name>,
    pub ctors: Vec<Name>,
    pub is_recursive: bool,
    pub is_reflexive: bool,
    pub is_nested: bool,
    pub is_unsafe: bool,
}

/// Constructor declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtorInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub induct: Name,
    pub cidx: u32,
    pub num_params: u32,
    pub num_fields: u32,
    pub is_unsafe: bool,
}

/// Recursor rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecRule {
    pub ctor: Name,
    pub nfields: u32,
    pub rhs: Arc<Expr>,
}

/// Recursor declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecInfo {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Arc<Expr>,
    pub all: Vec<Name>,
    pub num_params: u32,
    pub num_indices: u32,
    pub num_motives: u32,
    pub num_minors: u32,
    pub rules: Vec<RecRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// A Lean declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Axiom(AxiomInfo),
    Defn(DefnInfo),
    Thm(ThmInfo),
    Opaque(OpaqueInfo),
    Quot(QuotInfo),
    Induct(InductInfo),
    Ctor(CtorInfo),
    Rec(RecInfo),
}

impl Decl {
    /// The name of this declaration.
    pub fn name(&self) -> &Name {
        match self {
            Decl::Axiom(d) => &d.name,
            Decl::Defn(d) => &d.name,
            Decl::Thm(d) => &d.name,
            Decl::Opaque(d) => &d.name,
            Decl::Quot(d) => &d.name,
            Decl::Induct(d) => &d.name,
            Decl::Ctor(d) => &d.name,
            Decl::Rec(d) => &d.name,
        }
    }

    /// The type of this declaration.
    pub fn ty(&self) -> &Arc<Expr> {
        match self {
            Decl::Axiom(d) => &d.ty,
            Decl::Defn(d) => &d.ty,
            Decl::Thm(d) => &d.ty,
            Decl::Opaque(d) => &d.ty,
            Decl::Quot(d) => &d.ty,
            Decl::Induct(d) => &d.ty,
            Decl::Ctor(d) => &d.ty,
            Decl::Rec(d) => &d.ty,
        }
    }
}
