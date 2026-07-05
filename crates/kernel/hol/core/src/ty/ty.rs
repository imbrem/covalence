//! The type language: `Type` and `TypeKind`.
//!
//! Type identity is structural (`PartialEq` on `TypeKind`); the
//! constructors below return `Arc`-wrapped instances so identical
//! types share a single allocation. The canonical primitive types
//! (`prop`, `bool`, `nat`, `int`, `bytes`, `unit`) are cached behind
//! `LazyLock` so calls like `Type::bool()` are O(1) `Arc` bumps.
//!

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, LazyLock};

use smol_str::SmolStr;

use crate::term::{FreshId, FreshTyLeaf};

use super::list::TypeList;
use super::spec::TypeSpec;

// ============================================================================
// Type
// ============================================================================

#[derive(Clone)]
pub struct Type(Arc<TypeKind>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TypeKind {
    /// Type variable, e.g. `'a` in Isabelle notation.
    TFree(SmolStr),
    /// Type of `TermKind::Nat(_)` term values. Built in. The natural
    /// numbers (non-negative integers, arbitrary precision). The
    /// kernel's foundational data type (see `notes/vibes/type-hierarchy.md`).
    Nat,
    /// The HOL formula type — two inhabitants `T` and `F`. Built in
    /// as a first-class variant (not a named `Tycon`) so the HOL-
    /// Light kernel rules (`hol_refl`, `hol_eq_mp`, …) recognise
    /// formulas structurally — no name string-matching, no special
    /// `Tycon` carve-outs. Mirrors the same shape as `Prop`/`Nat`/
    /// `Int`/`Bytes`/`Unit`.
    Bool,
    /// Function type τ ⇒ σ.
    Fun(Type, Type),
    /// User-declared type constructor applied to arguments.
    /// **Structural identity** by name + args — cross-process stable.
    /// Best for "named uninterpreted" cases (HOL `num`, `list`, …).
    Tycon(SmolStr, TypeList),
    /// Type constructor whose identity is a kernel-allocated
    /// [`FreshId`] token (`Arc` pointer identity). **Process-local**
    /// — each `new_type_definition` call mints a distinct token, so
    /// two typedefs' subtypes can never be confused. Mirrors
    /// `TermKind::FreshConst` on the type side.
    ///
    /// Identity is the `FreshId` plus the args; the args participate
    /// in equality so that `τ α` and `τ β` are distinct even though
    /// they share the same constructor. The constructor is anonymous —
    /// no display label is stored. The payload is an opaque
    /// [`FreshTyLeaf`]: its private fields make the token↔args pairing
    /// structural, so a cloned token can never be re-paired with
    /// different args.
    FreshTyCon(FreshTyLeaf),
    /// Application of a derived-type [`TypeSpec`]
    /// factory to type arguments. The spec is process-shared
    /// (`LazyLock`-backed) and `args` is the positional
    /// substitution for the spec's type variables (in
    /// `spec.ty.free_tvars()` order — canonical alphabetical).
    ///
    /// Used by `crate::defs::*` to embed the semi-trusted derived-
    /// type catalogue (`set α`, `rel α β`, `option α`, …) into the
    /// kernel's type system without committing each one to its own
    /// `TypeKind` variant.
    Spec(TypeSpec, TypeList),
}

// Cached canonical instances of the common `Type`s, so the methods
// below are O(1) `Arc::clone` instead of a fresh allocation per call.
//
// `int` and `bytes` are NOT cached here directly — they are derived
// TypeSpecs (`crate::defs::int_ty_spec`, `crate::defs::bytes_spec`)
// wrapped in `Type::spec(…)`. The wrap itself is cached at the
// `Type::int()` / `Type::bytes()` call sites below.
static NAT: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Nat)));
static BOOL: LazyLock<Type> = LazyLock::new(|| Type(Arc::new(TypeKind::Bool)));

impl Type {
    pub fn kind(&self) -> &TypeKind {
        &self.0
    }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    pub(crate) fn alloc(kind: TypeKind) -> Self {
        Type(Arc::new(kind))
    }

    pub fn tfree(name: impl Into<SmolStr>) -> Self {
        Self::alloc(TypeKind::TFree(name.into()))
    }

    /// The byte-string type — `bytes := list u8`. Returns a shared
    /// instance; calls are O(1) `Arc` bumps. A derived TypeSpec
    /// (`crate::defs::bytes_spec`) wrapping a 0-ary
    /// `TypeKind::Spec(bytes_spec, [])` leaf. Literal terms of this
    /// type are constructed via [`crate::Term::blob`].
    pub fn bytes() -> Self {
        static LAZY: LazyLock<Type> =
            LazyLock::new(|| Type::spec(crate::defs::bytes_spec(), Vec::new()));
        LAZY.clone()
    }

    /// The native unbounded-naturals type — `nat`. Returns a
    /// shared instance; calls are O(1) `Arc` bumps. Literal terms
    /// of this type are constructed via [`crate::Term::nat_lit`].
    pub fn nat() -> Self {
        NAT.clone()
    }

    /// The integer type — `int := (nat × nat) / ~`, the Grothendieck
    /// construction (a pair `(a, b)` represents `a − b`). Returns a
    /// shared instance; calls are O(1) `Arc` bumps. A derived TypeSpec
    /// (`crate::defs::int_ty_spec`) wrapping a 0-ary
    /// `TypeKind::Spec(int_ty_spec, [])` leaf. Literal terms of this
    /// type are constructed via [`crate::Term::int_lit`].
    pub fn int() -> Self {
        static LAZY: LazyLock<Type> =
            LazyLock::new(|| Type::spec(crate::defs::int_ty_spec(), Vec::new()));
        LAZY.clone()
    }

    /// The singleton type — `unit := { b : bool | b = T }`. Has
    /// exactly one inhabitant. A derived TypeSpec
    /// (`crate::defs::unit_spec`) wrapping a 0-ary
    /// `TypeKind::Spec(unit_spec, [])` leaf (was the kernel-primitive
    /// `TypeKind::Unit` before the bool-subtype migration). The
    /// singleton fact is the kernel rule [`crate::Thm::unit_eq`].
    pub fn unit() -> Self {
        static LAZY: LazyLock<Type> =
            LazyLock::new(|| Type::spec(crate::defs::unit_spec(), Vec::new()));
        LAZY.clone()
    }

    /// The HOL formula type — `bool`. Returns a shared instance;
    /// calls are O(1) `Arc` bumps. First-class kernel variant
    /// (not a named `Tycon`) so the HOL-Light inference rules can
    /// recognise formulas structurally.
    pub fn bool() -> Self {
        BOOL.clone()
    }

    pub fn fun(dom: Type, cod: Type) -> Self {
        Self::alloc(TypeKind::Fun(dom, cod))
    }

    pub fn tycon(name: impl Into<SmolStr>, args: impl Into<TypeList>) -> Self {
        Self::alloc(TypeKind::Tycon(name.into(), args.into()))
    }

    /// Apply a derived-type [`TypeSpec`] to type
    /// arguments. The spec's type variables (in `ty.free_tvars()`
    /// order) are substituted positionally by `args`. The handle is
    /// process-shared (`LazyLock`-backed in `crate::defs`), so two
    /// `Type::spec(defs::set_spec(), …)` calls land at the same
    /// kind of leaf and pointer-equal at the spec component.
    pub fn spec(spec: TypeSpec, args: impl Into<TypeList>) -> Self {
        Self::alloc(TypeKind::Spec(spec, args.into()))
    }

    /// Construct a fresh-identity type constructor from a
    /// kernel-allocated [`FreshId`]. The token's Arc-pointer identity
    /// is the distinguishing identity — that's the freshness primitive
    /// [`crate::Thm::new_type_definition`] uses. Crate-private:
    /// identity is minted only inside the generative kernel rules.
    pub(crate) fn fresh_tycon(id: FreshId, args: impl Into<TypeList>) -> Self {
        Self::alloc(TypeKind::FreshTyCon(FreshTyLeaf::new(id, args.into())))
    }

    /// True when this is `Type::bool()` — the HOL formula type. The
    /// HOL-Light kernel rules ([`crate::Thm::refl`] et al.) accept
    /// `bool`-typed terms as theorems; we recognise them here
    /// structurally via the `TypeKind::Bool` variant.
    pub fn is_bool(&self) -> bool {
        matches!(self.kind(), TypeKind::Bool)
    }

    /// Free type variables of `self`, in sorted order with duplicates
    /// removed. Used by [`crate::Thm::new_type_definition`] to decide
    /// the arity of a freshly-introduced type constructor.
    pub fn free_tvars(&self) -> Vec<SmolStr> {
        let mut out = std::collections::BTreeSet::new();
        free_tvars_into(self, &mut out);
        out.into_iter().collect()
    }
}

pub(crate) fn free_tvars_into(ty: &Type, out: &mut std::collections::BTreeSet<SmolStr>) {
    match ty.kind() {
        TypeKind::TFree(name) => {
            out.insert(name.clone());
        }
        TypeKind::Nat | TypeKind::Bool => {}
        TypeKind::Fun(a, b) => {
            free_tvars_into(a, out);
            free_tvars_into(b, out);
        }
        TypeKind::Tycon(_, args) | TypeKind::Spec(_, args) => {
            for a in args {
                free_tvars_into(a, out);
            }
        }
        TypeKind::FreshTyCon(leaf) => {
            for a in leaf.args() {
                free_tvars_into(a, out);
            }
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}
impl Eq for Type {}
impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Type {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TypeKind::TFree(n) => write!(f, "'{}", n),
            TypeKind::Nat => write!(f, "nat"),
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Fun(a, b) => write!(f, "({} ⇒ {})", a, b),
            TypeKind::Tycon(name, args) => {
                if args.is_empty() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "({}", name)?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
            TypeKind::Spec(spec, args) => {
                if args.is_empty() {
                    write!(f, "{}", spec.symbol().label())
                } else {
                    write!(f, "({}", spec.symbol().label())?;
                    for a in args {
                        write!(f, " {}", a)?;
                    }
                    write!(f, ")")
                }
            }
            TypeKind::FreshTyCon(leaf) => {
                // Anonymous fresh-identity constructor: `tycon#ptr`,
                // disambiguated by the token's pointer identity.
                let (id, args) = (leaf.id(), leaf.args());
                let ptr = id.ptr_id();
                let label = format!("tycon#{ptr:x}");
                if args.is_empty() {
                    write!(f, "{label}")
                } else {
                    write!(f, "({label}")?;
                    for a in args {
                        write!(f, " {a}")?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}
