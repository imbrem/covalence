//! The type language: `Type`, `TypeKind`, and `BinderHint`.
//!
//! Type identity is structural (`PartialEq` on `TypeKind`); the
//! constructors below return `Arc`-wrapped instances so identical
//! types share a single allocation. The canonical primitive types
//! (`prop`, `bool`, `nat`, `int`, `bytes`, `unit`) are cached behind
//! `LazyLock` so calls like `Type::bool()` are O(1) `Arc` bumps.
//!
//! `BinderHint` lives here too — it's the α-transparent display label
//! used by both `TypeKind::TyConObs` (type-side) and `TermKind::Abs`
//! / `TermKind::All` / `Def` (term-side). Putting it in `types` keeps
//! the dependency edge clean: `types` is loaded before `terms`.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, LazyLock};

use smol_str::SmolStr;

use crate::term::{Object, Observer};

use super::list::TypeList;
use super::spec::TypeSpec;

// ============================================================================
// BinderHint
// ============================================================================

/// A display label for an `Abs`/`All` binder, or for a `TyConObs`
/// constructor. Transparent to equality and ordering —
/// `BinderHint("x") == BinderHint("y")` is `true`. Only `Display` and
/// `Debug` distinguish them, so that α-equivalence is structural
/// equality on `TermKind` and structural equality on `TypeKind`.
#[derive(Clone, Default)]
pub struct BinderHint(pub SmolStr);

impl BinderHint {
    pub fn new(s: impl Into<SmolStr>) -> Self {
        BinderHint(s.into())
    }
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<S: Into<SmolStr>> From<S> for BinderHint {
    fn from(s: S) -> Self {
        BinderHint(s.into())
    }
}

impl PartialEq for BinderHint {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for BinderHint {}
impl Hash for BinderHint {
    fn hash<H: Hasher>(&self, _: &mut H) {}
}
impl Ord for BinderHint {
    fn cmp(&self, _: &Self) -> Ordering {
        Ordering::Equal
    }
}
impl PartialOrd for BinderHint {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for BinderHint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Display for BinderHint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

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
    /// kernel's foundational data type (see `docs/type-hierarchy.md`).
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
    /// Type constructor whose identity is the wrapped observer's `Arc`
    /// pointer. **Process-local** — two `Type::tycon_obs` calls with
    /// independently constructed observers compare unequal even if they
    /// share the same `BinderHint` and args. Mirrors `TermKind::Obs` on the
    /// type side: the same Rust observer type is the unifying ε-family
    /// across term- and type-level uses (one theory → one identity).
    ///
    /// The [`BinderHint`] is α-transparent (display only). Identity is the
    /// `Object` plus the args; the args participate in equality so
    /// that `list α` and `list β` are distinct even though they share
    /// the same constructor.
    TyConObs(Object, BinderHint, TypeList),
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

    fn alloc(kind: TypeKind) -> Self {
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

    /// Construct a fresh-identity type constructor wrapping an
    /// observer. The Arc-pointer identity of `observer` is the
    /// distinguishing identity; `hint` is display-only (α-transparent).
    /// Distinct calls with independently-constructed observers produce
    /// distinct types — that's the freshness primitive
    /// [`crate::Thm::new_type_definition`] uses.
    pub fn tycon_obs<O: Observer>(
        observer: O,
        hint: impl Into<BinderHint>,
        args: impl Into<TypeList>,
    ) -> Self {
        Self::alloc(TypeKind::TyConObs(
            Object::new(observer),
            hint.into(),
            args.into(),
        ))
    }

    /// Like [`Type::tycon_obs`] but reuses an existing [`Object`]
    /// handle (preserving its `Arc` identity). Used internally by
    /// kernel rules and by deserialisers that already have a `Object`.
    pub fn tycon_obs_from_dyn(
        observer: Object,
        hint: impl Into<BinderHint>,
        args: impl Into<TypeList>,
    ) -> Self {
        Self::alloc(TypeKind::TyConObs(observer, hint.into(), args.into()))
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
        TypeKind::Tycon(_, args) | TypeKind::TyConObs(_, _, args) | TypeKind::Spec(_, args) => {
            for a in args {
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
            TypeKind::TyConObs(observer, hint, args) => {
                // `<hint#ptr>` for the constructor head, then args.
                // `hint` is the user-visible label; the pointer suffix
                // disambiguates fresh allocations sharing a name.
                let ptr = observer.ptr_id();
                let label = if hint.is_empty() {
                    format!("tycon#{ptr:x}")
                } else {
                    format!("{hint}#{ptr:x}")
                };
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
