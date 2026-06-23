//! The term language: `Term`, `TermKind`, plus `Def` and the
//! type-checker (`TypeEnv` + `type_of_in`). The only logical
//! primitives are `=` (`TermKind::Eq`) and `ε` (`TermKind::Select`);
//! all other connectives live in `crate::defs::logic`.
//!
//! Locally-nameless: bound variables use de Bruijn indices, free
//! variables and constants carry their declared type. Meta-implication,
//! meta-universal, and meta-equality are first-class variants — not
//! built-in `Const` applications — so inference rules pattern-match
//! them directly.
//!
//! ## α-equivalence is structural equality
//!
//! Binders (`Abs`) are anonymous — bound variables are pure de Bruijn
//! indices with no display label — so structural equality on
//! `TermKind` is exactly α-equivalence; rules can use `==` freely.
//!
//! ## Observations
//!
//! `TermKind::Obs { observer: Object, ty: Type }` is the only leaf
//! that carries oracle-supplied data. The kernel never sees the
//! observer's concrete type. Construct an observation with
//! `Term::obs(o, ty)`. Two `Term::obs(o, ty)` calls — even with
//! identical `o` values — produce **distinct** leaves; clone the
//! constructed `Term` to share an observation across multiple call
//! sites.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, LazyLock};

use covalence_types::{Bytes, Int, Nat};
use smol_str::SmolStr;

use crate::ty::TypeSpec;

use super::spec::TermSpec;
use crate::error::{Error, Result};

use super::observer::{Object, Observer};
use crate::ty::{Type, TypeKind, TypeList};

// ============================================================================
// Def — fresh defined constants
// ============================================================================

/// A defined constant. Carries a display name (a `SmolStr`) and the
/// definition body behind an `Arc`. Each
/// [`crate::Thm::define`] call allocates a *fresh* `Arc`, so two
/// distinct definitions — even with the same name and the same body
/// — produce distinct `Def`s. Identity is `Arc::ptr_eq`; the name is
/// display-only (transparent to `Eq`/`Hash`/`Ord`).
///
/// This is how we get freshness without a stateful kernel signature:
/// the allocator gives us a unique pointer per call.
///
/// Two `Def`s are equal iff they share the same `original` identity
/// (same `Thm::define` call) AND are at the same instance type. This
/// mirrors Isabelle/Pure's signature-based naming (`Const(name,
/// instance_type)`) but uses Arc identity for the "which entry in the
/// signature" lookup, so no global signature is needed.
///
/// `subst_tfree_in_term` on a `Term::def` updates `instance_type`
/// without rebuilding `original` — preserving Arc identity across
/// type-variable instantiation. This is what makes a HOL constant
/// usable at multiple type instances while still comparing equal
/// to other uses at the same instance.
#[derive(Clone)]
pub struct Def {
    original: Arc<DefOriginal>,
    instance_type: Type,
}

#[derive(Debug)]
struct DefOriginal {
    name: SmolStr,
    body: Term,
    /// Cached `body.type_of()` — the most-general (polymorphic)
    /// type of this constant. `instance_type` always equals this
    /// for un-substituted `Def`s, and a one-way `match_types`
    /// against this recovers the substitution applied to the body
    /// when `body()` is called.
    body_type: Type,
}

impl Def {
    pub fn name(&self) -> &str {
        self.original.name.as_str()
    }

    /// The type at which this `Def` is currently used. For the
    /// `Def` returned by `Thm::define` this equals the body's
    /// type; `subst_tfree_in_term` updates this without recomputing
    /// the body.
    pub fn instance_type(&self) -> &Type {
        &self.instance_type
    }

    /// The body of this `Def` with type variables instantiated to
    /// match `instance_type`. For an un-substituted `Def` this is
    /// just the original body; otherwise we recover the substitution
    /// by one-way matching the original body type against
    /// `instance_type`, then apply it to the body.
    pub fn body(&self) -> Term {
        if self.instance_type == self.original.body_type {
            return self.original.body.clone();
        }
        let mut sub: std::collections::BTreeMap<SmolStr, Type> = std::collections::BTreeMap::new();
        crate::subst::match_types(&self.original.body_type, &self.instance_type, &mut sub)
            .expect("Def: instance_type unreachable from body_type — kernel bug");
        // Simultaneous apply: a sequential fold could cascade a
        // matched substitution like `{a:=b, b:=c}` into `a → c`.
        crate::subst::subst_tfrees_in_term(&self.original.body, &sub)
    }

    /// Identity of the original definition (stable across
    /// substitutions). Useful as a cache key.
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.original) as usize
    }

    pub(crate) fn new_internal(name: SmolStr, body: Term, body_type: Type) -> Self {
        let original = Arc::new(DefOriginal {
            name,
            body,
            body_type: body_type.clone(),
        });
        Def {
            original,
            instance_type: body_type,
        }
    }

    /// Build a `Def` reusing this one's `original` identity but at a
    /// different instance type. Crate-private: used by
    /// `subst_tfree_in_term`.
    pub(crate) fn with_instance_type(&self, instance_type: Type) -> Self {
        Def {
            original: self.original.clone(),
            instance_type,
        }
    }
}

impl PartialEq for Def {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.original, &other.original) && self.instance_type == other.instance_type
    }
}
impl Eq for Def {}

impl Hash for Def {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (Arc::as_ptr(&self.original) as usize).hash(state);
        self.instance_type.hash(state);
    }
}

impl Ord for Def {
    fn cmp(&self, other: &Self) -> Ordering {
        (Arc::as_ptr(&self.original) as usize)
            .cmp(&(Arc::as_ptr(&other.original) as usize))
            .then_with(|| self.instance_type.cmp(&other.instance_type))
    }
}
impl PartialOrd for Def {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Def({})", self.original.name)
    }
}

impl fmt::Display for Def {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.original.name)
    }
}

// ============================================================================
// Logical primitives — `=` and `ε`
// ============================================================================
//
// `=` ([`TermKind::Eq`]) and `ε` ([`TermKind::Select`]) are the kernel's
// only logical primitives. Every other connective / quantifier
// (`∧ ∨ ¬ ⟹ ⟺ ∀ ∃`) is an ordinary defined constant in
// [`crate::defs::logic`], unfolded by `Thm::unfold_term_spec` and
// reduced on `bool` literals by `Thm::reduce_prim`. `T` / `F` are the
// `TermKind::Bool` literals. Each primitive carries its *element* type
// α: `Eq(α) : α → α → bool` and `Select(α) : (α → bool) → α`.

// ============================================================================
// Term
// ============================================================================

/// Cached typing/closedness summary of a term node, computed once at
/// construction (`Term::alloc`) from the children's summaries. Private and
/// encapsulated so the encoding can be optimised later (bit-packing, a
/// free-variable Bloom filter, …) without touching call sites.
///
/// - `Open(k)`: the node has free de Bruijn indices, the largest being `k`
///   (so it needs `k + 1` enclosing binders). Its type is context-
///   dependent, so none is cached.
/// - `Wf(ty)`: the node is closed and well-typed; `ty` is its (context-
///   free) type.
/// - `IllTyped`: the node is closed but does not type-check.
///
/// Invariant: `Wf`/`IllTyped` ⟹ closed (no free de Bruijn index);
/// `Open(_)` ⟹ not closed. A node's type is cached only when closed,
/// which (given free variables carry their type — see [`Var`]) makes it
/// context-free and therefore safe to reuse anywhere.
/// Every variant additionally carries a [`Bloom`] over the **names** of the
/// free variables occurring in the node (the union of the children's). It
/// costs nothing in space: the variant tag is a `u8` and the largest
/// payload (`Wf`'s `Type` pointer) is 8-byte-aligned, so the `u32` lives in
/// padding that would otherwise be wasted. No false negatives, so
/// substitution / closing / occurrence checks skip whole subtrees that
/// provably lack a name without recursing.
#[derive(Debug)]
enum TermInfo {
    Open { bvi: u32, free: Bloom },
    Wf { free: Bloom, ty: Type },
    IllTyped { free: Bloom },
}

impl TermInfo {
    /// The free-variable Bloom filter, common to every variant.
    fn free(&self) -> Bloom {
        match self {
            TermInfo::Open { free, .. }
            | TermInfo::Wf { free, .. }
            | TermInfo::IllTyped { free } => *free,
        }
    }
}

struct TermInner {
    info: TermInfo,
    kind: TermKind,
}

/// A 32-bucket Bloom filter over free-variable **names** (single FNV hash,
/// `k = 1`). Hashing by name only — same-name-different-type collisions are
/// harmless (an extra exact check, never a correctness issue). The only
/// guarantee, and all that callers rely on: **no false negatives** — if
/// `!contains(n)`, the name `n` is definitely absent.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Bloom(u32);

impl Bloom {
    /// The empty filter.
    pub(crate) const fn empty() -> Bloom {
        Bloom(0)
    }

    /// The filter containing exactly the variable name `name`.
    pub(crate) fn singleton(name: &str) -> Bloom {
        use std::hash::Hasher;
        let mut h = fnv::FnvHasher::default();
        h.write(name.as_bytes());
        Bloom(1u32 << (h.finish() & 31))
    }

    /// May the name `name` be present? `false` is exact (no false
    /// negatives); `true` means "maybe — do the exact check".
    pub(crate) fn contains(&self, name: &str) -> bool {
        self.0 & Bloom::singleton(name).0 != 0
    }

    /// The union of two filters (the names of either).
    pub(crate) fn union(&self, rhs: &Bloom) -> Bloom {
        Bloom(self.0 | rhs.0)
    }
}

/// The free-variable Bloom filter for a node, from its children's filters.
fn compute_free(kind: &TermKind) -> Bloom {
    match kind {
        TermKind::Free(v) => Bloom::singleton(v.name()),
        TermKind::App(f, x) => f.0.info.free().union(&x.0.info.free()),
        TermKind::Abs(_, body) => body.0.info.free(),
        // No (substitutable) free term variables: `Def` is opaque to
        // `subst_free` (treated as a leaf), and the rest carry none.
        _ => Bloom::empty(),
    }
}

/// A HOL term: an `Arc`-shared node carrying its [`TermKind`] plus a cached
/// [`TermInfo`] (type + closedness) computed once at construction. As a
/// result [`Term::ty`] / [`Term::type_of`] and `Thm` well-formedness
/// checks are O(1) for closed terms (the common case), instead of an
/// O(size) re-walk per query.
#[derive(Clone)]
pub struct Term(Arc<TermInner>);

/// Why a closed-or-open term has no usable cached type — the error of
/// [`Term::ty`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyError {
    /// The term is not closed: it has a free de Bruijn index, so its type
    /// is context-dependent. See [`Term::bvi`].
    Open,
    /// The term is closed but does not type-check.
    IllTyped,
}

/// Width-and-signedness tag of a [`SmallIntLiteral`] — the fixed-width
/// integer types of the WebAssembly component model (`u8`…`u64`,
/// `s8`…`s64`). Each maps to a kernel type via [`IntTag::ty`].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntTag {
    U8,
    U16,
    U32,
    U64,
    S8,
    S16,
    S32,
    S64,
}

impl IntTag {
    /// The kernel type of a literal carrying this tag (`u8 := { v :
    /// bits | bits.len v = 8 }`, `s8 := u8`, …).
    pub fn ty(self) -> Type {
        match self {
            IntTag::U8 => crate::defs::u8_ty(),
            IntTag::U16 => crate::defs::u16_ty(),
            IntTag::U32 => crate::defs::u32_ty(),
            IntTag::U64 => crate::defs::u64_ty(),
            IntTag::S8 => crate::defs::s8_ty(),
            IntTag::S16 => crate::defs::s16_ty(),
            IntTag::S32 => crate::defs::s32_ty(),
            IntTag::S64 => crate::defs::s64_ty(),
        }
    }

    /// Display / serialisation label (`"u8"`, `"s64"`, …). Stable
    /// across processes — used by content hashing and S-expressions.
    pub fn label(self) -> &'static str {
        match self {
            IntTag::U8 => "u8",
            IntTag::U16 => "u16",
            IntTag::U32 => "u32",
            IntTag::U64 => "u64",
            IntTag::S8 => "s8",
            IntTag::S16 => "s16",
            IntTag::S32 => "s32",
            IntTag::S64 => "s64",
        }
    }

    /// Parse a tag from its [`IntTag::label`].
    pub fn from_label(s: &str) -> Option<Self> {
        Some(match s {
            "u8" => IntTag::U8,
            "u16" => IntTag::U16,
            "u32" => IntTag::U32,
            "u64" => IntTag::U64,
            "s8" => IntTag::S8,
            "s16" => IntTag::S16,
            "s32" => IntTag::S32,
            "s64" => IntTag::S64,
            _ => return None,
        })
    }

    /// `true` for the signed tags (`s8`…`s64`).
    pub fn is_signed(self) -> bool {
        matches!(self, IntTag::S8 | IntTag::S16 | IntTag::S32 | IntTag::S64)
    }

    /// The bit width of this type (`8`, `16`, `32`, or `64`).
    pub fn width(self) -> u32 {
        match self {
            IntTag::U8 | IntTag::S8 => 8,
            IntTag::U16 | IntTag::S16 => 16,
            IntTag::U32 | IntTag::S32 => 32,
            IntTag::U64 | IntTag::S64 => 64,
        }
    }

    /// Every tag, unsigned widths then signed widths. Used to
    /// enumerate the fixed-width integer catalogue.
    pub const ALL: [IntTag; 8] = [
        IntTag::U8,
        IntTag::U16,
        IntTag::U32,
        IntTag::U64,
        IntTag::S8,
        IntTag::S16,
        IntTag::S32,
        IntTag::S64,
    ];
}

/// A fixed-width integer literal: a type tag plus the raw value held
/// in a `u64`. Unsigned values are zero-extended, signed values
/// sign-extended into the 64 bits, so `bits` round-trips with `tag`.
/// Build one with [`SmallIntLiteral::u8`] … [`SmallIntLiteral::s64`].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SmallIntLiteral {
    pub tag: IntTag,
    pub bits: u64,
}

impl SmallIntLiteral {
    /// Raw constructor from a tag and an already-extended `u64`.
    pub fn new(tag: IntTag, bits: u64) -> Self {
        Self { tag, bits }
    }

    /// The kernel type of this literal (`self.tag.ty()`).
    pub fn ty(self) -> Type {
        self.tag.ty()
    }

    pub fn u8(v: u8) -> Self {
        Self::new(IntTag::U8, v as u64)
    }
    pub fn u16(v: u16) -> Self {
        Self::new(IntTag::U16, v as u64)
    }
    pub fn u32(v: u32) -> Self {
        Self::new(IntTag::U32, v as u64)
    }
    pub fn u64(v: u64) -> Self {
        Self::new(IntTag::U64, v)
    }
    pub fn s8(v: i8) -> Self {
        Self::new(IntTag::S8, v as u64)
    }
    pub fn s16(v: i16) -> Self {
        Self::new(IntTag::S16, v as u64)
    }
    pub fn s32(v: i32) -> Self {
        Self::new(IntTag::S32, v as u64)
    }
    pub fn s64(v: i64) -> Self {
        Self::new(IntTag::S64, v as u64)
    }
}

impl fmt::Display for SmallIntLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.tag.is_signed() {
            write!(f, "{}{}", self.bits as i64, self.tag.label())
        } else {
            write!(f, "{}{}", self.bits, self.tag.label())
        }
    }
}

/// A **free variable**: a name paired with its type. The type is part of
/// the variable's *identity* (HOL Light's `Var(name, ty)` model), so
/// `Var("x", nat)` and `Var("x", bool)` are **distinct** variables.
/// Equality / ordering / hashing therefore consider both fields, and
/// substitution (`subst_free`) only matches a variable with the same name
/// *and* type.
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var {
    name: SmolStr,
    ty: Type,
}

impl Var {
    /// A free variable named `name` of type `ty`.
    pub fn new(name: impl Into<SmolStr>, ty: Type) -> Self {
        Var {
            name: name.into(),
            ty,
        }
    }

    /// The variable's name.
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    /// The variable's type — part of its identity.
    pub fn ty(&self) -> &Type {
        &self.ty
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl From<Var> for Term {
    fn from(v: Var) -> Self {
        Term::free_var(v)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermKind {
    /// de Bruijn–indexed bound variable. Index 0 refers to the
    /// innermost surrounding binder (`Abs` or `All`).
    Bound(u32),
    /// Free variable: a [`Var`] (name + type, type-carrying identity).
    Free(Var),
    /// Declared/defined constant: name + instance type.
    Const(SmolStr, Type),
    /// Application `f x`.
    App(Term, Term),
    /// Abstraction `λ:ty. body`. `body` uses `Bound(0)` for the binder.
    /// Binders are anonymous — bound variables are pure de Bruijn
    /// indices (printed `#i`), with no display label in the kernel.
    Abs(Type, Term),
    /// Builtin: opaque byte literal of kernel type `bytes`.
    Blob(Bytes),
    /// Builtin: natural-number literal. Kernel type `nat`. See
    /// [`crate::Thm::reduce_prim`] for the single-step computation
    /// rule that decides closed-form arithmetic by reflexivity.
    Nat(Nat),
    /// Builtin: integer literal. Kernel type `int`.
    Int(Int),
    /// Builtin: fixed-width integer literal (`u8`…`u64`, `s8`…`s64`) —
    /// the WebAssembly component model's small integers. Carries a
    /// [`SmallIntLiteral`] (type tag + raw `u64` value); the kernel
    /// type is `lit.ty()`. Closed `=` over two of these decides by
    /// `Thm::reduce_prim` (structural literal equality).
    SmallInt(SmallIntLiteral),
    /// Builtin: HOL `bool` literal (`T` / `F`). Kernel type
    /// `TypeKind::Bool`. First-class kernel atom — not a separate
    /// observer system.
    Bool(bool),
    /// HOL `=` at element type α (full type `α → α → bool`). One of
    /// the two logical primitives. Applications are formed by the
    /// usual `App` chain.
    Eq(Type),
    /// HOL `ε` (Hilbert's choice) at element type α (full type
    /// `(α → bool) → α`). The other logical primitive. Its
    /// characterising axiom (choice) is not yet exposed as a rule.
    Select(Type),
    /// The `nat` successor function `succ : nat → nat`. A primitive
    /// constructor (not a `defs` definition): `nat` is the kernel's
    /// freely-generated naturals (`0` literals + `succ`), so the kernel
    /// commits to `succ` being injective and
    /// `0 ≠ succ n` — exposed as the freeness rules
    /// [`crate::Thm::succ_inj`] / [`crate::Thm::zero_ne_succ`], and to
    /// `succ (n : literal)` reducing to the next literal
    /// ([`crate::Thm::reduce_prim`]). Applied via the usual `App` chain.
    Succ,
    /// Application of a derived-term [`TermSpec`]
    /// factory to type arguments. The spec is process-shared
    /// (`LazyLock`-backed) and `args` is the positional substitution
    /// for the spec's type variables.
    ///
    /// Used by `crate::defs::*` to embed semi-trusted term constants
    /// (`natAdd`, `listMap`, …) as catalogue entries instead of
    /// dedicated kernel variants. `Thm::reduce_prim` recognises a
    /// `Spec(h, args)` leaf by `h.ptr_eq(&catalogue_handle)`.
    Spec(TermSpec, TypeList),
    /// Abstraction coercion `abs : carrier → (spec args)` for a
    /// derived [`TypeSpec`]. The `carrier` is the spec's
    /// `ty()` with `args` substituted positionally for its type
    /// variables (`spec.ty().free_tvars()` order — canonical
    /// alphabetical), and `(spec args)` is the opaque
    /// [`TypeKind::Spec`] wrapper.
    ///
    /// This is HOL Light's typedef `abs`, but keyed by the
    /// process-shared spec handle rather than a fresh `Obs` marker —
    /// so every catalogue type gets its abstraction "for free"
    /// (`inl`/`some`/`ok`/`pair`/… are built from it). It carries **no
    /// theorems**: the bijection equations (`rep (abs x) = x` when the
    /// carrier value satisfies the predicate, `abs (rep y) = y`
    /// always) are derived downstream in `covalence-hol`. Adding the
    /// leaf alone is sound — it is just a typed constant the kernel
    /// commits nothing about. (Soundness audit: every shipped
    /// `TypeSpec` is inhabited, so its `abs` lands in a non-empty
    /// type.)
    SpecAbs(TypeSpec, TypeList),
    /// Representation coercion `rep : (spec args) → carrier` — the
    /// inverse direction of [`TermKind::SpecAbs`]. Used by the
    /// eliminators (`coprodCase`/`fst`/`snd`/`option_case`/…) to reach
    /// a wrapper value's underlying carrier representation.
    SpecRep(TypeSpec, TypeList),
    /// Typed observation leaf: observer + Core type. The kernel
    /// compares these by `Arc` pointer identity (via [`Object`]'s
    /// impls), never by the user's `Eq` on the underlying observer.
    Obs(Object, Type),
    /// A defined constant. Each [`crate::Thm::define`] call produces
    /// a fresh `Def` (a fresh `Arc<Term>` allocation); the
    /// unfolding equation `Def ≡ body` is emitted by the same rule
    /// application. Two distinct `define` calls — even with the
    /// same name and same body — yield distinct `Def`s.
    Def(Def),
}

impl Term {
    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }

    fn info(&self) -> &TermInfo {
        &self.0.info
    }

    /// The term's type, in O(1) from the cached summary. Returns
    /// [`TyError::Open`] if the term is not closed (its type is
    /// context-dependent) or [`TyError::IllTyped`] if it is closed but
    /// does not type-check. Borrows the cached type — no clone, no walk.
    pub fn ty(&self) -> std::result::Result<&Type, TyError> {
        match self.info() {
            TermInfo::Wf { ty, .. } => Ok(ty),
            TermInfo::Open { .. } => Err(TyError::Open),
            TermInfo::IllTyped { .. } => Err(TyError::IllTyped),
        }
    }

    /// The largest free de Bruijn index in the term ("bound-variable
    /// index"), or `-1` if the term is closed. `bvi() < 0` iff the term is
    /// closed; `bvi() == k ≥ 0` means it needs `k + 1` enclosing binders.
    pub fn bvi(&self) -> i64 {
        match self.info() {
            TermInfo::Open { bvi, .. } => *bvi as i64,
            TermInfo::Wf { .. } | TermInfo::IllTyped { .. } => -1,
        }
    }

    /// `true` iff the term is closed (no free de Bruijn index).
    pub fn is_closed(&self) -> bool {
        !matches!(self.info(), TermInfo::Open { .. })
    }

    /// The free-variable [`Bloom`] filter over this term's free-variable
    /// names. Used by `subst`/`close`/occurrence checks to skip subtrees
    /// that provably lack a given name: `!t.free_bloom().contains(n)` ⇒ no
    /// free variable named `n` occurs in `t`.
    pub(crate) fn free_bloom(&self) -> Bloom {
        self.info().free()
    }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    // ---- structural accessors ----
    //
    // Borrowing matchers over the common `TermKind` shapes. Downstream
    // (untrusted) code should prefer these to matching `TermKind`
    // directly, so the kernel can evolve the representation without
    // breaking every walker. They return borrows; clone at the call
    // site if you need owned terms.

    /// If this is an application `f x`, return `(f, x)`.
    pub fn as_app(&self) -> Option<(&Term, &Term)> {
        match self.kind() {
            TermKind::App(f, x) => Some((f, x)),
            _ => None,
        }
    }

    /// If this is an abstraction `λ:ty. body`, return `(ty, body)`.
    /// `body` still uses `Bound(0)` for the binder.
    pub fn as_abs(&self) -> Option<(&Type, &Term)> {
        match self.kind() {
            TermKind::Abs(ty, body) => Some((ty, body)),
            _ => None,
        }
    }

    /// If this is a HOL equation `lhs = rhs` — i.e. the primitive `=`
    /// applied to two arguments, `App(App(Eq(_), lhs), rhs)` — return
    /// `(lhs, rhs)`. Note this matches `=` at *any* element type,
    /// including `bool` (where it is the biconditional).
    pub fn as_eq(&self) -> Option<(&Term, &Term)> {
        let (f, rhs) = self.as_app()?;
        let (head, lhs) = f.as_app()?;
        matches!(head.kind(), TermKind::Eq(_)).then_some((lhs, rhs))
    }

    /// If this is a derived-term spec application `Spec(handle, args)`,
    /// return `(handle, args)`.
    pub fn as_spec(&self) -> Option<(&TermSpec, &TypeList)> {
        match self.kind() {
            TermKind::Spec(s, args) => Some((s, args)),
            _ => None,
        }
    }

    /// If this is a HOL `bool` literal (`T` / `F`), return its value.
    pub fn as_bool(&self) -> Option<bool> {
        match self.kind() {
            TermKind::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Allocate a fresh `Arc` for `kind` (no interning). This is the
    /// canonical no-op [`crate::term::TrustedCons`] (`<()>::cons`); the
    /// smart constructors below all bottom out here. Crate-internal so the
    /// `cons` module can use it as the trusted baseline.
    pub(crate) fn alloc(kind: TermKind) -> Self {
        let info = term_info(&kind);
        Term(Arc::new(TermInner { info, kind }))
    }

    /// Rebuild this term bottom-up through `cons`, returning a
    /// structurally-equal term. With `&mut ()` this is a deep structural
    /// copy (sharing untouched leaves); with a [`crate::term::HashCons`]
    /// it **interns** the whole tree, so equal subterms — within this
    /// term and across every other term routed through the same interner —
    /// come back `Arc`-shared.
    ///
    /// Only `App`/`Abs` interior nodes are rebuilt from interned children;
    /// every leaf is consed from a clone of its kind. `Def` is treated as
    /// an opaque leaf — its body is not interned.
    pub fn cons_with<C: crate::term::TrustedCons + ?Sized>(&self, cons: &mut C) -> Term {
        // The no-op `()` interns nothing, so a rebuild would just deep-copy an
        // already-equal term — short-circuit to an identity (one `Arc` bump).
        if cons.allow_clone() {
            return self.clone();
        }
        let kind = match self.kind() {
            TermKind::App(f, x) => TermKind::App(f.cons_with(cons), x.cons_with(cons)),
            TermKind::Abs(ty, body) => TermKind::Abs(ty.clone(), body.cons_with(cons)),
            other => other.clone(),
        };
        cons.make(kind)
    }

    // ---- smart constructors ----
    pub fn bound(idx: u32) -> Self {
        Self::alloc(TermKind::Bound(idx))
    }
    pub fn free(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Free(Var::new(name, ty)))
    }
    /// A free-variable leaf from an existing [`Var`].
    pub fn free_var(v: Var) -> Self {
        Self::alloc(TermKind::Free(v))
    }
    /// If this is a free variable, return its [`Var`].
    pub fn as_free(&self) -> Option<&Var> {
        match self.kind() {
            TermKind::Free(v) => Some(v),
            _ => None,
        }
    }
    pub fn const_(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Const(name.into(), ty))
    }
    pub fn app(fun: Term, arg: Term) -> Self {
        Self::alloc(TermKind::App(fun, arg))
    }
    /// `λ:ty. body` — anonymous abstraction. `body` must already use
    /// `Bound(0)` for the binder (see [`crate::subst::close`]).
    pub fn abs(ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::Abs(ty, body))
    }
    pub fn blob(bytes: impl Into<Bytes>) -> Self {
        Self::alloc(TermKind::Blob(bytes.into()))
    }

    // ---- builtin value constructors ----
    /// `nat` literal.
    pub fn nat_lit(n: impl Into<Nat>) -> Self {
        Self::alloc(TermKind::Nat(n.into()))
    }
    /// `int` literal.
    pub fn int_lit(n: impl Into<Int>) -> Self {
        Self::alloc(TermKind::Int(n.into()))
    }

    /// Fixed-width integer literal from an already-built
    /// [`SmallIntLiteral`].
    pub fn small_int(lit: SmallIntLiteral) -> Self {
        Self::alloc(TermKind::SmallInt(lit))
    }
    /// `u8` literal (kernel type `u8`).
    pub fn u8_lit(v: u8) -> Self {
        Self::small_int(SmallIntLiteral::u8(v))
    }
    /// `u16` literal (kernel type `u16`).
    pub fn u16_lit(v: u16) -> Self {
        Self::small_int(SmallIntLiteral::u16(v))
    }
    /// `u32` literal (kernel type `u32`).
    pub fn u32_lit(v: u32) -> Self {
        Self::small_int(SmallIntLiteral::u32(v))
    }
    /// `u64` literal (kernel type `u64`).
    pub fn u64_lit(v: u64) -> Self {
        Self::small_int(SmallIntLiteral::u64(v))
    }
    /// `s8` literal (kernel type `s8`).
    pub fn s8_lit(v: i8) -> Self {
        Self::small_int(SmallIntLiteral::s8(v))
    }
    /// `s16` literal (kernel type `s16`).
    pub fn s16_lit(v: i16) -> Self {
        Self::small_int(SmallIntLiteral::s16(v))
    }
    /// `s32` literal (kernel type `s32`).
    pub fn s32_lit(v: i32) -> Self {
        Self::small_int(SmallIntLiteral::s32(v))
    }
    /// `s64` literal (kernel type `s64`).
    pub fn s64_lit(v: i64) -> Self {
        Self::small_int(SmallIntLiteral::s64(v))
    }

    /// HOL `bool` literal — `Bool(true)` is `T`, `Bool(false)` is
    /// `F`. Kernel type `bool`.
    pub fn bool_lit(b: bool) -> Self {
        static TRUE: LazyLock<Term> = LazyLock::new(|| Term::alloc(TermKind::Bool(true)));
        static FALSE: LazyLock<Term> = LazyLock::new(|| Term::alloc(TermKind::Bool(false)));
        if b { TRUE.clone() } else { FALSE.clone() }
    }

    /// HOL `=` at element type `alpha` (full type `α → α → bool`).
    pub fn eq_op(alpha: Type) -> Self {
        Self::alloc(TermKind::Eq(alpha))
    }

    /// HOL `ε` (Hilbert choice) at element type `alpha` (full type
    /// `(α → bool) → α`).
    pub fn select_op(alpha: Type) -> Self {
        Self::alloc(TermKind::Select(alpha))
    }

    /// The primitive successor function `succ : nat → nat`. Apply via
    /// [`Term::app`]; see [`TermKind::Succ`].
    pub fn succ() -> Self {
        static SUCC: LazyLock<Term> = LazyLock::new(|| Term::alloc(TermKind::Succ));
        SUCC.clone()
    }

    /// Apply a derived-term [`TermSpec`] to type
    /// arguments. The spec is process-shared (`LazyLock`-backed in
    /// `crate::defs`); two calls with handles from the same lazy
    /// static pointer-equal at the spec component.
    pub fn term_spec(spec: TermSpec, args: impl Into<TypeList>) -> Self {
        Self::alloc(TermKind::Spec(spec, args.into()))
    }

    /// The abstraction coercion `abs : carrier → (spec args)` for a
    /// derived [`TypeSpec`] (see [`TermKind::SpecAbs`]).
    /// `args` instantiates the spec's type variables positionally.
    pub fn spec_abs(spec: TypeSpec, args: impl Into<TypeList>) -> Self {
        Self::alloc(TermKind::SpecAbs(spec, args.into()))
    }

    /// The representation coercion `rep : (spec args) → carrier` for a
    /// derived [`TypeSpec`] (see [`TermKind::SpecRep`]).
    pub fn spec_rep(spec: TypeSpec, args: impl Into<TypeList>) -> Self {
        Self::alloc(TermKind::SpecRep(spec, args.into()))
    }

    /// Wrap an observer as a typed leaf. The kernel treats the
    /// underlying value opaquely; only the user code constructing
    /// `o` controls what observations exist.
    pub fn obs<O: Observer>(o: O, ty: Type) -> Self {
        Self::alloc(TermKind::Obs(Object::new(o), ty))
    }

    /// Like [`Term::obs`] but reuses an existing [`Object`] handle
    /// (preserving its `Arc` identity). Used by deserialisers and
    /// other shells that have already constructed a `Object`.
    pub fn obs_from_dyn(observer: Object, ty: Type) -> Self {
        Self::alloc(TermKind::Obs(observer, ty))
    }

    /// Wrap an existing [`Def`] as a `Term` leaf. Sharing the same
    /// `Def` via `clone` preserves kernel identity; constructing two
    /// distinct `Def`s with the same name produces two distinct
    /// `Term`s here.
    pub fn def(d: Def) -> Self {
        Self::alloc(TermKind::Def(d))
    }

    /// Compute the type of `self` in an empty env. Walks the whole
    /// term, checking that every Free / Const occurrence uses a
    /// consistent type, every App is well-typed, every Imp / All body
    /// has type `prop`, every Eq has matching argument types, and no
    /// Bound variable escapes its binder.
    ///
    /// Each Thm-construction shares a single env across all hypotheses
    /// and the conclusion, so Thm validity is *stronger* than every
    /// individual term being well-typed: it also enforces that Free
    /// names are consistent *across* hyps and concl.
    pub fn type_of(&self) -> Result<Type> {
        // Fast path: a closed, well-typed term has its type cached.
        if let TermInfo::Wf { ty, .. } = self.info() {
            return Ok(ty.clone());
        }
        // Open / ill-typed: re-derive via the structural typer to produce
        // a *specific* error (NotClosed / NotFunction / TypeMismatch).
        let mut env = TypeEnv::default();
        type_of_in(self, &mut env)
    }

    /// Returns `true` iff no `Obs` leaf appears anywhere in this
    /// term (including transitively through any `Def` bodies). Used
    /// at theorem level via [`crate::Thm::has_no_obs`].
    pub fn has_no_obs(&self) -> bool {
        match self.kind() {
            TermKind::Obs(..) => false,
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_)
            | TermKind::Nat(_)
            | TermKind::Int(_)
            | TermKind::SmallInt(_)
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::SpecAbs(..)
            | TermKind::SpecRep(..)
            | TermKind::Eq(_)
            | TermKind::Select(_)
            | TermKind::Succ => true,
            TermKind::App(a, b) => a.has_no_obs() && b.has_no_obs(),
            TermKind::Abs(_, body) => body.has_no_obs(),
            TermKind::Def(d) => d.body().has_no_obs(),
        }
    }

    /// Returns `true` iff every `Obs` leaf carries an observer
    /// whose dynamic type is `O`. Trivially `true` for a term with
    /// no `Obs` leaves.
    pub fn all_obs_match<O: Observer>(&self) -> bool {
        match self.kind() {
            TermKind::Obs(observer, _) => observer.downcast::<O>().is_some(),
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_)
            | TermKind::Nat(_)
            | TermKind::Int(_)
            | TermKind::SmallInt(_)
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::SpecAbs(..)
            | TermKind::SpecRep(..)
            | TermKind::Eq(_)
            | TermKind::Select(_)
            | TermKind::Succ => true,
            TermKind::App(a, b) => a.all_obs_match::<O>() && b.all_obs_match::<O>(),
            TermKind::Abs(_, body) => body.all_obs_match::<O>(),
            TermKind::Def(d) => d.body().all_obs_match::<O>(),
        }
    }

    /// Walk the term and call `f` on every `Obs` leaf's observer
    /// downcast to `O`. Returns `Err(ObsDowncastTypeMismatch)` at
    /// the first leaf whose dynamic type does not match `O`.
    pub fn for_each_obs<O: Observer, F: FnMut(&O)>(&self, f: &mut F) -> Result<()> {
        match self.kind() {
            TermKind::Obs(observer, _) => {
                let o = observer
                    .downcast::<O>()
                    .ok_or(Error::ObsDowncastTypeMismatch)?;
                f(o);
                Ok(())
            }
            TermKind::Bound(_)
            | TermKind::Free(..)
            | TermKind::Const(..)
            | TermKind::Blob(_)
            | TermKind::Nat(_)
            | TermKind::Int(_)
            | TermKind::SmallInt(_)
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::SpecAbs(..)
            | TermKind::SpecRep(..)
            | TermKind::Eq(_)
            | TermKind::Select(_)
            | TermKind::Succ => Ok(()),
            TermKind::App(a, b) => {
                a.for_each_obs::<O, F>(f)?;
                b.for_each_obs::<O, F>(f)
            }
            TermKind::Abs(_, body) => body.for_each_obs::<O, F>(f),
            TermKind::Def(d) => d.body().for_each_obs::<O, F>(f),
        }
    }
}

// Equality / hashing / ordering are on the `kind` only: `info` is a pure
// function of `kind`, so equal kinds have equal info and comparing it
// would be redundant. The `Arc::ptr_eq` fast path stays.
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.kind == other.0.kind
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.kind.hash(state);
    }
}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            return Ordering::Equal;
        }
        self.0.kind.cmp(&other.0.kind)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Display a spec coercion leaf (`abs`/`rep`) as `kw[label]` (no
/// type args) or `(kw[label] arg …)` (with args).
fn fmt_coercion(f: &mut fmt::Formatter<'_>, kw: &str, label: &str, args: &[Type]) -> fmt::Result {
    if args.is_empty() {
        write!(f, "{kw}[{label}]")
    } else {
        write!(f, "({kw}[{label}]")?;
        for a in args {
            write!(f, " {a}")?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Bound(i) => write!(f, "#{}", i),
            TermKind::Free(v) => write!(f, "{}", v.name()),
            TermKind::Const(name, _) => write!(f, "{}", name),
            TermKind::App(g, x) => write!(f, "({} {})", g, x),
            TermKind::Abs(ty, body) => write!(f, "(λ:{}. {})", ty, body),
            TermKind::Blob(b) => write!(f, "blob[{}]", b.len()),
            TermKind::Nat(n) => write!(f, "{}n", n.as_inner()),
            TermKind::Int(n) => write!(f, "{}i", n.as_inner()),
            TermKind::SmallInt(lit) => write!(f, "{}", lit),
            TermKind::Bool(b) => write!(f, "{}", if *b { "T" } else { "F" }),
            TermKind::Eq(alpha) => write!(f, "=:{alpha}"),
            TermKind::Select(alpha) => write!(f, "@:{alpha}"),
            TermKind::Succ => write!(f, "succ"),
            TermKind::Spec(spec, args) => {
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
            TermKind::SpecAbs(spec, args) => fmt_coercion(f, "abs", spec.symbol().label(), args),
            TermKind::SpecRep(spec, args) => fmt_coercion(f, "rep", spec.symbol().label(), args),
            TermKind::Obs(observer, ty) => write!(f, "obs[{:?}:{}]", observer, ty),
            TermKind::Def(d) => write!(f, "{}", d),
        }
    }
}

// ============================================================================
// Type-of
// ============================================================================

/// Carries the binder context for a single `type_of` walk.
///
/// Free variables are identified by `(name, type)` (HOL Light's
/// `Var(name, ty)` model), so there is **no** cross-term name/type
/// consistency to track — `Free(name, ty)` simply has type `ty`. A
/// distinct same-named variable at another type is a different variable.
#[derive(Default)]
pub(crate) struct TypeEnv {
    /// Stack of binder types; the innermost binder is at the top.
    ctx: Vec<Type>,
}

/// The carrier type of a derived [`TypeSpec`] at the
/// given type `args`: the spec's stored `ty()` with each free tvar
/// (in `free_tvars()` canonical order) replaced positionally. This is
/// the same substitution `TypeKind::Spec` uses to denote the wrapper,
/// so `abs`/`rep` coerce between `carrier` and `(spec args)`
/// faithfully. Errors if the spec is carrier-less (`ty = None`).
fn spec_carrier(spec: &TypeSpec, args: &[Type]) -> Result<Type> {
    let result = spec.ty().cloned().ok_or(Error::SpecHasNoCarrier)?;
    Ok(crate::subst::subst_tfrees_in_type(
        &result,
        &positional_tvar_sub(&result, args),
    ))
}

/// Build the substitution mapping `ty`'s free type variables (in
/// `free_tvars()` canonical alphabetical order) to `args` positionally.
/// Used to instantiate a spec's stored type/carrier; the result feeds
/// [`crate::subst::subst_tfrees_in_type`] for a *simultaneous* apply.
fn positional_tvar_sub(ty: &Type, args: &[Type]) -> std::collections::BTreeMap<SmolStr, Type> {
    ty.free_tvars()
        .into_iter()
        .zip(args.iter().cloned())
        .collect()
}

/// Compute a node's cached [`TermInfo`] from its `kind`, reading the
/// children's already-cached summaries. O(1) for every shape except an
/// `Abs` that closes an `Open(0)` body — there the body is typed once
/// under the new binder via [`type_of_in`], which walks only the open
/// spine (closed subterms short-circuit on their cached `Wf`).
///
/// `Soundness:` this is the kernel's type checker, relocated to
/// construction time and made incremental. It must agree with
/// [`type_of_in`] (and indeed reuses it for the close case). A node is
/// `Wf(ty)` only when genuinely closed and well-typed; anything else is
/// `Open`/`IllTyped`, so no false type can be cached.
fn term_info(kind: &TermKind) -> TermInfo {
    use TermInfo::{IllTyped, Open, Wf};
    // The free-variable Bloom is the same for every node, regardless of its
    // type/openness; compute it once and stamp it into whichever variant we
    // return.
    let free = compute_free(kind);
    let wf = |ty: Type| Wf { free, ty };
    let open = |bvi: u32| Open { bvi, free };
    let ill = || IllTyped { free };
    // Wrap a possibly-failing closed-type computation into closed info.
    let closed = |r: Result<Type>| match r {
        Ok(ty) => Wf { free, ty },
        Err(_) => IllTyped { free },
    };
    match kind {
        TermKind::Bound(i) => open(*i),
        TermKind::Free(v) => wf(v.ty().clone()),
        TermKind::Const(_, ty) => wf(ty.clone()),
        TermKind::Blob(_) => wf(Type::bytes()),
        TermKind::Nat(_) => wf(Type::nat()),
        TermKind::Int(_) => wf(Type::int()),
        TermKind::SmallInt(lit) => wf(lit.ty()),
        TermKind::Bool(_) => wf(Type::bool()),
        TermKind::Eq(alpha) => wf(Type::fun(
            alpha.clone(),
            Type::fun(alpha.clone(), Type::bool()),
        )),
        TermKind::Select(alpha) => wf(Type::fun(
            Type::fun(alpha.clone(), Type::bool()),
            alpha.clone(),
        )),
        TermKind::Succ => wf(Type::fun(Type::nat(), Type::nat())),
        TermKind::Obs(_, ty) => wf(ty.clone()),
        TermKind::Def(d) => wf(d.instance_type().clone()),
        TermKind::Spec(spec, args) => closed(
            spec.ty()
                .cloned()
                .ok_or(Error::SpecHasNoCarrier)
                .map(|result| {
                    crate::subst::subst_tfrees_in_type(&result, &positional_tvar_sub(&result, args))
                }),
        ),
        TermKind::SpecAbs(spec, args) => closed((|| -> Result<Type> {
            Ok(Type::fun(
                spec_carrier(spec, args)?,
                Type::spec(spec.clone(), args.clone()),
            ))
        })()),
        TermKind::SpecRep(spec, args) => closed((|| -> Result<Type> {
            Ok(Type::fun(
                Type::spec(spec.clone(), args.clone()),
                spec_carrier(spec, args)?,
            ))
        })()),
        TermKind::App(f, x) => {
            let fo = match f.info() {
                Open { bvi, .. } => Some(*bvi),
                _ => None,
            };
            let xo = match x.info() {
                Open { bvi, .. } => Some(*bvi),
                _ => None,
            };
            match (fo, xo) {
                // Either side open ⇒ the application is open; defer typing.
                (Some(a), Some(b)) => open(a.max(b)),
                (Some(a), None) => open(a),
                (None, Some(b)) => open(b),
                // Both closed ⇒ type the application now.
                (None, None) => match (f.info(), x.info()) {
                    (Wf { ty: ft, .. }, Wf { ty: xt, .. }) => match ft.kind() {
                        TypeKind::Fun(dom, cod) if dom == xt => wf(cod.clone()),
                        _ => ill(),
                    },
                    // A closed child is `IllTyped`.
                    _ => ill(),
                },
            }
        }
        TermKind::Abs(ty, body) => match body.info() {
            Wf { ty: bt, .. } => wf(Type::fun(ty.clone(), bt.clone())),
            IllTyped { .. } => ill(),
            // Binding index 0 closes the term: type the body under the new
            // binder (walking only the open spine).
            Open { bvi: 0, .. } => {
                let mut env = TypeEnv {
                    ctx: vec![ty.clone()],
                };
                closed(type_of_in(body, &mut env).map(|bt| Type::fun(ty.clone(), bt)))
            }
            // Still open after binding one level.
            Open { bvi: m, .. } => open(m - 1),
        },
    }
}

/// Type-check `t` in `env`, where `env` carries the binder-type stack.
/// Used as the close-time typer by [`term_info`] and as the
/// specific-error fallback by [`Term::type_of`]. Closed subterms
/// short-circuit on their cached type, so this walks only the open spine.
pub(crate) fn type_of_in(t: &Term, env: &mut TypeEnv) -> Result<Type> {
    // A closed subterm's type is cached and context-independent — return it
    // without recursing. This is what makes a close-time typing (and any
    // `type_of`) walk only the *open* spine: closed subterms short-circuit.
    if let TermInfo::Wf { ty, .. } = t.info() {
        return Ok(ty.clone());
    }
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i as usize;
            if i >= env.ctx.len() {
                return Err(Error::NotClosed);
            }
            Ok(env.ctx[env.ctx.len() - 1 - i].clone())
        }
        // A free variable's type is part of its identity, so it simply
        // *is* its type — no cross-occurrence consistency to enforce.
        TermKind::Free(v) => Ok(v.ty().clone()),
        // Const instance types are NOT required to be consistent
        // across occurrences within a theorem — polymorphic constants
        // (`=` at `'a → 'a → bool`, etc.) are used at many instance
        // types in a single proof. The signature check that ties each
        // Const's instance type to a declared principal type lands
        // when `define` lands.
        TermKind::Const(_, ty) => Ok(ty.clone()),
        TermKind::App(fun, arg) => {
            let fun_ty = type_of_in(fun, env)?;
            let arg_ty = type_of_in(arg, env)?;
            let TypeKind::Fun(dom, cod) = fun_ty.kind() else {
                return Err(Error::NotFunction(fun_ty));
            };
            if *dom != arg_ty {
                return Err(Error::TypeMismatch {
                    expected: dom.clone(),
                    got: arg_ty,
                });
            }
            Ok(cod.clone())
        }
        TermKind::Abs(ty, body) => {
            env.ctx.push(ty.clone());
            let body_ty = type_of_in(body, env);
            env.ctx.pop();
            Ok(Type::fun(ty.clone(), body_ty?))
        }
        TermKind::Blob(_) => Ok(Type::bytes()),
        TermKind::Nat(_) => Ok(Type::nat()),
        TermKind::Int(_) => Ok(Type::int()),
        TermKind::SmallInt(lit) => Ok(lit.ty()),
        TermKind::Bool(_) => Ok(Type::bool()),
        // A `Spec` leaf's type is the spec's own `ty` field (the
        // factory's carrier) with positional type-arg substitution
        // applied. The spec is held by handle; deref is cheap.
        TermKind::Spec(spec, args) => {
            let result = spec
                .ty()
                .cloned()
                .ok_or_else(|| Error::NotBool(Type::bool()))?;
            // free_tvars on the carrier gives the spec's tvar names
            // in canonical alphabetical order. Substitute positionally
            // and *simultaneously* (a sequential fold would cascade,
            // e.g. instantiating `[a:=b, b:=c]` would turn `a` into `c`).
            Ok(crate::subst::subst_tfrees_in_type(
                &result,
                &positional_tvar_sub(&result, args),
            ))
        }
        // `abs` at `(spec, args)` has type `carrier → (spec args)`;
        // `rep` the reverse. `carrier` is the TypeSpec's stored
        // `ty()` with `args` substituted positionally for its tvars —
        // exactly the substitution `Type::spec`/`TypeKind::Spec` use,
        // so `abs`/`rep` round-trip the same wrapper type the leaf
        // denotes. A spec with no carrier (`ty = None`) has no
        // abstraction.
        TermKind::SpecAbs(spec, args) => {
            let carrier = spec_carrier(spec, args)?;
            let wrapper = Type::spec(spec.clone(), args.clone());
            Ok(Type::fun(carrier, wrapper))
        }
        TermKind::SpecRep(spec, args) => {
            let carrier = spec_carrier(spec, args)?;
            let wrapper = Type::spec(spec.clone(), args.clone());
            Ok(Type::fun(wrapper, carrier))
        }
        // `=` at α has type `α → α → bool`; `ε` at α has type
        // `(α → bool) → α`. Both are well-shaped by construction (the
        // stored type *is* α), so there is nothing to validate.
        TermKind::Eq(alpha) => Ok(Type::fun(
            alpha.clone(),
            Type::fun(alpha.clone(), Type::bool()),
        )),
        TermKind::Select(alpha) => Ok(Type::fun(
            Type::fun(alpha.clone(), Type::bool()),
            alpha.clone(),
        )),
        // `succ : nat → nat`, monomorphic.
        TermKind::Succ => Ok(Type::fun(Type::nat(), Type::nat())),
        TermKind::Obs(_, ty) => Ok(ty.clone()),
        // A `Def` denotes its body at the current instance type.
        // The body was validated once at `Thm::define` time, and
        // `subst_tfree_in_term` updates `instance_type` consistently
        // — so we can just read `instance_type` here without walking
        // through to the body. The body's Free-var tracking only
        // matters for the body itself; since this Term is just a
        // Def reference, there are no Free leaves to track at this
        // node.
        TermKind::Def(d) => Ok(d.instance_type().clone()),
    }
}

#[cfg(test)]
mod bloom_tests {
    use super::*;
    use crate::ty::Type;

    #[test]
    fn bloom_api() {
        assert!(!Bloom::empty().contains("x"));
        assert!(Bloom::singleton("x").contains("x"));
        let u = Bloom::singleton("x").union(&Bloom::singleton("y"));
        assert!(u.contains("x") && u.contains("y"));
    }

    #[test]
    fn free_bloom_no_false_negatives() {
        // Every free-var name present must be reported (no false negatives).
        let t = Term::app(Term::free("a", Type::nat()), Term::free("b", Type::bool()));
        assert!(t.free_bloom().contains("a"));
        assert!(t.free_bloom().contains("b"));
        // A closed term with no free vars: empty bloom, contains nothing.
        assert!(!Term::nat_lit(5u32).free_bloom().contains("a"));
        // An abstraction keeps its body's free vars (the binder is Bound 0,
        // not a free var).
        let lam = Term::abs(Type::nat(), Term::app(Term::free("a", Type::nat()), Term::bound(0)));
        assert!(lam.free_bloom().contains("a"));
    }
}
