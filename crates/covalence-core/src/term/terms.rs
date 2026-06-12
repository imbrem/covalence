//! The term language: `Term`, `TermKind`, plus `Def`, `HolOp`, and
//! the type-checker (`TypeEnv` + `type_of_in`).
//!
//! Locally-nameless: bound variables use de Bruijn indices, free
//! variables and constants carry their declared type. Meta-implication,
//! meta-universal, and meta-equality are first-class variants — not
//! built-in `Const` applications — so inference rules pattern-match
//! them directly.
//!
//! ## α-equivalence is structural equality
//!
//! Each `Abs` and `All` carries a [`BinderHint`] — a display label for
//! the binder. The `BinderHint` type is *transparent* to `PartialEq`,
//! `Hash`, and `Ord`: two `BinderHint`s always compare equal and hash
//! the same. So structural equality on `TermKind` is α-equivalence;
//! rules can use `==` freely without worrying about display labels.
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
use std::collections::BTreeMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use bytes::Bytes;
use covalence_types::{Int, Nat};
use smol_str::SmolStr;

use crate::error::{Error, Result};

use super::observers::{Object, Observer};
use super::types::{BinderHint, Type, TypeKind};

// ============================================================================
// Def — fresh defined constants
// ============================================================================

/// A defined constant. Carries a display [`BinderHint`] (the name, for
/// pretty-printing) and the definition body behind an `Arc`. Each
/// [`crate::Thm::define`] call allocates a *fresh* `Arc`, so two
/// distinct definitions — even with the same name and the same body
/// — produce distinct `Def`s. Identity is `Arc::ptr_eq`; the name is
/// display-only (transparent to `Eq`/`Hash`/`Ord`, like [`BinderHint`]).
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
    name: BinderHint,
    body: Term,
    /// Cached `body.type_of()` — the most-general (polymorphic)
    /// type of this constant. `instance_type` always equals this
    /// for un-substituted `Def`s, and a one-way `match_types`
    /// against this recovers the substitution applied to the body
    /// when `body()` is called.
    body_type: Type,
}

impl Def {
    pub fn name(&self) -> &BinderHint {
        &self.original.name
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
        let mut sub: std::collections::BTreeMap<SmolStr, Type> =
            std::collections::BTreeMap::new();
        crate::subst::match_types(&self.original.body_type, &self.instance_type, &mut sub)
            .expect("Def: instance_type unreachable from body_type — kernel bug");
        let mut result = self.original.body.clone();
        for (tv, replacement) in sub {
            result = crate::subst::subst_tfree_in_term(&result, tv.as_str(), &replacement);
        }
        result
    }

    /// Identity of the original definition (stable across
    /// substitutions). Useful as a cache key.
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.original) as usize
    }

    pub(crate) fn new_internal(name: BinderHint, body: Term, body_type: Type) -> Self {
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
// HolOp — folded-in HOL primitive operators
// ============================================================================

/// HOL Light's primitive operators, folded into the kernel.
///
/// Every variant denotes a *single* HOL constant. The
/// [`TermKind::HolOp`] variant pairs it with the instance type at the
/// point of use:
///
/// - Non-polymorphic ops (`Imp`, `Not`, `And`, `Or`, `Iff`,
///   `Trueprop`) take a fixed type (e.g., `bool → bool → bool`).
/// - Polymorphic ops (`Eq`, `Forall`, `Exists`, `Select`) carry the
///   instance type at α (e.g., `Eq` at α has full type
///   `α → α → bool`).
///
/// Soundness for the type field is enforced by `type_of_in`, which
/// matches the stored type against the operator's expected shape.
/// True / False are *not* HOL ops — they are kernel literals
/// [`TermKind::Bool`].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum HolOp {
    /// HOL `=` at type `α → α → bool` for the α stored alongside.
    Eq,
    /// HOL `==>` at type `bool → bool → bool`.
    Imp,
    /// HOL `~` at type `bool → bool`.
    Not,
    /// HOL `/\` at type `bool → bool → bool`.
    And,
    /// HOL `\/` at type `bool → bool → bool`.
    Or,
    /// HOL `<=>` at type `bool → bool → bool`.
    Iff,
    /// HOL `∀` at type `(α → bool) → bool`.
    Forall,
    /// HOL `∃` at type `(α → bool) → bool`.
    Exists,
    /// HOL `ε` (Hilbert's choice) at type `(α → bool) → α`.
    Select,
    /// `Trueprop : bool → prop` — explicit coercion from HOL `bool` to
    /// the kernel's meta-prop, mirroring Isabelle/HOL's `Trueprop`.
    Trueprop,
}

impl HolOp {
    /// Printable label, matching HOL Light's surface syntax.
    pub fn label(&self) -> &'static str {
        match self {
            HolOp::Eq => "=",
            HolOp::Imp => "==>",
            HolOp::Not => "~",
            HolOp::And => "/\\",
            HolOp::Or => "\\/",
            HolOp::Iff => "<=>",
            HolOp::Forall => "!",
            HolOp::Exists => "?",
            HolOp::Select => "@",
            HolOp::Trueprop => "Trueprop",
        }
    }
}

impl fmt::Display for HolOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

// ============================================================================
// Term
// ============================================================================

#[derive(Clone)]
pub struct Term(Arc<TermKind>);

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermKind {
    /// de Bruijn–indexed bound variable. Index 0 refers to the
    /// innermost surrounding binder (`Abs` or `All`).
    Bound(u32),
    /// Free variable: name + declared type.
    Free(SmolStr, Type),
    /// Declared/defined constant: name + instance type.
    Const(SmolStr, Type),
    /// Application `f x`.
    App(Term, Term),
    /// Abstraction `λ(hint:ty). body`. `body` uses Bound(0) for the
    /// binder; `hint` is a display label (α-transparent).
    Abs(BinderHint, Type, Term),
    /// Meta-implication `φ ⟹ ψ`.
    Imp(Term, Term),
    /// Meta-universal `⋀(hint:ty). body`. Same layout as `Abs`.
    All(BinderHint, Type, Term),
    /// Meta-equality `t ≡ u`.
    Eq(Term, Term),
    /// Builtin: opaque byte literal of kernel type `bytes`.
    Blob(Bytes),
    /// Builtin: natural-number literal. Kernel type `nat`. See
    /// [`crate::Thm::reduce_prim`] for the single-step computation
    /// rule that decides closed-form arithmetic by reflexivity.
    Nat(Nat),
    /// Builtin: integer literal. Kernel type `int`.
    Int(Int),
    /// Builtin: HOL `bool` literal (`T` / `F`). Kernel type
    /// `TypeKind::Bool`. First-class kernel atom — not a separate
    /// observer system.
    Bool(bool),
    /// Folded-in HOL primitive operator at its instance type. See
    /// [`HolOp`] for the catalogue. Applications are formed by the
    /// usual `App` chain.
    HolOp(HolOp, Type),
    /// Application of a derived-term [`crate::defs::TermSpec`]
    /// factory to type arguments. The spec is process-shared
    /// (`LazyLock`-backed) and `args` is the positional substitution
    /// for the spec's type variables.
    ///
    /// Used by `crate::defs::*` to embed semi-trusted term constants
    /// (`natAdd`, `listMap`, …) as catalogue entries instead of
    /// dedicated kernel variants. `Thm::reduce_prim` recognises a
    /// `Spec(h, args)` leaf by `h.ptr_eq(&catalogue_handle)`.
    Spec(crate::defs::TermSpec, Vec<Type>),
    /// Typed observation leaf: observer + Pure type. The kernel
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
        &self.0
    }

    /// Pointer identity of the underlying `Arc`. Useful as a cache key
    /// for outside-the-TCB walkers (hashers, pretty-printers).
    pub fn ptr_id(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }

    fn alloc(kind: TermKind) -> Self {
        Term(Arc::new(kind))
    }

    // ---- smart constructors ----
    pub fn bound(idx: u32) -> Self {
        Self::alloc(TermKind::Bound(idx))
    }
    pub fn free(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Free(name.into(), ty))
    }
    pub fn const_(name: impl Into<SmolStr>, ty: Type) -> Self {
        Self::alloc(TermKind::Const(name.into(), ty))
    }
    pub fn app(fun: Term, arg: Term) -> Self {
        Self::alloc(TermKind::App(fun, arg))
    }
    pub fn abs(hint: impl Into<BinderHint>, ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::Abs(hint.into(), ty, body))
    }
    pub fn imp(lhs: Term, rhs: Term) -> Self {
        Self::alloc(TermKind::Imp(lhs, rhs))
    }
    pub fn all(hint: impl Into<BinderHint>, ty: Type, body: Term) -> Self {
        Self::alloc(TermKind::All(hint.into(), ty, body))
    }
    pub fn eq(lhs: Term, rhs: Term) -> Self {
        Self::alloc(TermKind::Eq(lhs, rhs))
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

    /// HOL `bool` literal — `Bool(true)` is `T`, `Bool(false)` is
    /// `F`. Kernel type `bool`.
    pub fn bool_lit(b: bool) -> Self {
        Self::alloc(TermKind::Bool(b))
    }

    /// HOL operator constant at the supplied instance type. Used by
    /// `covalence-hol`'s `HolLightCtx::mk_*` builders.
    pub fn hol_op(op: HolOp, ty: Type) -> Self {
        Self::alloc(TermKind::HolOp(op, ty))
    }

    /// Apply a derived-term [`crate::defs::TermSpec`] to type
    /// arguments. The spec is process-shared (`LazyLock`-backed in
    /// `crate::defs`); two calls with handles from the same lazy
    /// static pointer-equal at the spec component.
    pub fn term_spec(spec: crate::defs::TermSpec, args: Vec<Type>) -> Self {
        Self::alloc(TermKind::Spec(spec, args))
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
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::HolOp(_, _) => true,
            TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
                a.has_no_obs() && b.has_no_obs()
            }
            TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => body.has_no_obs(),
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
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::HolOp(_, _) => true,
            TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
                a.all_obs_match::<O>() && b.all_obs_match::<O>()
            }
            TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => body.all_obs_match::<O>(),
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
            | TermKind::Bool(_)
            | TermKind::Spec(_, _)
            | TermKind::HolOp(_, _) => Ok(()),
            TermKind::App(a, b) | TermKind::Imp(a, b) | TermKind::Eq(a, b) => {
                a.for_each_obs::<O, F>(f)?;
                b.for_each_obs::<O, F>(f)
            }
            TermKind::Abs(_, _, body) | TermKind::All(_, _, body) => body.for_each_obs::<O, F>(f),
            TermKind::Def(d) => d.body().for_each_obs::<O, F>(f),
        }
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}
impl Eq for Term {}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
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
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TermKind::Bound(i) => write!(f, "@{}", i),
            TermKind::Free(name, _) | TermKind::Const(name, _) => write!(f, "{}", name),
            TermKind::App(g, x) => write!(f, "({} {})", g, x),
            TermKind::Abs(hint, ty, body) if hint.is_empty() => write!(f, "(λ:{}. {})", ty, body),
            TermKind::Abs(hint, ty, body) => write!(f, "(λ{}:{}. {})", hint, ty, body),
            TermKind::Imp(a, b) => write!(f, "({} ⟹ {})", a, b),
            TermKind::All(hint, ty, body) if hint.is_empty() => write!(f, "(⋀:{}. {})", ty, body),
            TermKind::All(hint, ty, body) => write!(f, "(⋀{}:{}. {})", hint, ty, body),
            TermKind::Eq(a, b) => write!(f, "({} ≡ {})", a, b),
            TermKind::Blob(b) => write!(f, "blob[{}]", b.len()),
            TermKind::Nat(n) => write!(f, "{}n", n.as_inner()),
            TermKind::Int(n) => write!(f, "{}i", n.as_inner()),
            TermKind::Bool(b) => write!(f, "{}", if *b { "T" } else { "F" }),
            TermKind::HolOp(op, ty) => write!(f, "{op}:{ty}"),
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
            TermKind::Obs(observer, ty) => write!(f, "obs[{:?}:{}]", observer, ty),
            TermKind::Def(d) => write!(f, "{}", d),
        }
    }
}

// ============================================================================
// Type-of
// ============================================================================

/// Carries the binder context plus the first-seen type of every free
/// variable referenced so far. Pass the same env across every term in
/// a theorem to enforce HOL Light–style cross-term consistency for
/// free variables.
#[derive(Default)]
pub(crate) struct TypeEnv {
    /// Stack of binder types; the innermost binder is at the top.
    ctx: Vec<Type>,
    /// First-seen type for each Free name; subsequent occurrences must
    /// match. Scope is whatever set of terms share this env.
    frees: BTreeMap<SmolStr, Type>,
}

/// Type-check `t` in `env`. The env carries the binder context plus
/// every Free name we have already seen, with its declared type.
/// Subsequent occurrences (in `t` or in later calls sharing the env)
/// must use the same type.
pub(crate) fn type_of_in(t: &Term, env: &mut TypeEnv) -> Result<Type> {
    match t.kind() {
        TermKind::Bound(i) => {
            let i = *i as usize;
            if i >= env.ctx.len() {
                return Err(Error::NotClosed);
            }
            Ok(env.ctx[env.ctx.len() - 1 - i].clone())
        }
        TermKind::Free(name, ty) => {
            if let Some(prev) = env.frees.get(name) {
                if prev != ty {
                    return Err(Error::FreeVarReuse {
                        name: name.clone(),
                        first: prev.clone(),
                        second: ty.clone(),
                    });
                }
            } else {
                env.frees.insert(name.clone(), ty.clone());
            }
            Ok(ty.clone())
        }
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
        TermKind::Abs(_, ty, body) => {
            env.ctx.push(ty.clone());
            let body_ty = type_of_in(body, env);
            env.ctx.pop();
            Ok(Type::fun(ty.clone(), body_ty?))
        }
        TermKind::All(_, ty, body) => {
            env.ctx.push(ty.clone());
            let body_ty = type_of_in(body, env);
            env.ctx.pop();
            let body_ty = body_ty?;
            if !body_ty.is_prop() {
                return Err(Error::NotProp(body_ty));
            }
            Ok(Type::prop())
        }
        TermKind::Imp(a, b) => {
            let ta = type_of_in(a, env)?;
            if !ta.is_prop() {
                return Err(Error::NotProp(ta));
            }
            let tb = type_of_in(b, env)?;
            if !tb.is_prop() {
                return Err(Error::NotProp(tb));
            }
            Ok(Type::prop())
        }
        TermKind::Eq(a, b) => {
            let ta = type_of_in(a, env)?;
            let tb = type_of_in(b, env)?;
            if ta != tb {
                return Err(Error::TypeMismatch {
                    expected: ta,
                    got: tb,
                });
            }
            Ok(Type::prop())
        }
        TermKind::Blob(_) => Ok(Type::bytes()),
        TermKind::Nat(_) => Ok(Type::nat()),
        TermKind::Int(_) => Ok(Type::int()),
        TermKind::Bool(_) => Ok(Type::bool()),
        // A `Spec` leaf's type is the spec's own `ty` field (the
        // factory's carrier) with positional type-arg substitution
        // applied. The spec is held by handle; deref is cheap.
        TermKind::Spec(spec, args) => {
            let mut result = spec
                .ty()
                .cloned()
                .ok_or_else(|| Error::NotProp(Type::prop()))?;
            // free_tvars on the carrier gives the spec's tvar names
            // in canonical alphabetical order. Substitute positionally.
            let tvars = result.free_tvars();
            for (tvar_name, arg) in tvars.iter().zip(args.iter()) {
                result = crate::subst::subst_tfree_in_type(&result, tvar_name, arg);
            }
            Ok(result)
        }
        TermKind::HolOp(_, ty) => Ok(ty.clone()),
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
