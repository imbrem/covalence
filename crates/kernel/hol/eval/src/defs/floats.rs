//! `f32 := u32`, `f64 := u64` — bitwise aliases for IEEE 754 floats — plus
//! the **bit-level float op registry** (stage F2b).
//!
//! ## The two-layer float architecture (mirrors `int`)
//!
//! **Layer 1 (here, TCB-by-manifest):** every WASM float operation appears as
//! a *bit-level* HOL constant on the raw bit types — `f32.addBits : u32 →
//! u32 → u32`, `f64.leBits : u64 → u64 → bool`, `u32.truncSatBits.f32 : u32 →
//! u32`, … All are **declaration-only** ([`TermSpec`] with `tm = None`) — the
//! same pattern as the fixed-width conversions in [`super::int_ops`]: they
//! are the primitive reducible interface, complete *on literals* via the
//! `FloatCert` certificate family (`crate::rules::FloatCert`, dispatched by
//! `crate::certs::float_bits` through the trusted
//! `covalence-pure-trusted::float` [`CanonRule`](covalence_pure::CanonRule)s
//! — the single NaN-canonicalization point, WASM deterministic profile,
//! pinned bit-for-bit against wasmtime by
//! `covalence-pure-eval/tests/differential_float.rs`).
//!
//! **Layer 2 (stage F2c, untrusted):** the *typed* ops `f64.add : f64 → f64 →
//! f64` ([`TypedF64`], the registry at the bottom of this module) are
//! ordinary **let-style** defined constants — `fromBits`/`toBits` wrappers
//! over the layer-1 constants via the `spec_abs`/`spec_rep` coercions on the
//! `f32 := u32` / `f64 := u64` newtypes below (`f64.add := λa b.
//! fromBits (f64.addBits (toBits a) (toBits b))`). Being let-style and
//! monomorphic they ride the S9 twin machinery (`covalence-init`'s
//! `init/twins.rs`) unchanged, and closed applications reduce through the
//! untrusted driver in `crate::typed_float` (definitional unfold → coercion
//! round-trip → `FloatCert`) with **no new trusted rule**. Only the ops ball
//! arithmetic needs are registered; `f32` and the rest of the op set follow
//! the same recipe when needed.
//!
//! ## Registry shape
//!
//! Like [`super::int_ops`], the ops are keyed by [`FloatKey`] in a
//! process-wide registry and dispatched by **canonical pointer identity**
//! ([`lookup_float_op`] reverse-maps a spec's `ptr_id()`); a user-built spec
//! that merely shares a label is a different allocation and never reduces.
//!
//! ## Scope decisions (F2b)
//!
//! - The `trunc_sat`/`convert` families ARE included (they were cheap: the
//!   base `CanonRule`s exist and are differential-tested; only the four
//!   32/64-bit tags `u32`/`u64`/`s32`/`s64` are registered, matching WASM).
//! - The `reinterpret` ops are **deliberately absent**: at the bit level they
//!   are the identity on `u32`/`u64` bits — the layer-2 `fromBits`/`toBits`
//!   coercions *are* the reinterpretation.

use std::collections::HashMap;
use std::sync::LazyLock;

use smol_str::SmolStr;

use covalence_core::subst;
use covalence_core::term::{IntTag, Term, TermKind, Type};

use crate::defs::Canonical;
use crate::defs::TypeSpec;
use crate::defs::{TermSpec, u32_ty, u64_ty};

/// `f32 := u32` — bitwise.
pub fn f32_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| TypeSpec::newtype(Canonical::F32, u32_ty()));
    LAZY.clone()
}
pub fn f32_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(f32_spec(), vec![]));
    LAZY.clone()
}

/// `f64 := u64`.
pub fn f64_spec() -> TypeSpec {
    static LAZY: LazyLock<TypeSpec> = LazyLock::new(|| TypeSpec::newtype(Canonical::F64, u64_ty()));
    LAZY.clone()
}
pub fn f64_ty() -> Type {
    static LAZY: LazyLock<Type> = LazyLock::new(|| Type::spec(f64_spec(), vec![]));
    LAZY.clone()
}

// ============================================================================
// Bit-level op vocabulary
// ============================================================================

/// A float width: which bit type carries the IEEE 754 pattern.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatWidth {
    /// `f32` — bits in `u32`.
    F32,
    /// `f64` — bits in `u64`.
    F64,
}

impl FloatWidth {
    /// Dotted label prefix (`"f32"` / `"f64"`).
    pub fn label(self) -> &'static str {
        match self {
            FloatWidth::F32 => "f32",
            FloatWidth::F64 => "f64",
        }
    }

    /// The kernel bit-pattern type (`u32` / `u64`).
    pub fn bits_ty(self) -> Type {
        match self {
            FloatWidth::F32 => u32_ty(),
            FloatWidth::F64 => u64_ty(),
        }
    }

    /// Both widths.
    pub const ALL: [FloatWidth; 2] = [FloatWidth::F32, FloatWidth::F64];
}

/// A width-homogeneous WASM float operation (bit-level: operands and
/// float-valued results are bit patterns at the width's bit type).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatOp {
    // Binary arithmetic: `bits → bits → bits`.
    Add,
    Sub,
    Mul,
    Div,
    Min,
    Max,
    Copysign,
    // Unary: `bits → bits`.
    Sqrt,
    Abs,
    Neg,
    Ceil,
    Floor,
    Trunc,
    Nearest,
    // Comparison: `bits → bits → bool` (IEEE 754 ordering).
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

impl FloatOp {
    /// Dotted label fragment (`"add"`, `"copysign"`, `"nearest"`, …).
    fn label(self) -> &'static str {
        match self {
            FloatOp::Add => "add",
            FloatOp::Sub => "sub",
            FloatOp::Mul => "mul",
            FloatOp::Div => "div",
            FloatOp::Min => "min",
            FloatOp::Max => "max",
            FloatOp::Copysign => "copysign",
            FloatOp::Sqrt => "sqrt",
            FloatOp::Abs => "abs",
            FloatOp::Neg => "neg",
            FloatOp::Ceil => "ceil",
            FloatOp::Floor => "floor",
            FloatOp::Trunc => "trunc",
            FloatOp::Nearest => "nearest",
            FloatOp::Eq => "eq",
            FloatOp::Ne => "ne",
            FloatOp::Lt => "lt",
            FloatOp::Gt => "gt",
            FloatOp::Le => "le",
            FloatOp::Ge => "ge",
        }
    }

    /// `true` for the comparison ops (`bits → bits → bool`).
    pub fn is_cmp(self) -> bool {
        matches!(
            self,
            FloatOp::Eq | FloatOp::Ne | FloatOp::Lt | FloatOp::Gt | FloatOp::Le | FloatOp::Ge
        )
    }

    /// `true` for the unary ops (`bits → bits`).
    pub fn is_unary(self) -> bool {
        matches!(
            self,
            FloatOp::Sqrt
                | FloatOp::Abs
                | FloatOp::Neg
                | FloatOp::Ceil
                | FloatOp::Floor
                | FloatOp::Trunc
                | FloatOp::Nearest
        )
    }

    /// Every op, in declaration order.
    pub const ALL: [FloatOp; 20] = [
        FloatOp::Add,
        FloatOp::Sub,
        FloatOp::Mul,
        FloatOp::Div,
        FloatOp::Min,
        FloatOp::Max,
        FloatOp::Copysign,
        FloatOp::Sqrt,
        FloatOp::Abs,
        FloatOp::Neg,
        FloatOp::Ceil,
        FloatOp::Floor,
        FloatOp::Trunc,
        FloatOp::Nearest,
        FloatOp::Eq,
        FloatOp::Ne,
        FloatOp::Lt,
        FloatOp::Gt,
        FloatOp::Le,
        FloatOp::Ge,
    ];
}

/// The integer tags the `trunc_sat`/`convert` families are registered at —
/// exactly WASM's 32/64-bit scalar int sorts.
pub const FLOAT_CVT_TAGS: [IntTag; 4] = [IntTag::U32, IntTag::U64, IntTag::S32, IntTag::S64];

/// Identity of a bit-level float catalogue entry — the registry key and the
/// value [`lookup_float_op`] returns for `FloatCert` reduction dispatch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatKey {
    /// Width-homogeneous op (`f32.addBits`, `f64.geBits`, …).
    Op(FloatWidth, FloatOp),
    /// WASM `f64.promote_f32` on bits: `f64.promoteBits : u32 → u64`.
    Promote,
    /// WASM `f32.demote_f64` on bits: `f32.demoteBits : u64 → u32`.
    Demote,
    /// WASM saturating float→int (`trunc_sat`): float bits at the width →
    /// the tag's value type, e.g. `u32.truncSatBits.f32 : u32 → u32`,
    /// `s64.truncSatBits.f64 : u64 → s64`. Tag ∈ [`FLOAT_CVT_TAGS`].
    TruncSat(FloatWidth, IntTag),
    /// WASM int→float (`convert`): the tag's value type → float bits at the
    /// width, e.g. `f32.convertBits.s32 : s32 → u32`. Tag ∈ [`FLOAT_CVT_TAGS`].
    Convert(FloatWidth, IntTag),
}

impl FloatKey {
    /// The dotted symbol label, e.g. `"f32.addBits"`, `"f64.promoteBits"`,
    /// `"u32.truncSatBits.f32"`, `"f64.convertBits.s64"`.
    fn label(self) -> String {
        match self {
            FloatKey::Op(w, op) => format!("{}.{}Bits", w.label(), op.label()),
            FloatKey::Promote => "f64.promoteBits".to_string(),
            FloatKey::Demote => "f32.demoteBits".to_string(),
            FloatKey::TruncSat(w, t) => format!("{}.truncSatBits.{}", t.label(), w.label()),
            FloatKey::Convert(w, t) => format!("{}.convertBits.{}", w.label(), t.label()),
        }
    }

    /// The op's kernel type (over the raw bit types — never `f32_ty`/`f64_ty`;
    /// the typed layer is stage F2c).
    fn ty(self) -> Type {
        match self {
            FloatKey::Op(w, op) if op.is_unary() => Type::fun(w.bits_ty(), w.bits_ty()),
            FloatKey::Op(w, op) if op.is_cmp() => {
                Type::fun(w.bits_ty(), Type::fun(w.bits_ty(), Type::bool()))
            }
            FloatKey::Op(w, _) => Type::fun(w.bits_ty(), Type::fun(w.bits_ty(), w.bits_ty())),
            FloatKey::Promote => Type::fun(u32_ty(), u64_ty()),
            FloatKey::Demote => Type::fun(u64_ty(), u32_ty()),
            FloatKey::TruncSat(w, t) => Type::fun(w.bits_ty(), t.ty()),
            FloatKey::Convert(w, t) => Type::fun(t.ty(), w.bits_ty()),
        }
    }
}

// ============================================================================
// Registry (declaration-only: `tm = None` for every key)
// ============================================================================

fn all_keys() -> Vec<FloatKey> {
    let mut keys = Vec::new();
    for &w in &FloatWidth::ALL {
        for op in FloatOp::ALL {
            keys.push(FloatKey::Op(w, op));
        }
        for &t in &FLOAT_CVT_TAGS {
            keys.push(FloatKey::TruncSat(w, t));
            keys.push(FloatKey::Convert(w, t));
        }
    }
    keys.push(FloatKey::Promote);
    keys.push(FloatKey::Demote);
    keys
}

/// `FloatKey → TermSpec`, the canonical cached specs (one `Arc` each). All
/// declaration-only — see the module docs.
static FORWARD: LazyLock<HashMap<FloatKey, TermSpec>> = LazyLock::new(|| {
    all_keys()
        .into_iter()
        .map(|key| {
            (
                key,
                TermSpec::new(SmolStr::from(key.label()), Some(key.ty()), None),
            )
        })
        .collect()
});

/// `spec.ptr_id() → FloatKey`, the reverse map used by `FloatCert` dispatch.
/// Only the canonical `FORWARD` allocations appear here.
static REVERSE: LazyLock<HashMap<usize, FloatKey>> = LazyLock::new(|| {
    FORWARD
        .iter()
        .map(|(k, spec)| (spec.ptr_id(), *k))
        .collect()
});

/// The canonical spec for `key`.
pub fn float_bits_spec(key: FloatKey) -> TermSpec {
    FORWARD
        .get(&key)
        .expect("every FloatKey is registered in FORWARD")
        .clone()
}

/// [`float_bits_spec`] applied to no type args, as a [`Term`].
pub fn float_bits_op(key: FloatKey) -> Term {
    Term::term_spec(float_bits_spec(key), Vec::new())
}

/// Recover the [`FloatKey`] of a catalogue spec by pointer identity, or
/// `None` if `handle` is not one of the canonical bit-level float ops.
pub fn lookup_float_op(handle: &TermSpec) -> Option<FloatKey> {
    REVERSE.get(&handle.ptr_id()).copied()
}

// ============================================================================
// Layer 2 (stage F2c, untrusted): typed `f64` ops + the `f64` literal form
// ============================================================================

/// `fromBits : u64 → f64` — the abstraction coercion of the `f64 := u64`
/// newtype. At the bit level this IS WASM's `f64.reinterpret_i64` (see the
/// module docs: the `reinterpret` ops are deliberately absent from the
/// layer-1 registry because the coercions are the reinterpretation).
pub fn f64_from_bits() -> Term {
    Term::spec_abs(f64_spec(), Vec::new())
}

/// `toBits : f64 → u64` — the representation coercion of `f64 := u64`
/// (WASM `i64.reinterpret_f64`).
pub fn f64_to_bits() -> Term {
    Term::spec_rep(f64_spec(), Vec::new())
}

/// Build the concrete `f64` term for `v` — the canonical typed-float
/// literal form `fromBits ⌜v.to_bits()⌝` (the coercion applied to the raw
/// `u64` bit literal). This is the normal form the typed reduction driver
/// produces and consumes; there is no kernel `f64` literal leaf.
pub fn mk_f64(v: f64) -> Term {
    Term::app(f64_from_bits(), crate::lit::mk_u64(v.to_bits()))
}

/// Recognize a concrete `f64` term ([`mk_f64`]'s shape), returning its raw
/// bit pattern. Returns bits — not `f64` — so NaN payloads compare exactly
/// and `-0.0`/`+0.0` stay distinct. `None` for any other shape.
pub fn as_f64_bits(t: &Term) -> Option<u64> {
    let (f, x) = t.as_app()?;
    match f.kind() {
        TermKind::SpecAbs(spec, targs) if targs.is_empty() && spec.ptr_eq(&f64_spec()) => {
            crate::lit::as_u64(x)
        }
        _ => None,
    }
}

/// A typed `f64` operation — the layer-2 (untrusted) op set, exactly what
/// ball arithmetic needs. Each is a **let-style** [`TermSpec`] whose body
/// wraps the matching layer-1 bit constant in the `f64 := u64` coercions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TypedF64 {
    /// `f64.add : f64 → f64 → f64`.
    Add,
    /// `f64.sub : f64 → f64 → f64`.
    Sub,
    /// `f64.mul : f64 → f64 → f64`.
    Mul,
    /// `f64.div : f64 → f64 → f64`.
    Div,
    /// `f64.min : f64 → f64 → f64`.
    Min,
    /// `f64.max : f64 → f64 → f64`.
    Max,
    /// `f64.sqrt : f64 → f64`.
    Sqrt,
    /// `f64.abs : f64 → f64`.
    Abs,
    /// `f64.neg : f64 → f64`.
    Neg,
    /// `f64.eq : f64 → f64 → bool`.
    Eq,
    /// `f64.lt : f64 → f64 → bool`.
    Lt,
    /// `f64.le : f64 → f64 → bool`.
    Le,
}

impl TypedF64 {
    /// Every typed op, in declaration order.
    pub const ALL: [TypedF64; 12] = [
        TypedF64::Add,
        TypedF64::Sub,
        TypedF64::Mul,
        TypedF64::Div,
        TypedF64::Min,
        TypedF64::Max,
        TypedF64::Sqrt,
        TypedF64::Abs,
        TypedF64::Neg,
        TypedF64::Eq,
        TypedF64::Lt,
        TypedF64::Le,
    ];

    /// The layer-1 [`FloatOp`] this typed op wraps.
    fn float_op(self) -> FloatOp {
        match self {
            TypedF64::Add => FloatOp::Add,
            TypedF64::Sub => FloatOp::Sub,
            TypedF64::Mul => FloatOp::Mul,
            TypedF64::Div => FloatOp::Div,
            TypedF64::Min => FloatOp::Min,
            TypedF64::Max => FloatOp::Max,
            TypedF64::Sqrt => FloatOp::Sqrt,
            TypedF64::Abs => FloatOp::Abs,
            TypedF64::Neg => FloatOp::Neg,
            TypedF64::Eq => FloatOp::Eq,
            TypedF64::Lt => FloatOp::Lt,
            TypedF64::Le => FloatOp::Le,
        }
    }

    /// The layer-1 registry key of the wrapped bit constant
    /// (`f64.add ↦ f64.addBits`, …).
    pub fn bits_key(self) -> FloatKey {
        FloatKey::Op(FloatWidth::F64, self.float_op())
    }

    /// `true` for `sqrt`/`abs`/`neg` (`f64 → f64`).
    pub fn is_unary(self) -> bool {
        self.float_op().is_unary()
    }

    /// `true` for `eq`/`lt`/`le` (`f64 → f64 → bool`).
    pub fn is_cmp(self) -> bool {
        self.float_op().is_cmp()
    }

    /// The dotted symbol label (`"f64.add"`, …).
    fn label(self) -> String {
        format!("{}.{}", FloatWidth::F64.label(), self.float_op().label())
    }

    /// The op's kernel type, over the `f64` wrapper type.
    fn ty(self) -> Type {
        let f = f64_ty();
        if self.is_unary() {
            Type::fun(f.clone(), f)
        } else if self.is_cmp() {
            Type::fun(f.clone(), Type::fun(f, Type::bool()))
        } else {
            Type::fun(f.clone(), Type::fun(f.clone(), f))
        }
    }

    /// The let-style body: `λa [b]. [fromBits] (opBits (toBits a) [(toBits b)])`
    /// — the coercion sandwich around the layer-1 constant (comparisons skip
    /// the result coercion; their bit op already lands in `bool`).
    fn body(self) -> Term {
        let f64t = f64_ty();
        let bits = float_bits_op(self.bits_key());
        let rep = f64_to_bits();
        let a = Term::free("a", f64t.clone());
        let inner = if self.is_unary() {
            Term::app(bits, Term::app(rep, a))
        } else {
            let b = Term::free("b", f64t.clone());
            Term::app(
                Term::app(bits, Term::app(rep.clone(), a)),
                Term::app(rep, b),
            )
        };
        let out = if self.is_cmp() {
            inner
        } else {
            Term::app(f64_from_bits(), inner)
        };
        if self.is_unary() {
            Term::abs(f64t, subst::close(&out, "a"))
        } else {
            let inner_abs = Term::abs(f64t.clone(), subst::close(&out, "b"));
            Term::abs(f64t, subst::close(&inner_abs, "a"))
        }
    }
}

/// `TypedF64 → TermSpec`, the canonical cached typed specs (one `Arc` each).
/// All **let-style** (monomorphic body of the declared type) — the shape the
/// S9 twin machinery and the kernel definitional-unfold rule both accept.
static TYPED_FORWARD: LazyLock<HashMap<TypedF64, TermSpec>> = LazyLock::new(|| {
    TypedF64::ALL
        .into_iter()
        .map(|op| {
            (
                op,
                TermSpec::new(SmolStr::from(op.label()), Some(op.ty()), Some(op.body())),
            )
        })
        .collect()
});

/// `spec.ptr_id() → TypedF64`, the reverse map the typed reduction driver
/// dispatches on. Only the canonical `TYPED_FORWARD` allocations appear here.
static TYPED_REVERSE: LazyLock<HashMap<usize, TypedF64>> = LazyLock::new(|| {
    TYPED_FORWARD
        .iter()
        .map(|(k, spec)| (spec.ptr_id(), *k))
        .collect()
});

/// The canonical spec for the typed op.
pub fn f64_op_spec(op: TypedF64) -> TermSpec {
    TYPED_FORWARD
        .get(&op)
        .expect("every TypedF64 is registered in TYPED_FORWARD")
        .clone()
}

/// [`f64_op_spec`] applied to no type args, as a [`Term`].
pub fn f64_op(op: TypedF64) -> Term {
    Term::term_spec(f64_op_spec(op), Vec::new())
}

/// Recover the [`TypedF64`] of a catalogue spec by pointer identity, or
/// `None` if `handle` is not one of the canonical typed `f64` ops.
pub fn lookup_f64_op(handle: &TermSpec) -> Option<TypedF64> {
    TYPED_REVERSE.get(&handle.ptr_id()).copied()
}
