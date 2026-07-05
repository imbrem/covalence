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
//! f64` are ordinary defined constants — `fromBits`/`toBits` wrappers over
//! the layer-1 constants via the `spec_abs`/`spec_rep` coercions on the
//! `f32 := u32` / `f64 := u64` newtypes below.
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

use covalence_core::term::{IntTag, Term, Type};

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
