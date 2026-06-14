//! Fixed-width integer operations — the WebAssembly-style arithmetic,
//! bitwise, comparison, conversion and cast ops on the `uN`/`sN`
//! literal types (`u8`…`u64`, `s8`…`s64`).
//!
//! ## Why a registry instead of one `Canonical` per op
//!
//! There are 8 literal widths and ~16 ops each, plus the
//! width × width conversion grid and the nat/int casts — several
//! hundred constants. Rather than mint a `Canonical` variant per
//! `(width, op)`, every op here is a [`TermSpec`] tagged with a plain
//! `SmolStr` symbol (`"u8.add"`, `"s32.lt"`, `"u16.zext.u64"`, …) and
//! cached in a process-wide registry keyed by [`OpKey`].
//!
//! Closed-form reduction (`builtins::reduce_spec`) dispatches the same
//! way the rest of the catalogue does — by pointer identity on the
//! cached `Arc` — via [`lookup_op`], which reverse-maps a spec's
//! `ptr_id()` back to its [`OpKey`]. A user-built spec that merely
//! *shares a label* is a different allocation, so it is absent from
//! the reverse map and never reduces — the same safety the `ptr_eq`
//! dispatch gives the hand-written ops.
//!
//! These ops are **declaration-only** (`tm = None`): sound, and
//! complete *on literals* through the reduction rules in
//! `builtins.rs`. Open-form definitional bodies (e.g. via the `bits`
//! carrier) are a follow-up — see `docs/roadmap.md`. The one
//! exception is list-indexing-by-`uN`/`sN`, which gets a real body
//! (`list.index` composed with `toNat`).

use std::collections::HashMap;
use std::sync::LazyLock;

use smol_str::SmolStr;

use crate::hol;
use crate::term::{IntTag, Term, Type};

use super::list::{list, list_index};
use super::spec::TermSpec;

// ============================================================================
// Op vocabulary
// ============================================================================

/// A width-homogeneous integer operation. Signedness is carried by the
/// operand *type* (`uN` vs `sN`), so a single `Div`/`Shr`/`Lt` covers
/// both — the reduction interprets the bits per the operand's tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntOp {
    // Binary arithmetic / bitwise: `T → T → T`.
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    // Comparison: `T → T → bool`.
    Lt,
    Le,
    Gt,
    Ge,
    // Unary: `T → T`.
    Neg,
    Not,
}

impl IntOp {
    /// Dotted label fragment (`"add"`, `"lt"`, `"neg"`, …).
    fn label(self) -> &'static str {
        match self {
            IntOp::Add => "add",
            IntOp::Sub => "sub",
            IntOp::Mul => "mul",
            IntOp::Div => "div",
            IntOp::Rem => "rem",
            IntOp::And => "and",
            IntOp::Or => "or",
            IntOp::Xor => "xor",
            IntOp::Shl => "shl",
            IntOp::Shr => "shr",
            IntOp::Lt => "lt",
            IntOp::Le => "le",
            IntOp::Gt => "gt",
            IntOp::Ge => "ge",
            IntOp::Neg => "neg",
            IntOp::Not => "not",
        }
    }

    /// `true` for the comparison ops (`T → T → bool`).
    pub(crate) fn is_cmp(self) -> bool {
        matches!(self, IntOp::Lt | IntOp::Le | IntOp::Gt | IntOp::Ge)
    }

    /// `true` for the unary ops (`T → T`).
    pub(crate) fn is_unary(self) -> bool {
        matches!(self, IntOp::Neg | IntOp::Not)
    }

    const ALL: [IntOp; 16] = [
        IntOp::Add,
        IntOp::Sub,
        IntOp::Mul,
        IntOp::Div,
        IntOp::Rem,
        IntOp::And,
        IntOp::Or,
        IntOp::Xor,
        IntOp::Shl,
        IntOp::Shr,
        IntOp::Lt,
        IntOp::Le,
        IntOp::Gt,
        IntOp::Ge,
        IntOp::Neg,
        IntOp::Not,
    ];
}

/// Identity of a catalogue entry — the registry key and the value
/// [`lookup_op`] returns for reduction dispatch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum OpKey {
    /// Width-homogeneous op at a tag.
    Op(IntTag, IntOp),
    /// `zext src → dst` — zero-extend (unsigned reinterpret) `src` then
    /// wrap to `dst`. Doubles as `wrap` when `dst` is narrower.
    Zext(IntTag, IntTag),
    /// `sext src → dst` — sign-extend (signed reinterpret) `src` then
    /// wrap to `dst`.
    Sext(IntTag, IntTag),
    /// `toNat : T → nat` — the unsigned value of the bits.
    ToNat(IntTag),
    /// `toInt : T → int` — the (signed for `sN`) value of the bits.
    ToInt(IntTag),
    /// `fromNat : nat → T` — wrap a nat into `T` (mod `2^width`).
    FromNat(IntTag),
    /// `fromInt : int → T` — wrap an int into `T` (two's complement).
    FromInt(IntTag),
}

impl OpKey {
    /// The dotted symbol label, e.g. `"u8.add"`, `"u16.zext.u64"`,
    /// `"s32.toInt"`.
    fn label(self) -> String {
        match self {
            OpKey::Op(t, op) => format!("{}.{}", t.label(), op.label()),
            OpKey::Zext(s, d) => format!("{}.zext.{}", s.label(), d.label()),
            OpKey::Sext(s, d) => format!("{}.sext.{}", s.label(), d.label()),
            OpKey::ToNat(t) => format!("{}.toNat", t.label()),
            OpKey::ToInt(t) => format!("{}.toInt", t.label()),
            OpKey::FromNat(t) => format!("{}.fromNat", t.label()),
            OpKey::FromInt(t) => format!("{}.fromInt", t.label()),
        }
    }

    /// The op's kernel type.
    fn ty(self) -> Type {
        match self {
            OpKey::Op(t, op) if op.is_unary() => Type::fun(t.ty(), t.ty()),
            OpKey::Op(t, op) if op.is_cmp() => {
                Type::fun(t.ty(), Type::fun(t.ty(), Type::bool()))
            }
            OpKey::Op(t, _) => Type::fun(t.ty(), Type::fun(t.ty(), t.ty())),
            OpKey::Zext(s, d) | OpKey::Sext(s, d) => Type::fun(s.ty(), d.ty()),
            OpKey::ToNat(t) => Type::fun(t.ty(), Type::nat()),
            OpKey::ToInt(t) => Type::fun(t.ty(), Type::int()),
            OpKey::FromNat(t) => Type::fun(Type::nat(), t.ty()),
            OpKey::FromInt(t) => Type::fun(Type::int(), t.ty()),
        }
    }
}

// ============================================================================
// Registry
// ============================================================================

fn all_keys() -> Vec<OpKey> {
    let mut keys = Vec::new();
    for &t in &IntTag::ALL {
        for op in IntOp::ALL {
            keys.push(OpKey::Op(t, op));
        }
        keys.push(OpKey::ToNat(t));
        keys.push(OpKey::ToInt(t));
        keys.push(OpKey::FromNat(t));
        keys.push(OpKey::FromInt(t));
    }
    for &s in &IntTag::ALL {
        for &d in &IntTag::ALL {
            keys.push(OpKey::Zext(s, d));
            keys.push(OpKey::Sext(s, d));
        }
    }
    keys
}

/// `OpKey → TermSpec`, the canonical cached specs (one `Arc` each).
static FORWARD: LazyLock<HashMap<OpKey, TermSpec>> = LazyLock::new(|| {
    all_keys()
        .into_iter()
        .map(|key| {
            let spec = TermSpec::new(SmolStr::from(key.label()), Some(key.ty()), None);
            (key, spec)
        })
        .collect()
});

/// `spec.ptr_id() → OpKey`, the reverse map used by reduction
/// dispatch. Only the canonical `FORWARD` allocations appear here.
static REVERSE: LazyLock<HashMap<usize, OpKey>> =
    LazyLock::new(|| FORWARD.iter().map(|(k, spec)| (spec.ptr_id(), *k)).collect());

fn spec_for(key: OpKey) -> TermSpec {
    FORWARD
        .get(&key)
        .expect("every OpKey is registered in FORWARD")
        .clone()
}

/// Recover the [`OpKey`] of a catalogue spec by pointer identity, or
/// `None` if `handle` is not one of the canonical fixed-width-int ops.
pub(crate) fn lookup_op(handle: &TermSpec) -> Option<OpKey> {
    REVERSE.get(&handle.ptr_id()).copied()
}

// ============================================================================
// Public term accessors
// ============================================================================

/// The op constant `op` at width/signedness `tag` (e.g.
/// `int_op(U8, Add) : u8 → u8 → u8`).
pub fn int_op_spec(tag: IntTag, op: IntOp) -> TermSpec {
    spec_for(OpKey::Op(tag, op))
}
/// [`int_op_spec`] applied to no type args, as a [`Term`].
pub fn int_op(tag: IntTag, op: IntOp) -> Term {
    Term::term_spec(int_op_spec(tag, op), Vec::new())
}

/// `zext : src → dst` — zero-extend then wrap.
pub fn int_zext(src: IntTag, dst: IntTag) -> Term {
    Term::term_spec(spec_for(OpKey::Zext(src, dst)), Vec::new())
}
/// `sext : src → dst` — sign-extend then wrap.
pub fn int_sext(src: IntTag, dst: IntTag) -> Term {
    Term::term_spec(spec_for(OpKey::Sext(src, dst)), Vec::new())
}

/// `toNat : tag → nat` — the unsigned value of the bits.
pub fn int_to_nat(tag: IntTag) -> Term {
    Term::term_spec(spec_for(OpKey::ToNat(tag)), Vec::new())
}
/// `toInt : tag → int` — the value (signed for `sN`).
pub fn int_to_int(tag: IntTag) -> Term {
    Term::term_spec(spec_for(OpKey::ToInt(tag)), Vec::new())
}
/// `fromNat : nat → tag` — wrap a nat into `tag`.
pub fn int_from_nat(tag: IntTag) -> Term {
    Term::term_spec(spec_for(OpKey::FromNat(tag)), Vec::new())
}
/// `fromInt : int → tag` — wrap an int into `tag` (two's complement).
pub fn int_from_int(tag: IntTag) -> Term {
    Term::term_spec(spec_for(OpKey::FromInt(tag)), Vec::new())
}

// ============================================================================
// List indexing by a fixed-width integer
// ============================================================================

/// Body of `list.index.<tag> : tag → list 'a → option 'a` ≡
/// `λi xs. list.index (tag.toNat i) xs` — index a list by a `uN`/`sN`
/// value, via the unsigned value of its bits.
fn list_index_body(tag: IntTag) -> Term {
    let alpha = Type::tfree("a");
    let n = Term::app(int_to_nat(tag), Term::free("i", tag.ty()));
    let indexed = Term::app(
        Term::app(list_index(alpha.clone()), n),
        Term::free("xs", list(alpha.clone())),
    );
    let lam_xs = hol::pub_abs("xs", list(alpha), indexed);
    hol::pub_abs("i", tag.ty(), lam_xs)
}

static LIST_INDEX: LazyLock<HashMap<IntTag, TermSpec>> = LazyLock::new(|| {
    IntTag::ALL
        .iter()
        .map(|&tag| {
            let body = list_index_body(tag);
            let ty = body
                .type_of()
                .expect("list.index.<tag> body must type-check");
            let label = format!("list.index.{}", tag.label());
            (tag, TermSpec::new(SmolStr::from(label), Some(ty), Some(body)))
        })
        .collect()
});

/// `list.index.<tag> : tag → list 'a → option 'a` — index a list by a
/// fixed-width integer. Defined as `λi xs. list.index (toNat i) xs`.
pub fn list_index_int_spec(tag: IntTag) -> TermSpec {
    LIST_INDEX
        .get(&tag)
        .expect("every tag has a list-index spec")
        .clone()
}
/// [`list_index_int_spec`] at element type `alpha`.
pub fn list_index_int(tag: IntTag, alpha: Type) -> Term {
    Term::term_spec(list_index_int_spec(tag), vec![alpha])
}
