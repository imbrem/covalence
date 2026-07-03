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
//! ## Definitional bodies
//!
//! The **conversions** (`toNat`/`toInt`/`fromNat`/`fromInt`/`zext`/`sext`)
//! stay **declaration-only** (`tm = None`): they are the primitive
//! reducible interface between `uN`/`sN` and `nat`/`int` (sound, and
//! complete *on literals* via `builtins.rs`). Every **operation** is then
//! *defined* over them in [`op_body`] — `add`/`sub`/`mul`/`neg` and
//! `div`/`rem` as `fromInt(intOp (toInt x) (toInt y))` (signed tags) or
//! `fromNat(natOp (toNat x) (toNat y))` (unsigned), bitwise / shifts via
//! the `nat` bit ops, comparisons via `nat.<` / `int.<`. The lone
//! exception still pending is the **arithmetic right shift** `sN >>`
//! (needs a floor-division the catalogue does not yet expose — see
//! `SKELETONS.md`), which remains declaration-only.
//!
//! Because every body reduces to a literal on literal arguments, it is
//! *derivably coupled* to `builtins::reduce_int_op` and must denote the
//! exact same function — guarded by
//! `tests/audit_reduce.rs::audit_reduce_matches_body`. See the
//! [`op_body`] section comment and `kernel-design.md` §9.
//!
//! Also defined: list-indexing-by-`uN`/`sN`, a real body (`list.index`
//! composed with `toNat`).

use std::collections::HashMap;
use std::sync::LazyLock;

use smol_str::SmolStr;

use crate::hol;
use crate::term::{IntTag, Term, Type};

use super::int::{int_add, int_div, int_le, int_lt, int_mod, int_mul, int_neg, int_sub};
use super::list::{list, list_index};
use super::nat::{
    nat_bit_and, nat_bit_or, nat_bit_xor, nat_div, nat_le, nat_lt, nat_mod, nat_shl, nat_shr,
    nat_sub,
};
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
            OpKey::Op(t, op) if op.is_cmp() => Type::fun(t.ty(), Type::fun(t.ty(), Type::bool())),
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
///
/// Built in two phases so a *defined* op's body can reference the primitive
/// conversion specs by the SAME `Arc` the registry dispatches on, without
/// re-entering this `LazyLock` through the public accessors:
///
/// 1. a declaration-only (`tm = None`) spec for every op;
/// 2. overwrite each *defined* op (see [`op_body`]) with a let-style spec
///    whose body is built from the phase-1 conversion specs in the map.
static FORWARD: LazyLock<HashMap<OpKey, TermSpec>> = LazyLock::new(|| {
    let keys = all_keys();
    let mut map: HashMap<OpKey, TermSpec> = keys
        .iter()
        .map(|&key| {
            (
                key,
                TermSpec::new(SmolStr::from(key.label()), Some(key.ty()), None),
            )
        })
        .collect();
    for &key in &keys {
        if let Some(body) = op_body(key, &map) {
            map.insert(
                key,
                TermSpec::new(SmolStr::from(key.label()), Some(key.ty()), Some(body)),
            );
        }
    }
    map
});

// ============================================================================
// Definitional bodies
//
// The fixed-width ops are *defined* by composing the primitive conversions
// (`toNat`/`toInt`/`fromNat`/`fromInt`, which stay declaration-only — they
// are the reducible interface to `nat`/`int`) with `nat`/`int` arithmetic.
//
// SOUNDNESS: every body reduces to a literal on literal arguments (its
// sub-ops all reduce), so it is *derivably coupled* to `builtins::
// reduce_int_op` — each body MUST denote exactly the function the reduction
// computes, on every input. The coupling is enforced by
// `tests/audit_reduce.rs::audit_reduce_matches_body`. See `kernel-design.md`
// §9 for the coupling and the `nat.mod` precedent.
// ============================================================================

/// The definitional body of `key`, or `None` if the op is still
/// declaration-only. `map` supplies the phase-1 specs the bodies reference.
fn op_body(key: OpKey, map: &HashMap<OpKey, TermSpec>) -> Option<Term> {
    let OpKey::Op(tag, op) = key else {
        // Conversions / casts (toNat/toInt/fromNat/fromInt/zext/sext) are
        // the primitive reducible interface; they keep `tm = None`.
        return None;
    };
    let signed = tag.is_signed();
    Some(match op {
        // Ring ops are sign-uniform: two's-complement add/sub/mul/neg are
        // bit-identical for `uN` and `sN`, so wrap the (signed or unsigned,
        // per `toInt[tag]`) integer result back in with `fromInt[tag]`.
        IntOp::Add => int_ring_body(tag, int_add(), map),
        IntOp::Sub => int_ring_body(tag, int_sub(), map),
        IntOp::Mul => int_ring_body(tag, int_mul(), map),
        IntOp::Neg => int_unary_body(tag, int_neg(), map),

        // Bitwise ops are sign-uniform: work on the unsigned bit value.
        IntOp::And => nat_binop_body(tag, nat_bit_and(), map),
        IntOp::Or => nat_binop_body(tag, nat_bit_or(), map),
        IntOp::Xor => nat_binop_body(tag, nat_bit_xor(), map),
        // `~x = (2^w − 1) − x` (the all-ones mask minus the value).
        IntOp::Not => {
            let to_nat = conv(map, OpKey::ToNat(tag));
            let from_nat = conv(map, OpKey::FromNat(tag));
            let xn = Term::app(to_nat, Term::free("x", tag.ty()));
            let comp = Term::app(Term::app(nat_sub(), all_ones(tag.width())), xn);
            hol::pub_abs("x", tag.ty(), Term::app(from_nat, comp))
        }

        // Comparisons are sign-DEPENDENT: unsigned tags compare `toNat`
        // values with `nat.<`, signed tags compare `toInt` values with
        // `int.<`. `gt`/`ge` swap the operands of `lt`/`le`.
        IntOp::Lt if signed => int_cmp_body(tag, int_lt(), false, map),
        IntOp::Le if signed => int_cmp_body(tag, int_le(), false, map),
        IntOp::Gt if signed => int_cmp_body(tag, int_lt(), true, map),
        IntOp::Ge if signed => int_cmp_body(tag, int_le(), true, map),
        IntOp::Lt => nat_cmp_body(tag, nat_lt(), false, map),
        IntOp::Le => nat_cmp_body(tag, nat_le(), false, map),
        IntOp::Gt => nat_cmp_body(tag, nat_lt(), true, map),
        IntOp::Ge => nat_cmp_body(tag, nat_le(), true, map),

        // Division / remainder are sign-DEPENDENT (truncating). `x / 0 = 0`
        // and `x rem 0 = x` (Euclidean) on both sides — see
        // `builtins::int_binop`.
        IntOp::Div if signed => int_ring_body(tag, int_div(), map),
        IntOp::Rem if signed => int_ring_body(tag, int_mod(), map),
        IntOp::Div => nat_binop_body(tag, nat_div(), map),
        IntOp::Rem => nat_binop_body(tag, nat_mod(), map),

        // Left shift is sign-uniform; the shift amount is taken mod width
        // (matching `builtins`). Right shift differs by sign — only the
        // unsigned (logical) case has a body here; arithmetic `sN >>` needs
        // a floor-division the catalogue does not yet expose, so it stays
        // declaration-only (reduces on literals via `builtins`).
        IntOp::Shl => shift_body(tag, nat_shl(), map),
        IntOp::Shr if !signed => shift_body(tag, nat_shr(), map),
        IntOp::Shr => return None,
    })
}

/// The all-ones mask `2^width − 1` as a `nat` literal.
fn all_ones(width: u32) -> Term {
    use covalence_types::Nat;
    let two_pow = Nat::from_inner(Nat::one().as_inner() << (width as usize));
    Term::nat_lit(two_pow.checked_sub(&Nat::one()).expect("2^width ≥ 1"))
}

/// The conversion spec `key` (must be a phase-1 entry) as a 0-ary term.
fn conv(map: &HashMap<OpKey, TermSpec>, key: OpKey) -> Term {
    Term::term_spec(map[&key].clone(), Vec::new())
}

/// `λx y:tag. fromInt[tag] (op (toInt[tag] x) (toInt[tag] y))` — a binary
/// op lifted through `toInt`/`fromInt`.
fn int_ring_body(tag: IntTag, op: Term, map: &HashMap<OpKey, TermSpec>) -> Term {
    let to_int = conv(map, OpKey::ToInt(tag));
    let from_int = conv(map, OpKey::FromInt(tag));
    let xi = Term::app(to_int.clone(), Term::free("x", tag.ty()));
    let yi = Term::app(to_int, Term::free("y", tag.ty()));
    let wrapped = Term::app(from_int, Term::app(Term::app(op, xi), yi));
    hol::pub_abs("x", tag.ty(), hol::pub_abs("y", tag.ty(), wrapped))
}

/// `λx:tag. fromInt[tag] (op (toInt[tag] x))` — a unary op lifted through
/// `toInt`/`fromInt`.
fn int_unary_body(tag: IntTag, op: Term, map: &HashMap<OpKey, TermSpec>) -> Term {
    let to_int = conv(map, OpKey::ToInt(tag));
    let from_int = conv(map, OpKey::FromInt(tag));
    let xi = Term::app(to_int, Term::free("x", tag.ty()));
    let wrapped = Term::app(from_int, Term::app(op, xi));
    hol::pub_abs("x", tag.ty(), wrapped)
}

/// `λx y:tag. fromNat[tag] (op (toNat[tag] x) (toNat[tag] y))` — a binary op
/// lifted through the UNSIGNED interpretation (`toNat`/`fromNat`). Used for
/// the bitwise ops and unsigned div/rem, whose result fits in `width` bits.
fn nat_binop_body(tag: IntTag, op: Term, map: &HashMap<OpKey, TermSpec>) -> Term {
    let to_nat = conv(map, OpKey::ToNat(tag));
    let from_nat = conv(map, OpKey::FromNat(tag));
    let xn = Term::app(to_nat.clone(), Term::free("x", tag.ty()));
    let yn = Term::app(to_nat, Term::free("y", tag.ty()));
    let wrapped = Term::app(from_nat, Term::app(Term::app(op, xn), yn));
    hol::pub_abs("x", tag.ty(), hol::pub_abs("y", tag.ty(), wrapped))
}

/// `λx y:tag. cmp (toNat x) (toNat y)` (operands swapped if `swap`) — an
/// unsigned comparison (`bool` result, no wrap).
fn nat_cmp_body(tag: IntTag, cmp: Term, swap: bool, map: &HashMap<OpKey, TermSpec>) -> Term {
    cmp_body(tag, conv(map, OpKey::ToNat(tag)), cmp, swap)
}

/// `λx y:tag. cmp (toInt x) (toInt y)` (operands swapped if `swap`) — a
/// signed comparison.
fn int_cmp_body(tag: IntTag, cmp: Term, swap: bool, map: &HashMap<OpKey, TermSpec>) -> Term {
    cmp_body(tag, conv(map, OpKey::ToInt(tag)), cmp, swap)
}

/// Shared comparison body: `λx y:tag. cmp (conv x) (conv y)`, optionally
/// swapping the two operands (so `gt`/`ge` reuse `lt`/`le`).
fn cmp_body(tag: IntTag, conv: Term, cmp: Term, swap: bool) -> Term {
    let xc = Term::app(conv.clone(), Term::free("x", tag.ty()));
    let yc = Term::app(conv, Term::free("y", tag.ty()));
    let (l, r) = if swap { (yc, xc) } else { (xc, yc) };
    let body = Term::app(Term::app(cmp, l), r);
    hol::pub_abs("x", tag.ty(), hol::pub_abs("y", tag.ty(), body))
}

/// `λx y:tag. fromNat[tag] (shift (toNat x) (toNat y mod width))` — a shift
/// by `toNat y mod width` (matching `builtins`'s shift-amount masking).
/// `shift` is `nat.shl` (left) or `nat.shr` (logical right).
fn shift_body(tag: IntTag, shift: Term, map: &HashMap<OpKey, TermSpec>) -> Term {
    let to_nat = conv(map, OpKey::ToNat(tag));
    let from_nat = conv(map, OpKey::FromNat(tag));
    let xn = Term::app(to_nat.clone(), Term::free("x", tag.ty()));
    let yn = Term::app(to_nat, Term::free("y", tag.ty()));
    let width = Term::nat_lit(u64::from(tag.width()));
    let amount = Term::app(Term::app(nat_mod(), yn), width);
    let shifted = Term::app(Term::app(shift, xn), amount);
    hol::pub_abs(
        "x",
        tag.ty(),
        hol::pub_abs("y", tag.ty(), Term::app(from_nat, shifted)),
    )
}

/// `spec.ptr_id() → OpKey`, the reverse map used by reduction
/// dispatch. Only the canonical `FORWARD` allocations appear here.
static REVERSE: LazyLock<HashMap<usize, OpKey>> = LazyLock::new(|| {
    FORWARD
        .iter()
        .map(|(k, spec)| (spec.ptr_id(), *k))
        .collect()
});

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
            (
                tag,
                TermSpec::new(SmolStr::from(label), Some(ty), Some(body)),
            )
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
