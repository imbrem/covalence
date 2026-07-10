//! Per-family certificate **dispatch**: the `decide` bodies of the
//! computation-backed `IsThm` certificate rules in `crate::rules`
//! (`NatArithCert` / `IntArithCert` / `BytesCert` / `FixedWidthCert` /
//! `FloatCert` / `LitEqCert` / `CoercionCert` / `SuccCert`).
//!
//! Each helper takes an **op selector** (a [`TermSpec`], keyed by canonical
//! pointer identity — `spec.ptr_id()` against a table built from the
//! `covalence_core::defs` handles — canonical pointer-identity dispatch) plus
//! **native argument values** ([`Lit`]), computes the result through the
//! matching `covalence-pure-eval` [`CanonRule`](covalence_pure::CanonRule)
//! (the enumerable computation-TCB record — see the `Builtins` manifest
//! golden), and returns the HOL equation `⊢ op ⌜args⌝ = ⌜result⌝` as a
//! [`Term`]. The rule bodies in `crate::rules` then pass it through the
//! `seq` well-typedness floor.
//!
//! In-TCB: a wrong table entry or a wrong literal rebuild here would mint a
//! false equation. The invariants to check:
//!
//! - every table key is a canonical `defs::*_spec()` handle (a user-built
//!   spec sharing the label is a different `Arc` ⇒ absent ⇒ never fires);
//! - arity and literal kinds are matched exactly (anything else refuses with
//!   [`Error::NotReducible`] — a refusal, never a wrong equation);
//! - the computation is the matching `covalence-pure-eval` op (whose FORCED
//!   conventions are pinned by that crate's semantics suite). `CanonRule::eval`
//!   is fallible: an op REFUSES (`None`) on a detectably unrepresentable
//!   result (oversize `nat.pow` exponents / `nat.shl` shifts), which is mapped
//!   to [`Error::NotReducible`] here — a refusal, never a wrong equation.

use std::collections::HashMap;
use std::sync::LazyLock;

use covalence_pure::CanonRule as _;
use covalence_pure_eval as pe;
use covalence_pure_eval::FwRepr;
use covalence_types::{Int, Nat};

use crate::defs;
use crate::defs::int_ops::{IntOp, OpKey, lookup_op};
use crate::defs::{FloatKey, FloatOp, FloatWidth};
use crate::hol;
use covalence_core::seam::Lit;
use covalence_core::{Error, Result};
use covalence_core::{IntTag, SmallIntLiteral, Term, TermSpec, Type};

// ============================================================================
// Families (untrusted classification metadata for drivers)
// ============================================================================

/// Which certificate family a canonical catalogue spec belongs to —
/// **untrusted metadata** for reduction drivers (`covalence-hol-eval`); the
/// gate stays each family rule's own table + `admits`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimFamily {
    /// `nat.*` arithmetic / comparison ([`crate::rules::NatArithCert`]).
    NatArith,
    /// `int.*` arithmetic / comparison ([`crate::rules::IntArithCert`]).
    IntArith,
    /// `bytes.*` ops ([`crate::rules::BytesCert`]).
    Bytes,
    /// nat ↔ int / bytes coercions ([`crate::rules::CoercionCert`]).
    Coercion,
    /// The fixed-width `uN`/`sN` ops ([`crate::rules::FixedWidthCert`]).
    FixedWidth,
    /// The bit-level WASM float ops ([`crate::rules::FloatCert`]).
    Float,
}

/// Classify a spec by canonical pointer identity, or `None` if it is not a
/// reducible catalogue op. Read-only; mints nothing.
pub fn prim_family(spec: &TermSpec) -> Option<PrimFamily> {
    let id = spec.ptr_id();
    if NAT_TABLE.contains_key(&id) {
        Some(PrimFamily::NatArith)
    } else if INT_TABLE.contains_key(&id) {
        Some(PrimFamily::IntArith)
    } else if BYTES_TABLE.contains_key(&id) {
        Some(PrimFamily::Bytes)
    } else if COERCE_TABLE.contains_key(&id) {
        Some(PrimFamily::Coercion)
    } else if lookup_op(spec).is_some() {
        Some(PrimFamily::FixedWidth)
    } else if defs::lookup_float_op(spec).is_some() {
        Some(PrimFamily::Float)
    } else {
        None
    }
}

// ============================================================================
// Op tables (canonical-handle `ptr_id` keyed, one per family)
// ============================================================================

macro_rules! table {
    ($name:ident, $op:ty, [$(($spec:path, $val:expr)),+ $(,)?]) => {
        static $name: LazyLock<HashMap<usize, $op>> = LazyLock::new(|| {
            [$(($spec().ptr_id(), $val)),+].into_iter().collect()
        });
    };
}

#[derive(Clone, Copy)]
enum NatOp {
    Pred,
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    Pow,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Le,
    Lt,
}

table!(
    NAT_TABLE,
    NatOp,
    [
        (defs::nat_pred_spec, NatOp::Pred),
        (defs::nat_add_spec, NatOp::Add),
        (defs::nat_mul_spec, NatOp::Mul),
        (defs::nat_sub_spec, NatOp::Sub),
        (defs::nat_div_spec, NatOp::Div),
        (defs::nat_mod_spec, NatOp::Mod),
        (defs::nat_pow_spec, NatOp::Pow),
        (defs::nat_shl_spec, NatOp::Shl),
        (defs::nat_shr_spec, NatOp::Shr),
        (defs::nat_bit_and_spec, NatOp::BitAnd),
        (defs::nat_bit_or_spec, NatOp::BitOr),
        (defs::nat_bit_xor_spec, NatOp::BitXor),
        (defs::nat_le_spec, NatOp::Le),
        (defs::nat_lt_spec, NatOp::Lt),
    ]
);

#[derive(Clone, Copy)]
enum IntFamOp {
    Succ,
    Pred,
    Neg,
    Abs,
    Sgn,
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    Le,
    Lt,
}

table!(
    INT_TABLE,
    IntFamOp,
    [
        (defs::int_succ_spec, IntFamOp::Succ),
        (defs::int_pred_spec, IntFamOp::Pred),
        (defs::int_neg_spec, IntFamOp::Neg),
        (defs::int_abs_spec, IntFamOp::Abs),
        (defs::int_sgn_spec, IntFamOp::Sgn),
        (defs::int_add_spec, IntFamOp::Add),
        (defs::int_mul_spec, IntFamOp::Mul),
        (defs::int_sub_spec, IntFamOp::Sub),
        (defs::int_div_spec, IntFamOp::Div),
        (defs::int_mod_spec, IntFamOp::Mod),
        (defs::int_le_spec, IntFamOp::Le),
        (defs::int_lt_spec, IntFamOp::Lt),
    ]
);

#[derive(Clone, Copy)]
enum BytesOp {
    Cat,
    ConsNat,
    Len,
    At,
    Slice,
}

table!(
    BYTES_TABLE,
    BytesOp,
    [
        (defs::bytes_cat_spec, BytesOp::Cat),
        (defs::bytes_cons_nat_spec, BytesOp::ConsNat),
        (defs::bytes_len_spec, BytesOp::Len),
        (defs::bytes_at_spec, BytesOp::At),
        (defs::bytes_slice_spec, BytesOp::Slice),
    ]
);

#[derive(Clone, Copy)]
enum CoerceOp {
    ToInt,
    ToBytesLe,
    ToBytesBe,
    FromBytesLe,
    FromBytesBe,
}

table!(
    COERCE_TABLE,
    CoerceOp,
    [
        (defs::nat_to_int_spec, CoerceOp::ToInt),
        (defs::nat_to_bytes_le_spec, CoerceOp::ToBytesLe),
        (defs::nat_to_bytes_be_spec, CoerceOp::ToBytesBe),
        (defs::nat_from_bytes_le_spec, CoerceOp::FromBytesLe),
        (defs::nat_from_bytes_be_spec, CoerceOp::FromBytesBe),
    ]
);

// ============================================================================
// Shared equation builders / argument matchers
// ============================================================================

/// `⊢ spec ⌜args⌝ = rhs`: rebuild the redex from the canonical handle (empty
/// type args — the only shape that reduces) and the literal arguments, then
/// wrap in HOL `=` at the redex's own type. The `type_of` here can only fail
/// on an arity/kind mismatch the caller's matchers let through — treated as
/// a refusal, never trusted.
fn eq_concl(spec: &TermSpec, args: &[Lit], rhs: Term) -> Result<Term> {
    let head = Term::term_spec(spec.clone(), Vec::new());
    let lhs = args.iter().fold(head, |f, a| Term::app(f, a.to_term()));
    let alpha = lhs.type_of()?;
    Ok(hol::hol_eq_at(alpha, lhs, rhs))
}

fn nat1(args: &[Lit]) -> Result<&Nat> {
    match args {
        [Lit::Nat(a)] => Ok(a),
        _ => Err(Error::NotReducible),
    }
}

fn nat2(args: &[Lit]) -> Result<(&Nat, &Nat)> {
    match args {
        [Lit::Nat(a), Lit::Nat(b)] => Ok((a, b)),
        _ => Err(Error::NotReducible),
    }
}

fn int1(args: &[Lit]) -> Result<&Int> {
    match args {
        [Lit::Int(a)] => Ok(a),
        _ => Err(Error::NotReducible),
    }
}

fn int2(args: &[Lit]) -> Result<(&Int, &Int)> {
    match args {
        [Lit::Int(a), Lit::Int(b)] => Ok((a, b)),
        _ => Err(Error::NotReducible),
    }
}

// ============================================================================
// Family dispatch
// ============================================================================

/// `nat.*` arithmetic / comparison — see [`crate::rules::NatArithCert`].
pub(crate) fn nat_arith(spec: &TermSpec, args: &[Lit]) -> Result<Term> {
    let op = *NAT_TABLE.get(&spec.ptr_id()).ok_or(Error::NotReducible)?;
    let pair = |a: &Nat, b: &Nat| (a.clone(), b.clone());
    let rhs = match op {
        NatOp::Pred => Term::nat_lit(pe::NatPred.eval(nat1(args)?).ok_or(Error::NotReducible)?),
        NatOp::Add => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatAdd.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Mul => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatMul.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Sub => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatSub.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Div => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatDiv.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Mod => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatMod.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Pow => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatPow.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Shl => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatShl.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Shr => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatShr.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::BitAnd => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatBitAnd.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::BitOr => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatBitOr.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::BitXor => {
            let (a, b) = nat2(args)?;
            Term::nat_lit(pe::NatBitXor.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Le => {
            let (a, b) = nat2(args)?;
            Term::bool_lit(pe::NatLe.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        NatOp::Lt => {
            let (a, b) = nat2(args)?;
            Term::bool_lit(pe::NatLt.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
    };
    eq_concl(spec, args, rhs)
}

/// The primitive successor on a closed literal — see
/// [`crate::rules::SuccCert`]. (`succ` is a kernel `TermKind::Succ` leaf,
/// not a catalogue spec, so it has no `TermSpec` selector.)
pub(crate) fn succ_concl(n: &Nat) -> Result<Term> {
    let lhs = Term::app(Term::succ(), Term::nat_lit(n.clone()));
    let rhs = Term::nat_lit(pe::NatSucc.eval(n).ok_or(Error::NotReducible)?);
    Ok(hol::hol_eq_at(Type::nat(), lhs, rhs))
}

/// `int.*` arithmetic / comparison — see [`crate::rules::IntArithCert`].
pub(crate) fn int_arith(spec: &TermSpec, args: &[Lit]) -> Result<Term> {
    let op = *INT_TABLE.get(&spec.ptr_id()).ok_or(Error::NotReducible)?;
    let pair = |a: &Int, b: &Int| (a.clone(), b.clone());
    let rhs = match op {
        IntFamOp::Succ => Term::int_lit(pe::IntSucc.eval(int1(args)?).ok_or(Error::NotReducible)?),
        IntFamOp::Pred => Term::int_lit(pe::IntPred.eval(int1(args)?).ok_or(Error::NotReducible)?),
        IntFamOp::Neg => Term::int_lit(pe::IntNeg.eval(int1(args)?).ok_or(Error::NotReducible)?),
        // `int.abs : int → nat`.
        IntFamOp::Abs => Term::nat_lit(pe::IntAbs.eval(int1(args)?).ok_or(Error::NotReducible)?),
        IntFamOp::Sgn => Term::int_lit(pe::IntSgn.eval(int1(args)?).ok_or(Error::NotReducible)?),
        IntFamOp::Add => {
            let (a, b) = int2(args)?;
            Term::int_lit(pe::IntAdd.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        IntFamOp::Mul => {
            let (a, b) = int2(args)?;
            Term::int_lit(pe::IntMul.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        IntFamOp::Sub => {
            let (a, b) = int2(args)?;
            Term::int_lit(pe::IntSub.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        IntFamOp::Div => {
            let (a, b) = int2(args)?;
            Term::int_lit(pe::IntDiv.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        IntFamOp::Mod => {
            let (a, b) = int2(args)?;
            Term::int_lit(pe::IntMod.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        IntFamOp::Le => {
            let (a, b) = int2(args)?;
            Term::bool_lit(pe::IntLe.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
        IntFamOp::Lt => {
            let (a, b) = int2(args)?;
            Term::bool_lit(pe::IntLt.eval(&pair(a, b)).ok_or(Error::NotReducible)?)
        }
    };
    eq_concl(spec, args, rhs)
}

/// `bytes.*` — see [`crate::rules::BytesCert`].
pub(crate) fn bytes_cert(spec: &TermSpec, args: &[Lit]) -> Result<Term> {
    let op = *BYTES_TABLE.get(&spec.ptr_id()).ok_or(Error::NotReducible)?;
    let rhs = match (op, args) {
        (BytesOp::Cat, [Lit::Bytes(a), Lit::Bytes(b)]) => Term::blob(
            pe::BytesCat
                .eval(&(a.clone(), b.clone()))
                .ok_or(Error::NotReducible)?,
        ),
        (BytesOp::ConsNat, [Lit::Nat(n), Lit::Bytes(bs)]) => Term::blob(
            pe::BytesConsNat
                .eval(&(n.clone(), bs.clone()))
                .ok_or(Error::NotReducible)?,
        ),
        (BytesOp::Len, [Lit::Bytes(bs)]) => {
            Term::nat_lit(pe::BytesLen.eval(bs).ok_or(Error::NotReducible)?)
        }
        (BytesOp::At, [Lit::Bytes(bs), Lit::Nat(i)]) => Term::nat_lit(
            pe::BytesAt
                .eval(&(bs.clone(), i.clone()))
                .ok_or(Error::NotReducible)?,
        ),
        (BytesOp::Slice, [Lit::Bytes(bs), Lit::Nat(start), Lit::Nat(len)]) => Term::blob(
            pe::BytesSlice
                .eval(&(bs.clone(), start.clone(), len.clone()))
                .ok_or(Error::NotReducible)?,
        ),
        _ => return Err(Error::NotReducible),
    };
    eq_concl(spec, args, rhs)
}

/// nat ↔ int / bytes coercions — see [`crate::rules::CoercionCert`].
pub(crate) fn coercion(spec: &TermSpec, args: &[Lit]) -> Result<Term> {
    let op = *COERCE_TABLE
        .get(&spec.ptr_id())
        .ok_or(Error::NotReducible)?;
    let rhs = match (op, args) {
        (CoerceOp::ToInt, [Lit::Nat(n)]) => {
            Term::int_lit(pe::NatToInt.eval(n).ok_or(Error::NotReducible)?)
        }
        (CoerceOp::ToBytesLe, [Lit::Nat(n)]) => {
            Term::blob(pe::NatToBytesLe.eval(n).ok_or(Error::NotReducible)?)
        }
        (CoerceOp::ToBytesBe, [Lit::Nat(n)]) => {
            Term::blob(pe::NatToBytesBe.eval(n).ok_or(Error::NotReducible)?)
        }
        (CoerceOp::FromBytesLe, [Lit::Bytes(bs)]) => {
            Term::nat_lit(pe::NatFromBytesLe.eval(bs).ok_or(Error::NotReducible)?)
        }
        (CoerceOp::FromBytesBe, [Lit::Bytes(bs)]) => {
            Term::nat_lit(pe::NatFromBytesBe.eval(bs).ok_or(Error::NotReducible)?)
        }
        _ => return Err(Error::NotReducible),
    };
    eq_concl(spec, args, rhs)
}

/// Closed literal (dis)equality — see [`crate::rules::LitEqCert`]:
/// `⊢ (a = b) = ⌜a == b⌝` for two same-kind literals (the kernel's
/// literal-distinctness commitment: same-kind literals are equal iff
/// structurally equal). Mixed kinds refuse (the equation would be
/// ill-typed anyway).
pub(crate) fn lit_eq(a: &Lit, b: &Lit) -> Result<Term> {
    let same = match (a, b) {
        (Lit::Bool(x), Lit::Bool(y)) => x == y,
        (Lit::Nat(x), Lit::Nat(y)) => x == y,
        (Lit::Int(x), Lit::Int(y)) => x == y,
        (Lit::Small(x), Lit::Small(y)) if x.tag() == y.tag() => x == y,
        (Lit::Bytes(x), Lit::Bytes(y)) => x == y,
        _ => return Err(Error::NotReducible),
    };
    let inner = hol::hol_eq_at(a.hol_type(), a.to_term(), b.to_term());
    Ok(hol::hol_eq_at(Type::bool(), inner, Term::bool_lit(same)))
}

// ============================================================================
// Fixed-width dispatch
// ============================================================================

/// Encode a fixed-width result back into the canonical `u64` payload
/// (sign-extend signed, zero-extend unsigned — the kernel literal payload
/// convention).
fn small_lit<T: FwRepr>(tag: IntTag, v: T) -> SmallIntLiteral {
    let bits = if T::SIGNED {
        v.value_s() as u64
    } else {
        v.value_u() as u64
    };
    SmallIntLiteral::new(tag, bits)
}

fn small1(args: &[Lit], tag: IntTag) -> Result<SmallIntLiteral> {
    match args {
        [Lit::Small(a)] if a.tag() == tag => Ok(*a),
        _ => Err(Error::NotReducible),
    }
}

fn small2(args: &[Lit], tag: IntTag) -> Result<(SmallIntLiteral, SmallIntLiteral)> {
    match args {
        [Lit::Small(a), Lit::Small(b)] if a.tag() == tag && b.tag() == tag => Ok((*a, *b)),
        _ => Err(Error::NotReducible),
    }
}

/// Run `$body` with `$T` bound to the native Rust type of `$tag`
/// (`u8`…`u64` / `i8`…`i64` — the pure-eval [`FwRepr`] sorts).
macro_rules! per_tag {
    ($tag:expr, $T:ident, $body:expr) => {
        match $tag {
            IntTag::U8 => {
                type $T = u8;
                $body
            }
            IntTag::U16 => {
                type $T = u16;
                $body
            }
            IntTag::U32 => {
                type $T = u32;
                $body
            }
            IntTag::U64 => {
                type $T = u64;
                $body
            }
            IntTag::S8 => {
                type $T = i8;
                $body
            }
            IntTag::S16 => {
                type $T = i16;
                $body
            }
            IntTag::S32 => {
                type $T = i32;
                $body
            }
            IntTag::S64 => {
                type $T = i64;
                $body
            }
        }
    };
}

/// The fixed-width `uN`/`sN` ops — see [`crate::rules::FixedWidthCert`].
/// Keyed by the canonical `defs::int_ops` registry ([`lookup_op`], pointer
/// identity); computed by the matching monomorphic pure-eval `Fw*` op.
pub(crate) fn fixed_width(spec: &TermSpec, args: &[Lit]) -> Result<Term> {
    let key = lookup_op(spec).ok_or(Error::NotReducible)?;
    let rhs = match key {
        OpKey::Op(tag, op) if op.is_unary() => {
            let a = small1(args, tag)?;
            per_tag!(tag, T, {
                let av = a.bits() as T;
                let res: T = match op {
                    IntOp::Neg => pe::FwNeg::<T>::new().eval(&av).ok_or(Error::NotReducible)?,
                    IntOp::Not => pe::FwNot::<T>::new().eval(&av).ok_or(Error::NotReducible)?,
                    _ => unreachable!("non-unary op in unary arm"),
                };
                Term::small_int(small_lit(tag, res))
            })
        }
        OpKey::Op(tag, op) if op.is_cmp() => {
            let (a, b) = small2(args, tag)?;
            per_tag!(tag, T, {
                let ab = (a.bits() as T, b.bits() as T);
                let res = match op {
                    IntOp::Lt => pe::FwLt::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Le => pe::FwLe::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Gt => pe::FwGt::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Ge => pe::FwGe::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    _ => unreachable!("non-comparison op in cmp arm"),
                };
                Term::bool_lit(res)
            })
        }
        OpKey::Op(tag, op) => {
            let (a, b) = small2(args, tag)?;
            per_tag!(tag, T, {
                let ab = (a.bits() as T, b.bits() as T);
                let res: T = match op {
                    IntOp::Add => pe::FwAdd::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Sub => pe::FwSub::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Mul => pe::FwMul::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Div => pe::FwDiv::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Rem => pe::FwRem::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::And => pe::FwAnd::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Or => pe::FwOr::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Xor => pe::FwXor::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Shl => pe::FwShl::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    IntOp::Shr => pe::FwShr::<T>::new().eval(&ab).ok_or(Error::NotReducible)?,
                    _ => unreachable!("non-binary-arith op in binop arm"),
                };
                Term::small_int(small_lit(tag, res))
            })
        }
        OpKey::Zext(src, dst) => {
            let a = small1(args, src)?;
            per_tag!(src, S, {
                let av = a.bits() as S;
                per_tag!(dst, D, {
                    Term::small_int(small_lit(
                        dst,
                        pe::Zext::<S, D>::new()
                            .eval(&av)
                            .ok_or(Error::NotReducible)?,
                    ))
                })
            })
        }
        OpKey::Sext(src, dst) => {
            let a = small1(args, src)?;
            per_tag!(src, S, {
                let av = a.bits() as S;
                per_tag!(dst, D, {
                    Term::small_int(small_lit(
                        dst,
                        pe::Sext::<S, D>::new()
                            .eval(&av)
                            .ok_or(Error::NotReducible)?,
                    ))
                })
            })
        }
        OpKey::ToNat(tag) => {
            let a = small1(args, tag)?;
            per_tag!(
                tag,
                T,
                Term::nat_lit(
                    pe::FwToNat::<T>::new()
                        .eval(&(a.bits() as T))
                        .ok_or(Error::NotReducible)?
                )
            )
        }
        OpKey::ToInt(tag) => {
            let a = small1(args, tag)?;
            per_tag!(
                tag,
                T,
                Term::int_lit(
                    pe::FwToInt::<T>::new()
                        .eval(&(a.bits() as T))
                        .ok_or(Error::NotReducible)?
                )
            )
        }
        OpKey::FromNat(tag) => {
            let n = match args {
                [Lit::Nat(n)] => n,
                _ => return Err(Error::NotReducible),
            };
            per_tag!(
                tag,
                T,
                Term::small_int(small_lit(
                    tag,
                    pe::FwFromNat::<T>::new()
                        .eval(n)
                        .ok_or(Error::NotReducible)?
                ))
            )
        }
        OpKey::FromInt(tag) => {
            let z = match args {
                [Lit::Int(z)] => z,
                _ => return Err(Error::NotReducible),
            };
            per_tag!(
                tag,
                T,
                Term::small_int(small_lit(
                    tag,
                    pe::FwFromInt::<T>::new()
                        .eval(z)
                        .ok_or(Error::NotReducible)?
                ))
            )
        }
    };
    eq_concl(spec, args, rhs)
}

// ============================================================================
// Bit-level float dispatch
// ============================================================================

/// Dispatch one width's bit-level [`FloatOp`] through its trusted base
/// CanonRules: decode the `uN` bit literals into the width's float sort
/// (`from_bits` — a raw bit move, no canonicalization), run the op, re-encode
/// (float results back to bit literals via `to_bits`, comparisons to bool
/// literals). The op↔rule pairing below is a trusted table: a transposed
/// entry would mint a false equation (guarded value-for-value by
/// `tests/floats.rs`).
macro_rules! float_op_arm {
    ($W:ident, $tag:expr, $op:expr, $args:expr;
     bin { $($bin:ident => $BinRule:ident),+ $(,)? }
     un { $($un:ident => $UnRule:ident),+ $(,)? }
     cmp { $($cmp:ident => $CmpRule:ident),+ $(,)? }) => {{
        let dec = |l: SmallIntLiteral| covalence_pure::$W::from_bits(l.bits() as _);
        match $op {
            $(FloatOp::$bin => {
                let (a, b) = small2($args, $tag)?;
                let r = pe::$BinRule
                    .eval(&(dec(a), dec(b)))
                    .ok_or(Error::NotReducible)?;
                Term::small_int(small_lit($tag, r.to_bits()))
            })+
            $(FloatOp::$un => {
                let a = small1($args, $tag)?;
                let r = pe::$UnRule.eval(&dec(a)).ok_or(Error::NotReducible)?;
                Term::small_int(small_lit($tag, r.to_bits()))
            })+
            $(FloatOp::$cmp => {
                let (a, b) = small2($args, $tag)?;
                Term::bool_lit(
                    pe::$CmpRule
                        .eval(&(dec(a), dec(b)))
                        .ok_or(Error::NotReducible)?,
                )
            })+
        }
    }};
}

/// The bit-level WASM float ops — see [`crate::rules::FloatCert`]. Keyed by
/// the canonical `defs::floats` registry ([`defs::lookup_float_op`], pointer
/// identity); computed by the trusted `covalence-pure-trusted::float`
/// [`CanonRule`](covalence_pure::CanonRule)s (bitwise sorts with the single
/// NaN-canonicalization point — the WASM deterministic profile, pinned
/// bit-for-bit against wasmtime by `covalence-pure-eval`'s
/// `tests/differential_float.rs`). Every float body is total on bit patterns,
/// so the only refusals here are shape refusals (wrong arity / literal tag).
pub(crate) fn float_bits(spec: &TermSpec, args: &[Lit]) -> Result<Term> {
    let key = defs::lookup_float_op(spec).ok_or(Error::NotReducible)?;
    let rhs = match key {
        FloatKey::Op(FloatWidth::F32, op) => float_op_arm!(F32, IntTag::U32, op, args;
        bin {
            Add => F32Add, Sub => F32Sub, Mul => F32Mul, Div => F32Div,
            Min => F32Min, Max => F32Max, Copysign => F32Copysign,
        }
        un {
            Sqrt => F32Sqrt, Abs => F32Abs, Neg => F32Neg, Ceil => F32Ceil,
            Floor => F32Floor, Trunc => F32Trunc, Nearest => F32Nearest,
        }
        cmp {
            Eq => F32Eq, Ne => F32Ne, Lt => F32Lt, Gt => F32Gt,
            Le => F32Le, Ge => F32Ge,
        }),
        FloatKey::Op(FloatWidth::F64, op) => float_op_arm!(F64, IntTag::U64, op, args;
        bin {
            Add => F64Add, Sub => F64Sub, Mul => F64Mul, Div => F64Div,
            Min => F64Min, Max => F64Max, Copysign => F64Copysign,
        }
        un {
            Sqrt => F64Sqrt, Abs => F64Abs, Neg => F64Neg, Ceil => F64Ceil,
            Floor => F64Floor, Trunc => F64Trunc, Nearest => F64Nearest,
        }
        cmp {
            Eq => F64Eq, Ne => F64Ne, Lt => F64Lt, Gt => F64Gt,
            Le => F64Le, Ge => F64Ge,
        }),
        FloatKey::Promote => {
            let a = small1(args, IntTag::U32)?;
            let r = pe::F64PromoteF32
                .eval(&covalence_pure::F32::from_bits(a.bits() as u32))
                .ok_or(Error::NotReducible)?;
            Term::small_int(small_lit(IntTag::U64, r.to_bits()))
        }
        FloatKey::Demote => {
            let a = small1(args, IntTag::U64)?;
            let r = pe::F32DemoteF64
                .eval(&covalence_pure::F64::from_bits(a.bits()))
                .ok_or(Error::NotReducible)?;
            Term::small_int(small_lit(IntTag::U32, r.to_bits()))
        }
        FloatKey::TruncSat(w, dst) => float_trunc_sat(w, dst, args)?,
        FloatKey::Convert(w, src) => float_convert(w, src, args)?,
    };
    eq_concl(spec, args, rhs)
}

/// WASM `trunc_sat` on bits: float bits at width `w` → the `dst` tag's value
/// (saturating; NaN → 0). Only the four WASM scalar int tags are registered
/// ([`defs::FLOAT_CVT_TAGS`]); anything else refuses defensively.
fn float_trunc_sat(w: FloatWidth, dst: IntTag, args: &[Lit]) -> Result<Term> {
    use covalence_pure::{F32, F64};
    let lit = match w {
        FloatWidth::F32 => {
            let v = F32::from_bits(small1(args, IntTag::U32)?.bits() as u32);
            match dst {
                IntTag::U32 => {
                    small_lit(dst, pe::U32TruncSatF32.eval(&v).ok_or(Error::NotReducible)?)
                }
                IntTag::U64 => {
                    small_lit(dst, pe::U64TruncSatF32.eval(&v).ok_or(Error::NotReducible)?)
                }
                IntTag::S32 => {
                    small_lit(dst, pe::I32TruncSatF32.eval(&v).ok_or(Error::NotReducible)?)
                }
                IntTag::S64 => {
                    small_lit(dst, pe::I64TruncSatF32.eval(&v).ok_or(Error::NotReducible)?)
                }
                _ => return Err(Error::NotReducible),
            }
        }
        FloatWidth::F64 => {
            let v = F64::from_bits(small1(args, IntTag::U64)?.bits());
            match dst {
                IntTag::U32 => {
                    small_lit(dst, pe::U32TruncSatF64.eval(&v).ok_or(Error::NotReducible)?)
                }
                IntTag::U64 => {
                    small_lit(dst, pe::U64TruncSatF64.eval(&v).ok_or(Error::NotReducible)?)
                }
                IntTag::S32 => {
                    small_lit(dst, pe::I32TruncSatF64.eval(&v).ok_or(Error::NotReducible)?)
                }
                IntTag::S64 => {
                    small_lit(dst, pe::I64TruncSatF64.eval(&v).ok_or(Error::NotReducible)?)
                }
                _ => return Err(Error::NotReducible),
            }
        }
    };
    Ok(Term::small_int(lit))
}

/// WASM `convert` on bits: the `src` tag's value → float bits at width `w`
/// (round-to-nearest-even; total, never NaN).
fn float_convert(w: FloatWidth, src: IntTag, args: &[Lit]) -> Result<Term> {
    let a = small1(args, src)?;
    let lit = match w {
        FloatWidth::F32 => {
            let r = match src {
                IntTag::U32 => pe::F32ConvertU32.eval(&(a.bits() as u32)),
                IntTag::U64 => pe::F32ConvertU64.eval(&a.bits()),
                IntTag::S32 => pe::F32ConvertI32.eval(&(a.bits() as i32)),
                IntTag::S64 => pe::F32ConvertI64.eval(&(a.bits() as i64)),
                _ => return Err(Error::NotReducible),
            };
            small_lit(IntTag::U32, r.ok_or(Error::NotReducible)?.to_bits())
        }
        FloatWidth::F64 => {
            let r = match src {
                IntTag::U32 => pe::F64ConvertU32.eval(&(a.bits() as u32)),
                IntTag::U64 => pe::F64ConvertU64.eval(&a.bits()),
                IntTag::S32 => pe::F64ConvertI32.eval(&(a.bits() as i32)),
                IntTag::S64 => pe::F64ConvertI64.eval(&(a.bits() as i64)),
                _ => return Err(Error::NotReducible),
            };
            small_lit(IntTag::U64, r.ok_or(Error::NotReducible)?.to_bits())
        }
    };
    Ok(Term::small_int(lit))
}
