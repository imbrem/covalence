//! The `toHOL` denotation ops: HOL terms as a **base sort** (`covalence-pure`
//! expressions of sort [`Term`]), with native values entering under
//! uninterpreted `toHOL` leaves.
//!
//! The maintainer's key move (notes/vibes/pure-hol-and-build-plan.md): the
//! canonical HOL term for a native value is **never materialized**. `toHOL n`
//! *denotes* the numeral `S(S(…(Z)…))` without building it; a megabyte
//! bytestring under [`ToHolBytes`] denotes its `cons`-tower for free. The HOL
//! term formers ([`HolApp`], …) are base ops on the `Term` sort too, so
//! partially-symbolic terms like `S (toHOL 4)` are ordinary base expressions.
//!
//! Trust story:
//! - [`ToHolNat`] / [`ToHolInt`] / [`ToHolBytes`] are **uninterpreted** ops
//!   (no [`CanonRule`]): writing `App<ToHolNat, _>` is inert and always sound.
//!   Their *meaning* is pinned only by admitted rules — the unfolding-equation
//!   and certificate rules in `crate::rules` (`ToHolNatVal`, `NatAddCert`, …).
//! - [`HolApp`] is an [`Op`] **and** a [`CanonRule`] whose `eval` is the raw,
//!   untyped [`Term::app`]. Reducing it via [`covalence_pure::canon`] is gated
//!   on its `TypeId` being admitted; `CoreEval` admits it (it is enumerated in
//!   `EVAL_MANIFEST`). Soundness: `App<HolApp, Val((f, x))> = Val(f x)` holds
//!   by literal denotation — `HolApp` *means* HOL application, and the
//!   equation's two sides are the same term value by construction.

use covalence_pure::{App, CanonRule, F32, F64, Op, Val};
use covalence_types::{Bytes, Int, Nat};

use covalence_core::Term;

/// `toHOL : Nat → Term` — the uninterpreted denotation of a native natural as
/// its canonical HOL numeral. Never evaluated (no [`CanonRule`]); its defining
/// properties arrive only as admitted rules.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolNat;

impl Op for ToHolNat {
    type In = Nat;
    type Out = Term;
}

/// `toHOL : Int → Term` — uninterpreted (see [`ToHolNat`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolInt;

impl Op for ToHolInt {
    type In = Int;
    type Out = Term;
}

/// `toHOL : Bytes → Term` — uninterpreted (see [`ToHolNat`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolBytes;

impl Op for ToHolBytes {
    type In = Bytes;
    type Out = Term;
}

/// `toHOL : F32 → Term` — the uninterpreted denotation of a native `f32`
/// bit-pattern (the base [`F32`] sort: raw bits, bitwise `Eq`, WASM
/// deterministic profile) as its canonical HOL term. Never evaluated (no
/// [`CanonRule`]); like [`ToHolNat`], its defining properties arrive only as
/// admitted rules. Under the F2b bit-level layer the denoted term is the
/// `u32` bit-pattern literal (`f32 := u32`); the typed layer (F2c) wraps it
/// with the newtype coercion.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolF32;

impl Op for ToHolF32 {
    type In = F32;
    type Out = Term;
}

/// `toHOL : F64 → Term` — uninterpreted (see [`ToHolF32`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct ToHolF64;

impl Op for ToHolF64 {
    type In = F64;
    type Out = Term;
}

/// HOL application as a base op on the `Term` sort: `(f, x) ↦ f x`.
///
/// The [`CanonRule`] eval is the **raw, untyped** [`Term::app`] — no type
/// check, exactly the constructor. Sound by literal denotation: on ground
/// `Val` arguments the minted equation's right-hand side *is* the application
/// node the left-hand side denotes. (An ill-typed application is a perfectly
/// good `Term` value; it simply never type-checks into an `IsThm` sequent.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct HolApp;

impl Op for HolApp {
    type In = (Term, Term);
    type Out = Term;
}

impl CanonRule for HolApp {
    fn eval(&self, (f, x): &Self::In) -> Option<Term> {
        Some(Term::app(f.clone(), x.clone()))
    }
}

// ---------------------------------------------------------------------------
// Expression-shape aliases for the nat.add slice (used by the `NatAddCert`
// rule's conclusion type and by the reification driver, which must agree on
// the exact nesting so `eq_mp`'s structural match succeeds).
// ---------------------------------------------------------------------------

/// A `toHOL`-denoted natural: `App<ToHolNat, Val<Nat>>`.
pub type ToHolNatE = App<ToHolNat, Val<Nat>>;

/// A `toHOL`-denoted integer: `App<ToHolInt, Val<Int>>`.
pub type ToHolIntE = App<ToHolInt, Val<Int>>;

/// A `toHOL`-denoted bytestring: `App<ToHolBytes, Val<Bytes>>`.
pub type ToHolBytesE = App<ToHolBytes, Val<Bytes>>;

/// A `toHOL`-denoted `f32` bit-pattern: `App<ToHolF32, Val<F32>>`.
pub type ToHolF32E = App<ToHolF32, Val<F32>>;

/// A `toHOL`-denoted `f64` bit-pattern: `App<ToHolF64, Val<F64>>`.
pub type ToHolF64E = App<ToHolF64, Val<F64>>;

/// A symbolic HOL application `f x` at the base layer.
pub type HolAppE<F, X> = App<HolApp, (F, X)>;

/// The symbolic HOL term `nat.add (toHOL a) (toHOL b)` (the `Val<Term>` leaf
/// is the `covalence_core::defs::nat_add` constant).
pub type NatAddLhsE = HolAppE<HolAppE<Val<Term>, ToHolNatE>, ToHolNatE>;

/// The symbolic HOL equation `nat.add (toHOL a) (toHOL b) = toHOL (a + b)`
/// (the outer `Val<Term>` leaf is HOL `=` at `nat`).
pub type NatAddEqE = HolAppE<HolAppE<Val<Term>, NatAddLhsE>, ToHolNatE>;

// ---------------------------------------------------------------------------
// Symbolic-conclusion shapes for the int / bytes landers (stage EG2 —
// `notes/vibes/literal-endgame-design.md`). Each mirrors `NatAddEqE`: a HOL
// equation `op (toHOL …) = toHOL result`, with the operands and result held as
// native `Int`/`Bytes`/`Nat` leaves under the uninterpreted `ToHol*` ops, so a
// megabyte bytestring stays a native leaf and never a `cons`-tower. Unlike
// `NatAddCert`, the int/bytes family certificates conclude the *concrete*
// `CoreProp`; the symbolic landers in `crate::tohol` transport that concrete
// certificate onto these shapes with the existing `ToHol*Val` reify rules +
// base `eq_mp` (no new admitted rule) — see `int_add_thm_symbolic` & co.
// ---------------------------------------------------------------------------

/// A **binary** `int` op applied to two `toHOL` integers:
/// `int.op (toHOL a) (toHOL b)`.
pub type IntBinLhsE = HolAppE<HolAppE<Val<Term>, ToHolIntE>, ToHolIntE>;

/// The symbolic HOL equation `int.op (toHOL a) (toHOL b) = toHOL (op a b)` at
/// the `int` sort (shared by `int.add` / `int.mul` — same shape, distinct
/// values).
pub type IntBinEqE = HolAppE<HolAppE<Val<Term>, IntBinLhsE>, ToHolIntE>;

/// A **unary** `int` op applied to one `toHOL` integer: `int.op (toHOL a)`.
pub type IntUnLhsE = HolAppE<Val<Term>, ToHolIntE>;

/// The symbolic HOL equation `int.op (toHOL a) = toHOL (op a)` at the `int`
/// sort (`int.neg`).
pub type IntUnEqE = HolAppE<HolAppE<Val<Term>, IntUnLhsE>, ToHolIntE>;

/// A **binary** bit-level `f32` op applied to two `toHOL` floats:
/// `f32.opBits (toHOL a) (toHOL b)`.
pub type F32BinLhsE = HolAppE<HolAppE<Val<Term>, ToHolF32E>, ToHolF32E>;

/// The symbolic HOL equation `f32.opBits (toHOL a) (toHOL b) = toHOL (op a b)`
/// at the `u32` bit sort (shared by `f32.addBits` / `f32.mulBits` — same
/// shape, distinct values; the operands and result stay native `F32`
/// bit-patterns under the uninterpreted `ToHolF32` op).
pub type F32BinEqE = HolAppE<HolAppE<Val<Term>, F32BinLhsE>, ToHolF32E>;

/// A **binary** bit-level `f64` op applied to two `toHOL` floats:
/// `f64.opBits (toHOL a) (toHOL b)`.
pub type F64BinLhsE = HolAppE<HolAppE<Val<Term>, ToHolF64E>, ToHolF64E>;

/// The symbolic HOL equation `f64.opBits (toHOL a) (toHOL b) = toHOL (op a b)`
/// at the `u64` bit sort (see [`F32BinEqE`]; native `F64` bit-patterns under
/// `ToHolF64`).
pub type F64BinEqE = HolAppE<HolAppE<Val<Term>, F64BinLhsE>, ToHolF64E>;

/// `bytes.cat (toHOL a) (toHOL b)` — a binary `bytes` op on two `toHOL`
/// bytestrings.
pub type BytesCatLhsE = HolAppE<HolAppE<Val<Term>, ToHolBytesE>, ToHolBytesE>;

/// The symbolic HOL equation `bytes.cat (toHOL a) (toHOL b) = toHOL (cat a b)`
/// at the `bytes` sort — the megabyte operands and result stay native `Bytes`
/// leaves under `ToHolBytes`.
pub type BytesCatEqE = HolAppE<HolAppE<Val<Term>, BytesCatLhsE>, ToHolBytesE>;

/// `bytes.len (toHOL bs)` — a `bytes → nat` op on a `toHOL` bytestring.
pub type BytesLenLhsE = HolAppE<Val<Term>, ToHolBytesE>;

/// The symbolic HOL equation `bytes.len (toHOL bs) = toHOL (len bs)` at the
/// `nat` sort — mixed toHOL sorts: a `ToHolBytes` operand and a `ToHolNat`
/// result.
pub type BytesLenEqE = HolAppE<HolAppE<Val<Term>, BytesLenLhsE>, ToHolNatE>;

/// Build the [`NatAddEqE`] expression for concrete `a`, `b`, `sum` — shared by
/// `NatAddCert::decide` and (implicitly, node by node) the reification driver.
pub(crate) fn nat_add_eq_expr(a: Nat, b: Nat, sum: Nat) -> NatAddEqE {
    let add = Val(crate::defs::nat_add());
    let eq = Val(Term::eq_op(covalence_core::Type::nat()));
    let lhs = App(
        HolApp,
        (
            App(HolApp, (add, App(ToHolNat, Val(a)))),
            App(ToHolNat, Val(b)),
        ),
    );
    App(HolApp, (App(HolApp, (eq, lhs)), App(ToHolNat, Val(sum))))
}
