//! The toHOL **symbolic-tier** driver (moved here from `covalence-core`'s
//! in-crate `proofs` module — the S4 first slice): a computation-backed
//! `IsThm` certificate whose numeral leaves are `toHOL` denotations, reified
//! through the admitted toHOL rules and transported with the base `eq_mp`,
//! landing as an [`EvalThm`] bit-for-bit equal to the fact the per-family cert
//! path mints. UNTRUSTED — composes gated mints only.
//!
//! This is the exemplar of the never-materialize pipeline (big values stay
//! symbolic; only the equations actually used ever exist). The bulk
//! reduction path in [`crate::reduce`] instead lands the per-family
//! certificates directly.

use covalence_pure::{CanonRule as _, Eqn, Expr, Thm as PThm, Val, apply, canon};
use covalence_pure_eval::{self as pe, NatAdd};
use covalence_types::{Bytes, Int, Nat};

use covalence_core::seam::{CoreProp, IsThm, Lit};
use covalence_core::{Ctx, Error, Result, Term, TermSpec, Type, defs};

use covalence_core::Thm;

use crate::defs::{
    bytes_cat, bytes_cat_spec, bytes_len, bytes_len_spec, int_add, int_add_spec, int_mul,
    int_mul_spec, int_neg, int_neg_spec,
};
use crate::lang::{CoreEval, EvalThm};
use crate::rules::{
    BytesCert, IntArithCert, NatAddCert, PairVal, ToHolBytesVal, ToHolIntVal, ToHolNatVal,
};
use crate::tohol_ops::{BytesCatEqE, BytesLenEqE, HolApp, HolAppE, IntBinEqE, IntUnEqE, NatAddEqE};

/// A pure theorem at the eval tier.
type PT<P> = PThm<CoreEval, P>;

/// A proven reification equation: `⊢ E = Val(t)` at the `Term` sort.
type Reified<E> = PT<Eqn<E, Val<Term>>>;

/// Lower a `covalence_pure` error into the core error type.
fn perr(e: covalence_pure::Error) -> Error {
    Error::Pure(format!("{e:?}"))
}

/// `⊢ nat.add ⌜a⌝ ⌜b⌝ = ⌜a + b⌝` as a kernel [`EvalThm`], computed **natively**
/// and landed through the toHOL seam — the end-to-end first slice, minting
/// the same conclusion as the legacy literal reduction of the application.
///
/// The pipeline (all steps gated or ungated-sound; none can forge):
/// 1. `NatAddCert` mints the symbolic-tier certificate
///    `⊢ IsThm(∅, ⌜nat.add (toHOL a) (toHOL b) = toHOL (a+b)⌝)`.
/// 2. `ToHolNatVal` (transitional) reifies each `toHOL` leaf to today's
///    literal-numeral `Term`, and `reify_app` pushes the equations up the
///    `HolApp` spine (`cong_pair` + `PairVal` + `cong_app` + `canon` +
///    `trans`) until the whole symbolic term expression equals a single
///    `Val<Term>`.
/// 3. The base `eq_mp` transports the `IsThm` proposition along the
///    reification equation (lifted through `cong_pair`/`cong_app(IsThm)`),
///    landing a genuine `CoreProp`.
/// 4. [`covalence_core::Thm::from_pure`] wraps it, re-running the sequent well-typedness
///    floor — indistinguishable from a rule-minted theorem.
pub fn nat_add_thm(a: Nat, b: Nat) -> Result<EvalThm> {
    // `NatAdd` is total (addition never refuses), so the `None` arm is
    // unreachable; refuse cleanly if it ever fires.
    let sum = NatAdd
        .eval(&(a.clone(), b.clone()))
        .ok_or_else(|| Error::Pure("nat.add: CanonRule refused a ground input".into()))?;

    // 1. The computation-backed certificate (symbolic tier).
    let cert = apply(CoreEval, NatAddCert, (a.clone(), b.clone())).map_err(perr)?;

    // 2. Reify the three toHOL leaves (transitional literal form) …
    let ta = apply(CoreEval, ToHolNatVal, a).map_err(perr)?;
    let tb = apply(CoreEval, ToHolNatVal, b).map_err(perr)?;
    let tc = apply(CoreEval, ToHolNatVal, sum).map_err(perr)?;

    // … and push them up the HolApp spine, innermost-first (the nesting must
    // mirror `tohol_ops::NatAddEqE` exactly for eq_mp's structural match).
    let add = PThm::refl(Val(defs::nat_add()), CoreEval);
    let lhs_partial = reify_app(add, ta)?; // ⊢ (nat.add (toHOL a)) = Val
    let lhs = reify_app(lhs_partial, tb)?; // ⊢ (nat.add (toHOL a) (toHOL b)) = Val
    let eq_op = PThm::refl(Val(Term::eq_op(Type::nat())), CoreEval);
    let eq_partial = reify_app(eq_op, lhs)?; // ⊢ ((=) lhs) = Val
    let full = reify_app(eq_partial, tc)?; // ⊢ E = Val(t_final)

    // 3. Transport IsThm(∅, E) along ⊢ E = Val(t_final), then wrap.
    let ctx = PThm::refl(Val(Ctx::new()), CoreEval);
    let pair = ctx.cong_pair(full).map_err(perr)?;
    let isthm_eq = pair.cong_app(IsThm);
    let landed = cert
        .eq_mp(isthm_eq)
        .ok_or_else(|| Error::Pure("eq_mp: reified lhs did not match the certificate".into()))?;
    EvalThm::from_pure(landed)
}

/// `⊢ nat.add (toHOL a) (toHOL b) = toHOL (a + b)` as a **symbolic** kernel
/// theorem — the literal-endgame proof-of-mechanism (design:
/// `notes/vibes/literal-endgame-design.md`, stage EG1). Unlike
/// [`nat_add_thm`], the `toHOL` numeral leaves are **never reified**: the three
/// naturals `a`, `b`, `a+b` stay as native [`Nat`] values under the
/// uninterpreted [`ToHolNat`](crate::tohol_ops::ToHolNat) op, so **no
/// succ-tower is ever built** — the theorem's conclusion is the base expression
/// [`NatAddEqE`], carried directly by [`Thm<CoreEval, NatAddEqE>`] with zero
/// base-TCB machinery.
///
/// The pipeline is a single step: mint the already-admitted, already-sound
/// [`NatAddCert`] (which derives the whole well-typed symbolic sequent from the
/// input pair, computing the sum natively via
/// [`covalence_pure_eval::NatAdd`]), then land it via
/// [`Thm::from_pure_sym`] — **no** `ToHolNatVal`, **no** `reify_app`, **no**
/// `eq_mp` reification. Soundness rests on `admits()` alone (`NatAddCert` is
/// the sole, sound mint; see its docstring and `Thm::from_pure_sym`'s).
///
/// The never-materialize guarantee is machine-checked by
/// `tests/nat_add_symbolic.rs::nat_add_symbolic_never_materializes`.
pub fn nat_add_thm_symbolic(a: Nat, b: Nat) -> Result<Thm<CoreEval, NatAddEqE>> {
    let cert = apply(CoreEval, NatAddCert, (a, b)).map_err(perr)?;
    Ok(Thm::from_pure_sym(cert))
}

// ===========================================================================
// The int / bytes symbolic landers (stage EG2 —
// `notes/vibes/literal-endgame-design.md`).
//
// KEY ASYMMETRY WITH NAT: `NatAddCert` already concludes the *symbolic*
// `NatAddEqE`, so `nat_add_thm_symbolic` is a one-step mint-and-land. The
// int/bytes family certificates (`IntArithCert`/`BytesCert`) instead conclude
// the *concrete* `CoreProp` (`Val<Term>` with kernel-literal leaves). So these
// landers mint the existing sound family certificate, then **transport** it
// backwards along a proven `⊢ symbolicE = Val(concrete)` reification equation
// (built with the existing `ToHol*Val` reify rules + `reify_app`, then flipped
// with `sym`), landing a `Thm<CoreEval, symbolicE>` whose `toHOL` leaves stay
// native. This adds **zero** new admitted rules and **zero** base machinery
// (design B1): the transport is the existing base `eq_mp`/`cong`/`sym`
// calculus, exactly as for `nat_add_thm`.
//
// FLOAT IS BLOCKED (recorded in SKELETONS + the design doc): `FloatCert`
// concludes concrete `CoreProp` too, but there is **no** `ToHolF32Val` /
// `ToHolF64Val` reify rule admitted (only `ToHolNatVal`/`ToHolIntVal`/
// `ToHolBytesVal` exist), so the backward transport cannot relate a
// `ToHolF32`/`ToHolF64` leaf to the certificate's `small_int` operand without
// adding a new admitted rule — out of scope for EG2's zero-new-rule contract.
// ===========================================================================

/// Transport a concrete family certificate `⊢ IsThm(∅, Val(concrete))` onto a
/// symbolic conclusion, given the proven reification equation
/// `full : ⊢ symbolicE = Val(concrete)` — the shared tail of every int/bytes
/// symbolic lander.
///
/// Lifts `full` to `⊢ IsThm(∅, symbolicE) = IsThm(∅, Val(concrete))`
/// (`cong_pair` under the empty context + `cong_app(IsThm)`), flips it with
/// `sym`, and transports the certificate along it with the base `eq_mp` —
/// landing `⊢ IsThm(∅, symbolicE)` via [`Thm::from_pure_sym`] **without ever
/// reifying** the symbolic operand. The `eq_mp` structural match confirms the
/// certificate's concrete operand is exactly the `Val(concrete)` the reify
/// chain produced (an ill-matched reification refuses cleanly, never mints).
fn transport_symbolic<E>(
    cert: PT<CoreProp>,
    full: PT<Eqn<E, Val<Term>>>,
) -> Result<Thm<CoreEval, E>>
where
    E: Expr<Ty = Term>,
{
    let ctx = PThm::refl(Val(Ctx::new()), CoreEval);
    let pair = ctx.cong_pair(full).map_err(perr)?; // ⊢ (∅, E) = (∅, Val)
    let isthm_eq = pair.cong_app(IsThm); // ⊢ IsThm(∅, E) = IsThm(∅, Val)
    let landed = cert.eq_mp(isthm_eq.sym()).ok_or_else(|| {
        Error::Pure("eq_mp: the reified concrete term did not match the certificate".into())
    })?;
    Ok(Thm::from_pure_sym(landed))
}

/// `⊢ int.add ⌜a⌝ ⌜b⌝ = ⌜a + b⌝` as a floored kernel [`EvalThm`] — the
/// concrete `int.add` computation lander (mints [`IntArithCert`], lands via
/// [`Thm::from_pure`], re-running the well-typedness floor). The integer
/// literals are native single-node leaves (O(1)); this is the **self-floor
/// witness** for [`int_add_thm_symbolic`] and the general concrete int lander.
pub fn int_arith_thm(spec: TermSpec, args: Vec<Lit>) -> Result<EvalThm> {
    let cert = apply(CoreEval, IntArithCert, (spec, args)).map_err(perr)?;
    EvalThm::from_pure(cert)
}

/// `⊢ bytes.op ⌜args⌝ = ⌜result⌝` as a floored kernel [`EvalThm`] — the
/// concrete `bytes.*` computation lander (mints [`BytesCert`], lands via
/// [`Thm::from_pure`]). A bytestring argument/result is a native single-node
/// blob leaf (O(1), never a `cons`-tower); this is the self-floor witness for
/// the `bytes.*` symbolic landers.
pub fn bytes_thm(spec: TermSpec, args: Vec<Lit>) -> Result<EvalThm> {
    let cert = apply(CoreEval, BytesCert, (spec, args)).map_err(perr)?;
    EvalThm::from_pure(cert)
}

/// `⊢ int.add (toHOL a) (toHOL b) = toHOL (a + b)` as a **symbolic** kernel
/// theorem (stage EG2) — the `int` analogue of [`nat_add_thm_symbolic`]. The
/// two integers and their sum stay native [`Int`] values under the
/// uninterpreted [`ToHolInt`](crate::tohol_ops::ToHolInt) op; no kernel
/// integer literal is materialized in the landed conclusion.
///
/// Mints the existing sound [`IntArithCert`] (concrete), then transports it
/// onto [`IntBinEqE`] via `transport_symbolic` — **no new admitted rule**.
/// Self-floor witness: [`int_arith_thm`] with the same input.
pub fn int_add_thm_symbolic(a: Int, b: Int) -> Result<Thm<CoreEval, IntBinEqE>> {
    let sum = pe::IntAdd
        .eval(&(a.clone(), b.clone()))
        .ok_or_else(|| Error::Pure("int.add: CanonRule refused a ground input".into()))?;
    let cert = apply(
        CoreEval,
        IntArithCert,
        (
            int_add_spec(),
            vec![Lit::Int(a.clone()), Lit::Int(b.clone())],
        ),
    )
    .map_err(perr)?;
    let full = int_bin_reify(int_add(), a, b, sum)?;
    transport_symbolic(cert, full)
}

/// `⊢ int.mul (toHOL a) (toHOL b) = toHOL (a * b)` — the `int.mul` symbolic
/// lander (see [`int_add_thm_symbolic`]; same [`IntBinEqE`] shape, distinct
/// value). Self-floor witness: [`int_arith_thm`].
pub fn int_mul_thm_symbolic(a: Int, b: Int) -> Result<Thm<CoreEval, IntBinEqE>> {
    let prod = pe::IntMul
        .eval(&(a.clone(), b.clone()))
        .ok_or_else(|| Error::Pure("int.mul: CanonRule refused a ground input".into()))?;
    let cert = apply(
        CoreEval,
        IntArithCert,
        (
            int_mul_spec(),
            vec![Lit::Int(a.clone()), Lit::Int(b.clone())],
        ),
    )
    .map_err(perr)?;
    let full = int_bin_reify(int_mul(), a, b, prod)?;
    transport_symbolic(cert, full)
}

/// `⊢ int.neg (toHOL a) = toHOL (-a)` — the unary `int.neg` symbolic lander
/// ([`IntUnEqE`] shape). Self-floor witness: [`int_arith_thm`].
pub fn int_neg_thm_symbolic(a: Int) -> Result<Thm<CoreEval, IntUnEqE>> {
    let neg = pe::IntNeg
        .eval(&a)
        .ok_or_else(|| Error::Pure("int.neg: CanonRule refused a ground input".into()))?;
    let cert = apply(
        CoreEval,
        IntArithCert,
        (int_neg_spec(), vec![Lit::Int(a.clone())]),
    )
    .map_err(perr)?;
    // int.neg (toHOL a) = toHOL (-a), eq at `int`.
    let neg_op = PThm::refl(Val(int_neg()), CoreEval);
    let ta = apply(CoreEval, ToHolIntVal, a).map_err(perr)?;
    let lhs = reify_app(neg_op, ta)?; // ⊢ int.neg (toHOL a) = Val
    let eq_op = PThm::refl(Val(Term::eq_op(Type::int())), CoreEval);
    let eq_partial = reify_app(eq_op, lhs)?;
    let tc = apply(CoreEval, ToHolIntVal, neg).map_err(perr)?;
    let full = reify_app(eq_partial, tc)?; // ⊢ IntUnEqE = Val(final)
    transport_symbolic(cert, full)
}

/// `⊢ bytes.cat (toHOL a) (toHOL b) = toHOL (a ++ b)` as a **symbolic** kernel
/// theorem (stage EG2). The two bytestrings and their concatenation stay
/// native [`Bytes`] leaves under the uninterpreted
/// [`ToHolBytes`](crate::tohol_ops::ToHolBytes) op — a megabyte operand is a
/// single native leaf, **never** a `cons`-tower (the binary-substrate payoff).
/// Self-floor witness: [`bytes_thm`].
pub fn bytes_cat_thm_symbolic(a: Bytes, b: Bytes) -> Result<Thm<CoreEval, BytesCatEqE>> {
    let cat = pe::BytesCat
        .eval(&(a.clone(), b.clone()))
        .ok_or_else(|| Error::Pure("bytes.cat: CanonRule refused a ground input".into()))?;
    let cert = apply(
        CoreEval,
        BytesCert,
        (
            bytes_cat_spec(),
            vec![Lit::Bytes(a.clone()), Lit::Bytes(b.clone())],
        ),
    )
    .map_err(perr)?;
    // bytes.cat (toHOL a) (toHOL b) = toHOL (cat), eq at `bytes`.
    let cat_op = PThm::refl(Val(bytes_cat()), CoreEval);
    let ta = apply(CoreEval, ToHolBytesVal, a).map_err(perr)?;
    let tb = apply(CoreEval, ToHolBytesVal, b).map_err(perr)?;
    let lhs = reify_app(reify_app(cat_op, ta)?, tb)?;
    let eq_op = PThm::refl(Val(Term::eq_op(Type::bytes())), CoreEval);
    let eq_partial = reify_app(eq_op, lhs)?;
    let tc = apply(CoreEval, ToHolBytesVal, cat).map_err(perr)?;
    let full = reify_app(eq_partial, tc)?; // ⊢ BytesCatEqE = Val(final)
    transport_symbolic(cert, full)
}

/// `⊢ bytes.len (toHOL bs) = toHOL (len bs)` — the `bytes.len` symbolic lander
/// (stage EG2), a **mixed-sort** shape ([`BytesLenEqE`]): a `ToHolBytes`
/// operand and a `ToHolNat` result. A megabyte operand stays a native
/// [`Bytes`] leaf. Self-floor witness: [`bytes_thm`].
pub fn bytes_len_thm_symbolic(bs: Bytes) -> Result<Thm<CoreEval, BytesLenEqE>> {
    let len = pe::BytesLen
        .eval(&bs)
        .ok_or_else(|| Error::Pure("bytes.len: CanonRule refused a ground input".into()))?;
    let cert = apply(
        CoreEval,
        BytesCert,
        (bytes_len_spec(), vec![Lit::Bytes(bs.clone())]),
    )
    .map_err(perr)?;
    // bytes.len (toHOL bs) = toHOL (len), eq at `nat` (the result sort).
    let len_op = PThm::refl(Val(bytes_len()), CoreEval);
    let tbs = apply(CoreEval, ToHolBytesVal, bs).map_err(perr)?;
    let lhs = reify_app(len_op, tbs)?; // ⊢ bytes.len (toHOL bs) = Val
    let eq_op = PThm::refl(Val(Term::eq_op(Type::nat())), CoreEval);
    let eq_partial = reify_app(eq_op, lhs)?;
    let tc = apply(CoreEval, ToHolNatVal, len).map_err(perr)?;
    let full = reify_app(eq_partial, tc)?; // ⊢ BytesLenEqE = Val(final)
    transport_symbolic(cert, full)
}

/// Build the reification equation `⊢ int.op (toHOL a) (toHOL b) = toHOL r`
/// `= Val(concrete)` for a **binary** `int` op whose head term is `op`, eq at
/// the `int` sort — the shared reify chain of the binary int symbolic landers.
fn int_bin_reify(op: Term, a: Int, b: Int, r: Int) -> Result<PT<Eqn<IntBinEqE, Val<Term>>>> {
    let op = PThm::refl(Val(op), CoreEval);
    let ta = apply(CoreEval, ToHolIntVal, a).map_err(perr)?;
    let tb = apply(CoreEval, ToHolIntVal, b).map_err(perr)?;
    let lhs = reify_app(reify_app(op, ta)?, tb)?; // ⊢ int.op (toHOL a) (toHOL b) = Val
    let eq_op = PThm::refl(Val(Term::eq_op(Type::int())), CoreEval);
    let eq_partial = reify_app(eq_op, lhs)?;
    let tc = apply(CoreEval, ToHolIntVal, r).map_err(perr)?;
    reify_app(eq_partial, tc)
}

/// Reify one symbolic HOL application node: given `⊢ F = Val(f)` and
/// `⊢ X = Val(x)`, derive `⊢ HolApp(F, X) = Val(f x)`.
///
/// Steps: `cong_pair` (⊢ `(F, X) = (Val f, Val x)`), the admitted `PairVal`
/// fusion (⊢ `(Val f, Val x) = Val((f, x))`), `trans`, congruence under
/// `HolApp`, then the admitted `canon(HolApp)` evaluation
/// (⊢ `HolApp(Val((f, x))) = Val(f x)`) and a final `trans`.
fn reify_app<F, X>(f: Reified<F>, x: Reified<X>) -> Result<Reified<HolAppE<F, X>>>
where
    F: Expr<Ty = Term>,
    X: Expr<Ty = Term>,
{
    let fv = f.rhs().0.clone();
    let xv = x.rhs().0.clone();
    let pair = f.cong_pair(x).map_err(perr)?;
    let fused = apply(CoreEval, PairVal, (fv.clone(), xv.clone())).map_err(perr)?;
    let ground = pair.trans(fused).map_err(perr)?;
    let under_app = ground.cong_app(HolApp);
    let evaled = canon(HolApp, (fv, xv), CoreEval).map_err(perr)?;
    under_app.trans(evaled).map_err(perr)
}
