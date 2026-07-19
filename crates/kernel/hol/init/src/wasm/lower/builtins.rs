//! **Exact numeric/representation builtin clauses** — supplementary `fn.*`
//! clauses for WASM integer numerics and structural floating-point
//! representation, the biggest fireability unlock of the Dec leg.
//!
//! ## Why these clauses exist (what the spec clauses can't fire)
//!
//! The bundled dump *does* define most integer ops equationally, but their
//! canonical lowerings are blocked in three distinct ways (measured on the
//! combined set):
//!
//! - `isub_`/`signed_`/`inv_signed_`/`sat_*` bodies route through `Cvt`
//!   (`nat↔int↔rat`) spines — their graph conclusions are **value-dead
//!   operator spines**, never value encodings, so downstream consumers
//!   (`fn.binop_`'s SUB clause, comparisons' signed legs) can only bind junk;
//! - `ieq_`/`ine_`/`ilt_`/`igt_`/`ile_`/`ige_`/`ieqz_` conclude
//!   `$bool(cmp …)` — a `fn.bool` premise applied to a coarse `cmp.*` spine
//!   that never matches `bool.true`/`bool.false`, so the premise is
//!   underivable at every point;
//! - `ishl_`/`ishr_`/`irotl_`/`irotr_`/`iclz_`/`ictz_`/`ipopcnt_` (and
//!   `idiv_`/`irem_`'s `truncz`) are **zero-clause builtins** — no equations
//!   in the spec at all.
//!
//! This module gives the integer family *defining clauses with computable
//! `Side` antecedents* — pure real-nat arithmetic over the two's-complement
//! carrier — emitted per **width** (8/16/32/64 — the widths reachable from
//! corpus call sites: `sizenn` yields 32/64 for scalars, `lsizenn` adds 8/16
//! for SIMD lanes; `idiv_`/`irem_` are scalar-only, 32/64). Zero axioms: every
//! antecedent is kernel-computed at each ground instance, so the kernel
//! re-checks the arithmetic itself each time a clause fires. It also defines
//! the two inverse sequence builtins through ordinary recursive `Judgement`
//! premises over the exact reified `st$app` list spine. Those clauses introduce
//! no axiom either: every recursive step is replayed through the same combined
//! `RuleSet`.
//!
//! ## Faithfulness (definitional, not axiomatic)
//!
//! Values of `iN(N)` encode as `case.%(tup(num.nat n))` with `0 ≤ n < 2^N` —
//! the **unsigned carrier**; the signed reading is the two's-complement
//! interpretation `signed_N(n) = n − 2^N·[n ≥ 2^(N−1)]` (spec §4.3.2,
//! `signed`). Per clause, the `Side` antecedents implement the spec
//! definition exactly:
//!
//! - `isub_`: `r = (a + 2^N − b) mod 2^N` — wraparound mod `2^N` (spec
//!   `isub`); `iadd_`/`imul_` need no clauses here (their spec lowerings
//!   already fire — pure nat `add`/`mul`/`mod`/`pow`).
//! - comparisons (`ilt_`/`igt_`/`ile_`/`ige_` with `sx`, and `ieq_`/`ine_`/
//!   `ieqz_`): result `u32` is `%(1)`/`%(0)`; two clauses per op (true/false
//!   outcome), each guarded by the comparison or its complement
//!   (`¬(a < b) ⟺ b ≤ a` over nat). The **signed** order is taken through
//!   the sign-bias isomorphism `biased(x) = (x + 2^(N−1)) mod 2^N`, which is
//!   the order-embedding of two's-complement `signed_N` into unsigned nat
//!   order (nonneg `x < 2^(N−1)` ↦ `x + 2^(N−1)`, neg `x ≥ 2^(N−1)` ↦
//!   `x − 2^(N−1)`; checked against Rust's `i8`/`i32` signed order by the
//!   oracle test). We *audited* building on the `signed_`/`inv_signed_` Dec
//!   graphs instead (the task's preferred route): their spec clauses conclude
//!   `cvt` spines and carry `cond.cmp-nonnat` opaque premises, so they
//!   provide no derivable value equations to build on — the bias trick stays
//!   entirely in the nat fragment.
//! - shifts/rotates (`k` is the `u32` shift count, `k' = k mod N` — spec
//!   takes the count modulo the width): `ishl_`: `r = (a·2^k') mod 2^N`;
//!   `ishr_` U: `r = a div 2^k'` (zero-filling); `ishr_` S: sign split —
//!   nonneg `r = a div 2^k'`, neg `r = a div 2^k' + (2^N − 2^(N−k'))`
//!   (sign-replicating: `⌊(a − 2^N)/2^k'⌋ = a div 2^k' − 2^(N−k')`, then
//!   `inv_signed` adds `2^N`); `irotl_`: `r = (a·2^k') mod 2^N + a div
//!   2^(N−k')`; `irotr_`: `r = a div 2^k' + (a mod 2^k')·2^(N−k')` (the two
//!   summands occupy disjoint bit ranges, so `+` is exact `|`).
//! - `iclz_`/`ictz_`: `0 ↦ N` (ground clause); nonzero `a`: `iclz_` pins `r`
//!   by `2^(N−1−r) ≤ a < 2^(N−r)` (i.e. `r = N − 1 − ⌊log₂ a⌋`), `ictz_` by
//!   `a mod 2^r = 0 ∧ a mod 2^(r+1) ≠ 0`. Both systems have exactly one
//!   solution `r` per real `a` and refuse every other `r` (including junk
//!   `r ≥ N`, which contradicts the bounds). `ipopcnt_` is the sum of the
//!   separately pinned structural bits.
//! - `truncz`/`ceilz`: exact on the structural rational fragment produced by
//!   natural-to-rational conversion and division.  For `n/d`, `d > 0`,
//!   truncation is `n div d` and ceiling is `(n + d - 1) div d`; unary-minus
//!   inputs split at `n < d` so zero remains canonically non-negative and
//!   nonzero results carry the encoded negative sign.  Opaque rational
//!   literals and other expression shapes deliberately receive no clause.
//! - `idiv_`/`irem_` (**partial**, option results like the Dec leg's eps
//!   legs: `opt.none` / `opt.some(%(r))`): division-by-zero keeps the spec's
//!   own ground `i_2 = %(0) ↦ eps` clauses (they already fire); every clause
//!   here carries a `0 < b` guard so it never overlaps them. Unsigned:
//!   `r = a div b` / `r = a mod b` (nat `div`/`mod` = truncation toward zero
//!   on nonnegatives). Signed: per sign-class clauses over magnitudes
//!   (`mag(x) = x` if `x < 2^(N−1)` else `2^N − x`): quotient magnitude
//!   `q = mag(a) div mag(b)`, negated (`(2^N − q) mod 2^N` — the `mod`
//!   maps `q = 0` to `0`) when signs differ; remainder magnitude
//!   `mag(a) mod mag(b)` with the **dividend's** sign (spec: `irem` sign
//!   follows `i_1`). The signed-overflow point `idiv_s(INT_MIN, −1)`
//!   (`q = 2^(N−1)`, unrepresentable) gets an explicit `↦ opt.none` clause;
//!   the normal same-sign-negative clause carries the complementary
//!   `q < 2^(N−1)` guard.
//! - float representation: SpecTec's explicit sign, normal/subnormal,
//!   significand, and exponent constructors map to the IEEE payload by exact
//!   natural arithmetic. Bits and bytes are least-significant first, hence
//!   bytes are WebAssembly's required little-endian encoding. The same raw
//!   payload proves typed byte serialization, reinterpretation, `fabs_`, and
//!   `fneg_`. Finite values, infinities, and exact NaN payloads are covered;
//!   malformed structural values deliberately remain underivable.
//!
//! Every clause also carries carrier guards (`a < 2^N`, `b < 2^N`, sign-class
//! bounds) — antecedents at least as strong as the SpecTec semantics (the
//! spec assumes well-typed `iN` inputs; we *check* them), so the graph
//! under-approximates the true function everywhere, junk points included.
//! Clause order is irrelevant for this family: unlike the Dec leg's
//! order-complement machinery, these clauses are pairwise disjoint by their
//! guards *and* each is independently faithful to the total function, so no
//! `dec.order` complement is needed.
//!
//! The cross-check against an independent oracle (Rust's wrapping/two's
//! complement arithmetic: `wrapping_add`/`wrapping_sub`, `i8`/`i32` casts,
//! `rotate_left`, `leading_zeros`, …) lives in this module's tests: each op
//! is asserted to fire **exactly** at the oracle's result and to refuse
//! every perturbed result (`r ± 1`).

use covalence_core::{Result, Term};
use covalence_hol_eval::mk_nat;

use super::super::encode::{app, con, metavar};
use super::evalrel::{wrap_int, wrap_nat};
use super::{Clause, LowerPrem, fn_graph};
use crate::init::ext::TermExt;
use crate::init::nat;

/// Widths reachable by the whole integer family (scalar `sizenn`: 32/64;
/// SIMD `lsizenn`: 8/16 as well).
pub const WIDTHS: [u64; 4] = [8, 16, 32, 64];
/// Widths used by integer bit/byte serialization. `128` is required by the
/// real `v128.const` binary/text paths, which call `inv_ibytes_(128, …)`.
pub const SERIALIZATION_WIDTHS: [u64; 5] = [8, 16, 32, 64, 128];
/// Widths for the scalar-only partial ops `idiv_` / `irem_`.
pub const DIV_WIDTHS: [u64; 2] = [32, 64];

/// Operations given defining clauses by this leg.
pub const OPS: [&str; 85] = [
    "truncz",
    "ceilz",
    "isub_",
    "ieq_",
    "ine_",
    "ilt_",
    "igt_",
    "ile_",
    "ige_",
    "ieqz_",
    "ishl_",
    "ishr_",
    "irotl_",
    "irotr_",
    "iclz_",
    "ictz_",
    "idiv_",
    "irem_",
    "inot_",
    "irev_",
    "iand_",
    "iandnot_",
    "ior_",
    "ixor_",
    "ipopcnt_",
    "ibitselect_",
    "ibits_",
    "inv_ibits_",
    "ibytes_",
    "inv_ibytes_",
    "lanes_",
    "inv_lanes_",
    "wrap__",
    "extend__",
    "iextend_",
    "narrow__",
    "iavgr_",
    "iq15mulr_sat_",
    "nbytes_",
    "inv_nbytes_",
    "vbytes_",
    "inv_vbytes_",
    "zbytes_",
    "inv_zbytes_",
    "cbytes_",
    "inv_cbytes_",
    "inv_concat_",
    "inv_concatn_",
    "fbits_",
    "inv_fbits_",
    "fbytes_",
    "inv_fbytes_",
    "reinterpret__",
    "fabs_",
    "fneg_",
    "fcopysign_",
    "feq_",
    "fne_",
    "flt_",
    "fgt_",
    "fle_",
    "fge_",
    "fpmin_",
    "fpmax_",
    "fmin_",
    "fmax_",
    "fceil_",
    "ffloor_",
    "ftrunc_",
    "fnearest_",
    "ND",
    "R_fmadd",
    "R_fmin",
    "R_fmax",
    "R_idot",
    "R_iq15mulr",
    "R_trunc_u",
    "R_trunc_s",
    "R_swizzle",
    "R_laneselect",
    "trunc__",
    "trunc_sat__",
    "convert__",
    "promote__",
    "demote__",
];

/// How many of the 91 zero-clause builtin tags gain their **first** clauses
/// here: the six shift/rotate/count-zero operations, eight exact bit-structure
/// operations, four integer serialization/inverse operations, the exact
/// integer SIMD lane isomorphism, and three integer conversions. The other
/// eleven [`OPS`] supplement blocked spec lowerings.
pub const ZERO_CLAUSE_OPS_COVERED: usize = 74;

// ===========================================================================
// Term helpers (Side currency: bare nat metavars; spine currency: encodings)
// ===========================================================================

fn mv(id: &str) -> Term {
    metavar(id)
}

/// The encoded `iN` value `case.%(tup(num.nat x))` over a numeric term `x`
/// (bare metavar or bare numeral — the numeric-metavar discipline's wrapped
/// spine form).
fn ival(x: Term) -> Result<Term> {
    app(con("case.%"), app(con("tup"), wrap_nat(x)?)?)
}

/// `opt.some(v)` — the option-result convention shared with the Dec leg.
fn some(v: Term) -> Result<Term> {
    app(con("opt.some"), v)
}

/// `sx` constant: `case.U(tup)` / `case.S(tup)`.
fn sx_case(sx: &str) -> Result<Term> {
    app(con(format!("case.{sx}")), con("tup"))
}

/// The wrapped width literal for the `N` spine slot (`app(num.nat, ⌜w⌝)`) —
/// exactly what `fn.sizenn` / `fn.lsizenn` produce, so chains meet on keys.
fn w_lit(w: u64) -> Result<Term> {
    wrap_nat(mk_nat(w))
}

fn add(a: Term, b: Term) -> Result<Term> {
    nat::nat_add().apply(a)?.apply(b)
}
fn sub(a: Term, b: Term) -> Result<Term> {
    nat::nat_sub().apply(a)?.apply(b)
}
fn mul(a: Term, b: Term) -> Result<Term> {
    nat::nat_mul().apply(a)?.apply(b)
}
fn div(a: Term, b: Term) -> Result<Term> {
    nat::nat_div().apply(a)?.apply(b)
}
fn md(a: Term, b: Term) -> Result<Term> {
    nat::nat_mod().apply(a)?.apply(b)
}
/// `2^e` as a kernel-reducible term (numerals stay small; the kernel computes
/// the power at each ground discharge).
fn pow2(e: Term) -> Result<Term> {
    nat::nat_pow().apply(mk_nat(2u64))?.apply(e)
}
/// `2^w` / `2^(w−1)` with a literal exponent.
fn p2(w: u64) -> Result<Term> {
    pow2(mk_nat(w))
}
fn lt(a: Term, b: Term) -> Result<Term> {
    nat::nat_lt().apply(a)?.apply(b)
}
fn le(a: Term, b: Term) -> Result<Term> {
    nat::nat_le().apply(a)?.apply(b)
}

/// A clause whose premises are all `Side`s (this whole leg emits no
/// judgement premises: the definitions are closed arithmetic).
fn clause(metavars: &[&str], sides: Vec<Term>, concl: Term) -> Clause {
    Clause {
        metavars: metavars.iter().map(|s| s.to_string()).collect(),
        prems: sides.into_iter().map(LowerPrem::Side).collect(),
        concl,
    }
}

/// Carrier guard `x < 2^w`.
fn in_carrier(x: Term, w: u64) -> Result<Term> {
    lt(x, p2(w)?)
}

/// `k' = k mod w` (the spec takes shift counts modulo the width).
fn shift_amount(k: Term, w: u64) -> Result<Term> {
    md(k, mk_nat(w))
}

/// Reachable ordered width pairs. SpecTec uses these both for scalar
/// conversions and for packed integer fields. Keeping the family structural
/// (rather than enumerating instruction spellings) also covers every future
/// call site whose widths elaborate to the existing integer carriers.
fn width_pairs() -> impl Iterator<Item = (u64, u64)> {
    WIDTHS
        .into_iter()
        .flat_map(|m| WIDTHS.into_iter().map(move |n| (m, n)))
}

// ===========================================================================
// Per-op emitters
// ===========================================================================

/// The canonical encoded nonnegative rational `nat(n) / nat(d)` produced by
/// SpecTec's structural `nat -> rat` conversions.  Keeping the exact AST shape
/// here is what makes these clauses an under-approximation rather than a
/// representation-erasing rational oracle.
fn nat_ratio(n: Term, d: Term) -> Result<Term> {
    let cvt = |x| app(con("cvt.Nat.Rat"), wrap_nat(x)?);
    app(app(con("bin.Div"), cvt(n)?)?, cvt(d)?)
}

/// The same rational after extracting an integer carrier payload. This is the
/// exact shape of the real unsigned `idiv_`/`irem_` calls in the corpus.
fn carrier_ratio(n: Term, d: Term) -> Result<Term> {
    let payload = |x| app(con("proj.0"), app(con("uncase.%"), ival(x)?)?);
    let cvt = |x| app(con("cvt.Nat.Rat"), payload(x)?);
    app(app(con("bin.Div"), cvt(n)?)?, cvt(d)?)
}

// Exact finite-arithmetic frontier contract
// -----------------------------------------
//
// The remaining strict float arithmetic must not use a host float oracle. Its
// reusable intermediate should be:
//
//   ExactRatio {
//     sign: 0 | 1,
//     numerator: nat, denominator: nat, // both > 0
//     exp2: SignedNat,                  // value = (-1)^sign * n/d * 2^exp2
//   }
//
// It need not be gcd-reduced: cross multiplication, quotient, and remainder
// do not depend on canonical reduction. A witnessed `NormalizedRatio` adds the
// unique binary bin exponent `e` satisfying `2^e <= |x| < 2^(e+1)`. Emitters
// split signed exponents before forming powers, keeping every Side in natural
// arithmetic.
//
// The target quantum must be selected *before* rounding:
//
// - normal bin `e`: quantum `2^(e-p)`;
// - subnormal corridor: fixed quantum `2^(emin-p)`.
//
// Scale the original exact ratio once to `A/B = |x| / quantum`, define
// `q = A div B` and `r = A mod B`, and compare `2*r` with `B`. The strict
// inequalities plus equality and `q mod 2` are the complete nearest/ties-even
// partition even when `B` is odd. In particular, an implementation must not
// first round a normalized significand and then round that result into the
// subnormal corridor: that would introduce double-rounding. Existing carry,
// signed-zero, overflow, and quantified-NaN emitters consume the one rounded
// candidate.
//
// Proposed untrusted construction boundary:
//
//   trait ExactFloatOp {
//     fn exceptional_clauses(&self, width: u64) -> Result<Vec<Clause>>;
//     fn finite_ratio_cases(&self, width: u64) -> Result<Vec<RatioCase>>;
//   }
//   fn emit_normalized_ratio(case: RatioCase) -> Result<Vec<NormalizedCase>>;
//   fn select_target_quantum(case: NormalizedCase, width: u64)
//       -> Result<Vec<QuantumCase>>;
//   fn emit_round_ratio(case: QuantumCase, width: u64) -> Result<Vec<Clause>>;
//
// `RatioCase` owns metavariable names, Side premises, the input spine, and the
// ratio terms. `NormalizedCase` additionally owns the witnessed bin;
// `QuantumCase` records a normal/subnormal/overflow partition and the scaling
// direction needed to form `A/B` from the original ratio. Neither stores a
// theorem or mints a trusted rule; only NativeHol replay of emitted clauses
// establishes authority.
//
// The smallest end-to-end milestone is `fmul_`: its finite ratio has a wide
// significand product, denominator one, and an exponent sum. It exercises
// normalization and every output boundary without addition's cancellation or
// division's odd denominator. `fdiv_` follows to validate general `2*r` vs
// `B`; add/sub then add alignment and cancellation. `fsqrt_` is not rational
// and requires a separate integer-square-bound witness.

#[derive(Clone)]
#[cfg_attr(not(test), allow(dead_code))]
struct SignedNatTerm {
    negative: bool,
    magnitude: Term,
}

#[derive(Clone)]
#[cfg_attr(not(test), allow(dead_code))]
struct SignedTermCase {
    sides: Vec<Term>,
    value: SignedNatTerm,
}

/// Exact signed-magnitude addition with a small nonnegative carry.
///
/// Inputs marked negative are guarded away from negative zero. The returned
/// cases are disjoint except at ordinary positive zero, and cover every
/// ordering of the two magnitudes. This is the exponent arithmetic needed for
/// multiplying normalized float bins and adding normalization/rounding carry.
#[cfg_attr(not(test), allow(dead_code))]
fn signed_bin_add_cases(
    base: &[Term],
    left: SignedNatTerm,
    right: SignedNatTerm,
    carry: u64,
) -> Result<Vec<SignedTermCase>> {
    let mut base = base.to_vec();
    if left.negative {
        base.push(lt(mk_nat(0u64), left.magnitude.clone())?);
    }
    if right.negative {
        base.push(lt(mk_nat(0u64), right.magnitude.clone())?);
    }
    let carry = mk_nat(carry);
    let mut out = Vec::new();
    match (left.negative, right.negative) {
        (false, false) => out.push(SignedTermCase {
            sides: base,
            value: SignedNatTerm {
                negative: false,
                magnitude: add(add(left.magnitude, right.magnitude)?, carry)?,
            },
        }),
        (false, true) | (true, false) => {
            let (positive, negative) = if left.negative {
                (right.magnitude, left.magnitude)
            } else {
                (left.magnitude, right.magnitude)
            };
            let positive = add(positive, carry)?;
            let mut nonnegative = base.clone();
            nonnegative.push(le(negative.clone(), positive.clone())?);
            out.push(SignedTermCase {
                sides: nonnegative,
                value: SignedNatTerm {
                    negative: false,
                    magnitude: sub(positive.clone(), negative.clone())?,
                },
            });
            let mut negative_case = base;
            negative_case.push(lt(positive.clone(), negative.clone())?);
            out.push(SignedTermCase {
                sides: negative_case,
                value: SignedNatTerm {
                    negative: true,
                    magnitude: sub(negative, positive)?,
                },
            });
        }
        (true, true) => {
            let negative = add(left.magnitude, right.magnitude)?;
            let mut nonnegative = base.clone();
            nonnegative.push(le(negative.clone(), carry.clone())?);
            out.push(SignedTermCase {
                sides: nonnegative,
                value: SignedNatTerm {
                    negative: false,
                    magnitude: sub(carry.clone(), negative.clone())?,
                },
            });
            let mut negative_case = base;
            negative_case.push(lt(carry.clone(), negative.clone())?);
            out.push(SignedTermCase {
                sides: negative_case,
                value: SignedNatTerm {
                    negative: true,
                    magnitude: sub(negative, carry)?,
                },
            });
        }
    }
    Ok(out)
}

#[derive(Clone)]
#[cfg_attr(not(test), allow(dead_code))]
struct ExactRatioTerms {
    sign: u64,
    numerator: Term,
    denominator: Term,
    exp2: SignedNatTerm,
}

#[derive(Clone)]
#[cfg_attr(not(test), allow(dead_code))]
enum QuantumClass {
    Normal,
    Subnormal,
}

#[derive(Clone)]
#[cfg_attr(not(test), allow(dead_code))]
struct QuantumCase {
    sides: Vec<Term>,
    sign: u64,
    numerator: Term,
    denominator: Term,
    class: QuantumClass,
}

/// Scale an exact ratio by the reciprocal of a target quantum.
///
/// For `x = n/d * 2^e` and quantum `2^q`, this emits cases for the signed
/// difference `e-q`. A nonnegative difference multiplies the numerator by its
/// power of two; a negative difference multiplies the denominator. No rounding
/// occurs here, so the later quotient/remainder step observes the original
/// exact value exactly once.
#[cfg_attr(not(test), allow(dead_code))]
fn scale_ratio_to_quantum(
    base: &[Term],
    ratio: ExactRatioTerms,
    quantum_exp: SignedNatTerm,
    class: QuantumClass,
) -> Result<Vec<QuantumCase>> {
    let negated_quantums = if quantum_exp.negative {
        vec![(
            base.to_vec(),
            SignedNatTerm {
                negative: false,
                magnitude: quantum_exp.magnitude,
            },
        )]
    } else {
        let mut zero = base.to_vec();
        zero.push(quantum_exp.magnitude.clone().equals(mk_nat(0u64))?);
        let mut nonzero = base.to_vec();
        nonzero.push(lt(mk_nat(0u64), quantum_exp.magnitude.clone())?);
        vec![
            (
                zero,
                SignedNatTerm {
                    negative: false,
                    magnitude: mk_nat(0u64),
                },
            ),
            (
                nonzero,
                SignedNatTerm {
                    negative: true,
                    magnitude: quantum_exp.magnitude,
                },
            ),
        ]
    };
    let mut out = Vec::new();
    for (negation_sides, negated_quantum) in negated_quantums {
        for difference in
            signed_bin_add_cases(&negation_sides, ratio.exp2.clone(), negated_quantum, 0)?
        {
            let scale = pow2(difference.value.magnitude)?;
            let (numerator, denominator) = if difference.value.negative {
                (
                    ratio.numerator.clone(),
                    mul(ratio.denominator.clone(), scale)?,
                )
            } else {
                (
                    mul(ratio.numerator.clone(), scale)?,
                    ratio.denominator.clone(),
                )
            };
            let mut sides = difference.sides;
            sides.push(lt(mk_nat(0u64), ratio.numerator.clone())?);
            sides.push(lt(mk_nat(0u64), ratio.denominator.clone())?);
            out.push(QuantumCase {
                sides,
                sign: ratio.sign,
                numerator,
                denominator,
                class: class.clone(),
            });
        }
    }
    Ok(out)
}

fn rational_concl(op: &str, arg: Term, sign: u64, magnitude: Term) -> Result<Term> {
    fn_graph(op, &[arg], &wrap_int(sign, magnitude)?)
}

/// Exact structural-rational host primitives.  Clause order is positive,
/// negative-zero, negative-nonzero for each source declaration.
fn rational_rounding(op: &str, ceiling: bool, carrier: bool) -> Result<Vec<Clause>> {
    let ratio = |n, d| {
        if carrier {
            carrier_ratio(n, d)
        } else {
            nat_ratio(n, d)
        }
    };
    let negative_ratio = |n, d| app(con("un.Minus"), ratio(n, d)?);
    let positive_mag = if ceiling {
        div(sub(add(mv("n"), mv("d"))?, mk_nat(1u64))?, mv("d"))?
    } else {
        div(mv("n"), mv("d"))?
    };
    let floor_mag = div(mv("n"), mv("d"))?;
    Ok(vec![
        clause(
            &["n", "d", "r"],
            vec![lt(mk_nat(0u64), mv("d"))?, mv("r").equals(positive_mag)?],
            rational_concl(op, ratio(mv("n"), mv("d"))?, 0, mv("r"))?,
        ),
        clause(
            &["n", "d"],
            vec![lt(mk_nat(0u64), mv("d"))?, lt(mv("n"), mv("d"))?],
            rational_concl(op, negative_ratio(mv("n"), mv("d"))?, 0, mk_nat(0u64))?,
        ),
        clause(
            &["n", "d", "r"],
            vec![
                lt(mk_nat(0u64), mv("d"))?,
                le(mv("d"), mv("n"))?,
                mv("r").equals(floor_mag)?,
            ],
            rational_concl(op, negative_ratio(mv("n"), mv("d"))?, 1, mv("r"))?,
        ),
    ])
}

/// `fn.<op>(⌜w⌝, %(a), %(b), %(r))` — binary op conclusion (no `sx`).
fn bin_concl(op: &str, w: u64, a: &str, b: &str, r: &str) -> Result<Term> {
    fn_graph(op, &[w_lit(w)?, ival(mv(a))?, ival(mv(b))?], &ival(mv(r))?)
}

/// `fn.<op>(⌜w⌝, sx, %(a), %(b), result)`.
fn sx_concl(op: &str, w: u64, sx: &str, a: &str, b: &str, result: Term) -> Result<Term> {
    fn_graph(
        op,
        &[w_lit(w)?, sx_case(sx)?, ival(mv(a))?, ival(mv(b))?],
        &result,
    )
}

/// `isub_`: `r = (a + 2^w − b) mod 2^w`.
fn isub(w: u64) -> Result<Clause> {
    let r_def = mv("r").equals(md(sub(add(mv("a"), p2(w)?)?, mv("b"))?, p2(w)?)?)?;
    Ok(clause(
        &["a", "b", "r"],
        vec![in_carrier(mv("a"), w)?, in_carrier(mv("b"), w)?, r_def],
        bin_concl("isub_", w, "a", "b", "r")?,
    ))
}

/// `wrap__(M,N,%(a)) = %(a mod 2^N)`.
///
/// Although the core scalar instruction only uses 64→32, packed integer
/// paths use the same primitive at 8/16/32-bit field widths. We therefore
/// define the complete reachable width matrix. The input carrier guard keeps
/// the graph a faithful under-approximation outside the typed SpecTec domain.
fn wrap_conversion(m: u64, n: u64) -> Result<Clause> {
    Ok(clause(
        &["a", "r"],
        vec![
            in_carrier(mv("a"), m)?,
            in_carrier(mv("r"), n)?,
            mv("r").equals(md(mv("a"), p2(n)?)?)?,
        ],
        fn_graph(
            "wrap__",
            &[w_lit(m)?, w_lit(n)?, ival(mv("a"))?],
            &ival(mv("r"))?,
        )?,
    ))
}

/// Unsigned rounded average used by `i8x16.avgr_u` and `i16x8.avgr_u`.
///
/// WebAssembly defines this as `(a + b + 1) / 2`; evaluating in the unbounded
/// natural carrier before division is important because `a + b + 1` may need
/// one bit more than the lane. Only the two instruction-reachable widths and
/// the `U` sign selector receive clauses, so signed or invented-width calls
/// remain fail closed.
fn unsigned_average(w: u64) -> Result<Clause> {
    let rounded = div(add(add(mv("a"), mv("b"))?, mk_nat(1u64))?, mk_nat(2u64))?;
    Ok(clause(
        &["a", "b", "r"],
        vec![
            in_carrier(mv("a"), w)?,
            in_carrier(mv("b"), w)?,
            in_carrier(mv("r"), w)?,
            mv("r").equals(rounded)?,
        ],
        sx_concl("iavgr_", w, "U", "a", "b", ival(mv("r"))?)?,
    ))
}

/// Exact `i16x8.q15mulr_sat_s` lane primitive.
///
/// For signed 16-bit inputs this is the saturated Q15 product
/// `sat_s16((a * b + 2^14) >> 15)`.  We stay entirely in natural arithmetic:
/// same-sign products round to `(mag(a)·mag(b)+2^14) div 2^15`, while
/// opposite-sign products have magnitude
/// `ceil(max(mag(a)·mag(b)-2^14, 0)/2^15)`.  The sole overflowing rounded
/// result is `(-2^15)·(-2^15)`, which saturates to `2^15-1`.
///
/// Only the instruction-reachable `(N,sx)=(16,S)` specialization receives
/// clauses. Invented widths and `U` remain underivable.
fn q15mulr_sat() -> Result<Vec<Clause>> {
    const W: u64 = 16;
    let half = p2(14)?;
    let scale = p2(15)?;
    let conclusion = || sx_concl("iq15mulr_sat_", W, "S", "a", "b", ival(mv("r"))?);
    let carrier = || -> Result<Vec<Term>> {
        Ok(vec![
            in_carrier(mv("a"), W)?,
            in_carrier(mv("b"), W)?,
            in_carrier(mv("r"), W)?,
        ])
    };
    let sign_guard = |x: &str, negative: bool| -> Result<Term> {
        if negative {
            le(scale.clone(), mv(x))
        } else {
            lt(mv(x), scale.clone())
        }
    };
    let magnitude = |x: &str, negative: bool| -> Result<Term> {
        if negative {
            neg_mag(mv(x), W)
        } else {
            Ok(mv(x))
        }
    };

    let mut out = Vec::new();
    for (a_neg, b_neg) in [(false, false), (false, true), (true, false), (true, true)] {
        let product = mul(magnitude("a", a_neg)?, magnitude("b", b_neg)?)?;
        let mut sides = carrier()?;
        sides.push(sign_guard("a", a_neg)?);
        sides.push(sign_guard("b", b_neg)?);
        if a_neg == b_neg {
            let rounded = div(add(product, half.clone())?, scale.clone())?;
            sides.push(lt(rounded.clone(), scale.clone())?);
            sides.push(mv("r").equals(rounded)?);
        } else {
            // Nat subtraction is truncated, so products at or below the
            // half-way point correctly round to signed zero.
            let magnitude = div(
                add(
                    sub(product, half.clone())?,
                    sub(scale.clone(), mk_nat(1u64))?,
                )?,
                scale.clone(),
            )?;
            sides.push(mv("r").equals(neg_result(magnitude, W)?)?);
        }
        out.push(clause(&["a", "b", "r"], sides, conclusion()?));
    }

    // The only same-sign rounded magnitude outside the signed carrier:
    // INT16_MIN × INT16_MIN rounds to 2^15 and saturates to 2^15−1.
    out.push(clause(
        &[],
        vec![],
        fn_graph(
            "iq15mulr_sat_",
            &[
                w_lit(W)?,
                sx_case("S")?,
                ival(mk_nat(1u64 << 15))?,
                ival(mk_nat(1u64 << 15))?,
            ],
            &ival(mk_nat((1u64 << 15) - 1))?,
        )?,
    ));
    Ok(out)
}

/// Exact unsigned/sign extension of the low `m` bits into an `n`-bit
/// carrier. `m < n` is enforced by construction.
fn extended_value(a: Term, m: u64, n: u64, signed: bool) -> Result<Term> {
    let low = md(a, p2(m)?)?;
    if !signed {
        return Ok(low);
    }
    // If the source sign bit is clear, extension is the low value. If it is
    // set, prepend `n-m` one bits: low + 2^n - 2^m. The branch is selected in
    // the clauses below, avoiding an untrusted conditional operator.
    add(low, sub(p2(n)?, p2(m)?)?)
}

/// `extend__(M,N,sx,%(a))`: conversion between distinct integer carriers.
fn extend_conversion(m: u64, n: u64, sx: &str) -> Result<Vec<Clause>> {
    debug_assert!(m < n);
    let conclusion = |r: &str| {
        fn_graph(
            "extend__",
            &[w_lit(m)?, w_lit(n)?, sx_case(sx)?, ival(mv("a"))?],
            &ival(mv(r))?,
        )
    };
    let common =
        || -> Result<Vec<Term>> { Ok(vec![in_carrier(mv("a"), m)?, in_carrier(mv("r"), n)?]) };
    if sx == "U" {
        let mut sides = common()?;
        sides.push(mv("r").equals(extended_value(mv("a"), m, n, false)?)?);
        return Ok(vec![clause(&["a", "r"], sides, conclusion("r")?)]);
    }
    let low = md(mv("a"), p2(m)?)?;
    let mut nonnegative = common()?;
    nonnegative.push(lt(low.clone(), p2(m - 1)?)?);
    nonnegative.push(mv("r").equals(low.clone())?);
    let mut negative = common()?;
    negative.push(le(p2(m - 1)?, low)?);
    negative.push(mv("r").equals(extended_value(mv("a"), m, n, true)?)?);
    Ok(vec![
        clause(&["a", "r"], nonnegative, conclusion("r")?),
        clause(&["a", "r"], negative, conclusion("r")?),
    ])
}

/// `iextend_(N,M,sx,%(a))`: sign/zero-extend the low `M` bits while staying
/// in the original `N` carrier (the `i32.extend8_s` family).
fn integer_extend(n: u64, m: u64, sx: &str) -> Result<Vec<Clause>> {
    debug_assert!(m < n);
    let conclusion = |r: &str| {
        fn_graph(
            "iextend_",
            &[w_lit(n)?, w_lit(m)?, sx_case(sx)?, ival(mv("a"))?],
            &ival(mv(r))?,
        )
    };
    let common =
        || -> Result<Vec<Term>> { Ok(vec![in_carrier(mv("a"), n)?, in_carrier(mv("r"), n)?]) };
    if sx == "U" {
        let mut sides = common()?;
        sides.push(mv("r").equals(extended_value(mv("a"), m, n, false)?)?);
        return Ok(vec![clause(&["a", "r"], sides, conclusion("r")?)]);
    }
    let low = md(mv("a"), p2(m)?)?;
    let mut nonnegative = common()?;
    nonnegative.push(lt(low.clone(), p2(m - 1)?)?);
    nonnegative.push(mv("r").equals(low.clone())?);
    let mut negative = common()?;
    negative.push(le(p2(m - 1)?, low)?);
    negative.push(mv("r").equals(extended_value(mv("a"), m, n, true)?)?);
    Ok(vec![
        clause(&["a", "r"], nonnegative, conclusion("r")?),
        clause(&["a", "r"], negative, conclusion("r")?),
    ])
}

/// Saturating integer narrowing from an `m`-bit carrier to an `n`-bit
/// carrier. This is the scalar primitive used lane-wise by SIMD `NARROW`.
fn narrow_conversion(m: u64, n: u64, sx: &str) -> Result<Vec<Clause>> {
    debug_assert!(n < m);
    let conclusion = || {
        fn_graph(
            "narrow__",
            &[w_lit(m)?, w_lit(n)?, sx_case(sx)?, ival(mv("a"))?],
            &ival(mv("r"))?,
        )
    };
    let common =
        || -> Result<Vec<Term>> { Ok(vec![in_carrier(mv("a"), m)?, in_carrier(mv("r"), n)?]) };
    if sx == "U" {
        let max = sub(p2(n)?, mk_nat(1u64))?;
        let mut fits = common()?;
        fits.push(le(mv("a"), max.clone())?);
        fits.push(mv("r").equals(mv("a"))?);
        let mut high = common()?;
        high.push(lt(max.clone(), mv("a"))?);
        high.push(mv("r").equals(max)?);
        return Ok(vec![
            clause(&["a", "r"], fits, conclusion()?),
            clause(&["a", "r"], high, conclusion()?),
        ]);
    }

    let max = sub(p2(n - 1)?, mk_nat(1u64))?;
    let min_mag = p2(n - 1)?;
    let source_half = p2(m - 1)?;
    // Nonnegative source values either fit or saturate to +max.
    let mut pos_fits = common()?;
    pos_fits.push(lt(mv("a"), source_half.clone())?);
    pos_fits.push(le(mv("a"), max.clone())?);
    pos_fits.push(mv("r").equals(mv("a"))?);
    let mut pos_high = common()?;
    pos_high.push(lt(mv("a"), source_half.clone())?);
    pos_high.push(lt(max.clone(), mv("a"))?);
    pos_high.push(mv("r").equals(max)?);
    // Negative source values are compared by magnitude. Values down to the
    // destination minimum fit; more-negative values saturate at that minimum.
    let mag = neg_mag(mv("a"), m)?;
    let mut neg_fits = common()?;
    neg_fits.push(le(source_half.clone(), mv("a"))?);
    neg_fits.push(le(mag.clone(), min_mag.clone())?);
    neg_fits.push(mv("r").equals(sub(p2(n)?, mag.clone())?)?);
    let mut neg_low = common()?;
    neg_low.push(le(source_half, mv("a"))?);
    neg_low.push(lt(min_mag.clone(), mag)?);
    neg_low.push(mv("r").equals(min_mag)?);
    Ok(vec![
        clause(&["a", "r"], pos_fits, conclusion()?),
        clause(&["a", "r"], pos_high, conclusion()?),
        clause(&["a", "r"], neg_fits, conclusion()?),
        clause(&["a", "r"], neg_low, conclusion()?),
    ])
}

/// The sign-bias order embedding `biased(x) = (x + 2^(w−1)) mod 2^w`
/// (two's-complement signed order ≅ unsigned order after biasing).
fn biased(x: Term, w: u64) -> Result<Term> {
    md(add(x, p2(w - 1)?)?, p2(w)?)
}

/// The two outcome clauses of a comparison whose conclusion is
/// `fn.<op>(…, %(1))` when `cond` holds and `fn.<op>(…, %(0))` when `ncond`
/// (the exact complement) holds.
fn cmp_outcomes(
    op: &str,
    w: u64,
    sx: Option<&str>,
    cond: Term,
    ncond: Term,
) -> Result<Vec<Clause>> {
    let guards = vec![in_carrier(mv("a"), w)?, in_carrier(mv("b"), w)?];
    let concl = |result: u64| -> Result<Term> {
        let res = ival(mk_nat(result))?;
        match sx {
            Some(sx) => fn_graph(
                op,
                &[w_lit(w)?, sx_case(sx)?, ival(mv("a"))?, ival(mv("b"))?],
                &res,
            ),
            None => fn_graph(op, &[w_lit(w)?, ival(mv("a"))?, ival(mv("b"))?], &res),
        }
    };
    let mut on_true = guards.clone();
    on_true.push(cond);
    let mut on_false = guards;
    on_false.push(ncond);
    Ok(vec![
        clause(&["a", "b"], on_true, concl(1)?),
        clause(&["a", "b"], on_false, concl(0)?),
    ])
}

/// One ordering comparison (`ilt_`/`igt_`/`ile_`/`ige_`) at one width and
/// signedness. The op is defined by which unsigned order it takes on the
/// (possibly biased) operands: `lt(x, y)` with `(x, y)` = `(a, b)` for
/// `ilt_`/`ile_`-style or swapped for `igt_`/`ige_`; `strict` picks `<` vs
/// `≤`. Complement of `x < y` is `y ≤ x` and of `x ≤ y` is `y < x`.
fn ordering(op: &str, w: u64, sx: &str, swap: bool, strict: bool) -> Result<Vec<Clause>> {
    let (x, y) = {
        let a = if sx == "S" {
            biased(mv("a"), w)?
        } else {
            mv("a")
        };
        let b = if sx == "S" {
            biased(mv("b"), w)?
        } else {
            mv("b")
        };
        if swap { (b, a) } else { (a, b) }
    };
    let (cond, ncond) = if strict {
        (lt(x.clone(), y.clone())?, le(y, x)?)
    } else {
        (le(x.clone(), y.clone())?, lt(y, x)?)
    };
    cmp_outcomes(op, w, Some(sx), cond, ncond)
}

/// `ieq_`/`ine_` (no `sx`): equality of carrier values.
fn equality(op: &str, w: u64, negated: bool) -> Result<Vec<Clause>> {
    let eq = mv("a").equals(mv("b"))?;
    let ne = eq.clone().not()?;
    let (cond, ncond) = if negated { (ne.clone(), eq) } else { (eq, ne) };
    cmp_outcomes(op, w, None, cond, ncond)
}

/// `ieqz_(⌜w⌝, %(a), %(r))`: `r = 1 ⟺ a = 0`.
fn ieqz(w: u64) -> Result<Vec<Clause>> {
    let concl = |result: u64| -> Result<Term> {
        fn_graph(
            "ieqz_",
            &[w_lit(w)?, ival(mv("a"))?],
            &ival(mk_nat(result))?,
        )
    };
    let zero = mv("a").equals(mk_nat(0u64))?;
    Ok(vec![
        clause(
            &["a"],
            vec![in_carrier(mv("a"), w)?, zero.clone()],
            concl(1)?,
        ),
        clause(
            &["a"],
            vec![in_carrier(mv("a"), w)?, zero.not()?],
            concl(0)?,
        ),
    ])
}

/// `ishl_`: `r = (a · 2^(k mod w)) mod 2^w` (`k` is `u32`-typed).
fn ishl(w: u64) -> Result<Clause> {
    let kp = shift_amount(mv("k"), w)?;
    let r_def = mv("r").equals(md(mul(mv("a"), pow2(kp)?)?, p2(w)?)?)?;
    Ok(clause(
        &["a", "k", "r"],
        vec![in_carrier(mv("a"), w)?, in_carrier(mv("k"), 32)?, r_def],
        fn_graph(
            "ishl_",
            &[w_lit(w)?, ival(mv("a"))?, ival(mv("k"))?],
            &ival(mv("r"))?,
        )?,
    ))
}

/// `ishr_` (has `sx`): U one clause; S sign-split (nonneg / neg).
fn ishr(w: u64) -> Result<Vec<Clause>> {
    let concl = |sx: &str| -> Result<Term> {
        fn_graph(
            "ishr_",
            &[w_lit(w)?, sx_case(sx)?, ival(mv("a"))?, ival(mv("k"))?],
            &ival(mv("r"))?,
        )
    };
    let guards =
        || -> Result<Vec<Term>> { Ok(vec![in_carrier(mv("a"), w)?, in_carrier(mv("k"), 32)?]) };
    let kp = || shift_amount(mv("k"), w);
    // U: zero-filling shift = floor division.
    let mut u_sides = guards()?;
    u_sides.push(mv("r").equals(div(mv("a"), pow2(kp()?)?)?)?);
    let u = clause(&["a", "k", "r"], u_sides, concl("U")?);
    // S, nonnegative (`a < 2^(w−1)`): same as U.
    let mut s_pos = guards()?;
    s_pos.push(lt(mv("a"), p2(w - 1)?)?);
    s_pos.push(mv("r").equals(div(mv("a"), pow2(kp()?)?)?)?);
    let s_nonneg = clause(&["a", "k", "r"], s_pos, concl("S")?);
    // S, negative (`a ≥ 2^(w−1)`): sign-replicating —
    // r = a div 2^k' + (2^w − 2^(w−k')).
    let mut s_neg_sides = guards()?;
    s_neg_sides.push(le(p2(w - 1)?, mv("a"))?);
    let fill = sub(p2(w)?, pow2(sub(mk_nat(w), kp()?)?)?)?;
    s_neg_sides.push(mv("r").equals(add(div(mv("a"), pow2(kp()?)?)?, fill)?)?);
    let s_neg = clause(&["a", "k", "r"], s_neg_sides, concl("S")?);
    Ok(vec![u, s_nonneg, s_neg])
}

/// `irotl_` / `irotr_` (second operand is `iN`-typed like the first).
fn rotate(op: &str, w: u64, left: bool) -> Result<Clause> {
    let kp = || shift_amount(mv("b"), w);
    let r_def = if left {
        // (a·2^k') mod 2^w + a div 2^(w−k')
        mv("r").equals(add(
            md(mul(mv("a"), pow2(kp()?)?)?, p2(w)?)?,
            div(mv("a"), pow2(sub(mk_nat(w), kp()?)?)?)?,
        )?)?
    } else {
        // a div 2^k' + (a mod 2^k')·2^(w−k')
        mv("r").equals(add(
            div(mv("a"), pow2(kp()?)?)?,
            mul(md(mv("a"), pow2(kp()?)?)?, pow2(sub(mk_nat(w), kp()?)?)?)?,
        )?)?
    };
    Ok(clause(
        &["a", "b", "r"],
        vec![in_carrier(mv("a"), w)?, in_carrier(mv("b"), w)?, r_def],
        bin_concl(op, w, "a", "b", "r")?,
    ))
}

/// `iclz_` / `ictz_`: ground `0 ↦ w` clause + the nonzero pinning clause.
fn count_zeros(op: &str, w: u64, leading: bool) -> Result<Vec<Clause>> {
    let concl_ground = fn_graph(op, &[w_lit(w)?, ival(mk_nat(0u64))?], &ival(mk_nat(w))?)?;
    let zero = clause(&[], vec![], concl_ground);
    let sides = if leading {
        // 2^(w−1−r) ≤ a < 2^(w−r) pins r = w − 1 − ⌊log₂ a⌋ (and refuses
        // a = 0 and every junk r — the bounds become contradictory).
        vec![
            in_carrier(mv("a"), w)?,
            le(pow2(sub(mk_nat(w - 1), mv("r"))?)?, mv("a"))?,
            lt(mv("a"), pow2(sub(mk_nat(w), mv("r"))?)?)?,
        ]
    } else {
        // a mod 2^r = 0 ∧ a mod 2^(r+1) ≠ 0 pins r = trailing zeros (and
        // refuses a = 0: the second side becomes ¬(0 = 0)).
        vec![
            in_carrier(mv("a"), w)?,
            md(mv("a"), pow2(mv("r"))?)?.equals(mk_nat(0u64))?,
            md(mv("a"), pow2(add(mv("r"), mk_nat(1u64))?)?)?
                .equals(mk_nat(0u64))?
                .not()?,
        ]
    };
    let nonzero = clause(
        &["a", "r"],
        sides,
        fn_graph(op, &[w_lit(w)?, ival(mv("a"))?], &ival(mv("r"))?)?,
    );
    Ok(vec![zero, nonzero])
}

/// Bit `i` of a natural carrier value, as a kernel-computable natural in
/// `{0,1}`. Fixed-width bit operations are deliberately expanded into this
/// arithmetic basis instead of adding trusted bitwise primitives.
fn bit(x: Term, i: u64) -> Result<Term> {
    md(div(x, p2(i)?)?, mk_nat(2u64))
}

/// A left-associated natural sum (the widths are at most 64, so this stays
/// comfortably below the evaluator's stack limits and adds no evaluator
/// clauses).
fn sum(ts: impl IntoIterator<Item = Result<Term>>) -> Result<Term> {
    let mut acc = mk_nat(0u64);
    for t in ts {
        acc = add(acc, t?)?;
    }
    Ok(acc)
}

/// Reassemble a fixed-width result from a per-bit arithmetic expression.
fn bits_value(w: u64, f: impl Fn(u64) -> Result<Term>) -> Result<Term> {
    sum((0..w).map(|i| Ok(mul(f(i)?, p2(i)?)?)))
}

/// One exact unary bit-operation graph clause.
fn bit_unary(op: &str, w: u64, result: Term) -> Result<Clause> {
    Ok(clause(
        &["a", "r"],
        vec![
            in_carrier(mv("a"), w)?,
            in_carrier(mv("r"), w)?,
            mv("r").equals(result)?,
        ],
        fn_graph(op, &[w_lit(w)?, ival(mv("a"))?], &ival(mv("r"))?)?,
    ))
}

/// One exact binary bit-operation graph clause.
fn bit_binary(op: &str, w: u64, result: Term) -> Result<Clause> {
    Ok(clause(
        &["a", "b", "r"],
        vec![
            in_carrier(mv("a"), w)?,
            in_carrier(mv("b"), w)?,
            in_carrier(mv("r"), w)?,
            mv("r").equals(result)?,
        ],
        bin_concl(op, w, "a", "b", "r")?,
    ))
}

/// Exact fixed-width bit-structure clauses, expressed solely through natural
/// `div`/`mod`/`pow`/`add`/`sub`/`mul`:
///
/// - boolean bits use `and = ab`, `or = a+b-ab`, `xor = a+b-2ab`;
/// - popcount sums the bits and reverse reweights bit `i` at `w-1-i`;
/// - bitselect is `(a & mask) | (b & ~mask)` (the summands are disjoint).
fn bit_structure(w: u64) -> Result<Vec<Clause>> {
    let abit = |i| bit(mv("a"), i);
    let bbit = |i| bit(mv("b"), i);
    let and_bit = |i| mul(abit(i)?, bbit(i)?);
    let or_bit = |i| sub(add(abit(i)?, bbit(i)?)?, and_bit(i)?);
    let xor_bit = |i| sub(add(abit(i)?, bbit(i)?)?, mul(mk_nat(2u64), and_bit(i)?)?);
    let andnot_bit = |i| mul(abit(i)?, sub(mk_nat(1u64), bbit(i)?)?);

    let mut out = vec![
        bit_unary("inot_", w, sub(sub(p2(w)?, mk_nat(1u64))?, mv("a"))?)?,
        bit_unary(
            "irev_",
            w,
            sum((0..w).map(|i| Ok(mul(abit(i)?, p2(w - 1 - i)?)?)))?,
        )?,
        bit_unary("ipopcnt_", w, sum((0..w).map(abit))?)?,
        bit_binary("iand_", w, bits_value(w, and_bit)?)?,
        bit_binary("iandnot_", w, bits_value(w, andnot_bit)?)?,
        bit_binary("ior_", w, bits_value(w, or_bit)?)?,
        bit_binary("ixor_", w, bits_value(w, xor_bit)?)?,
    ];

    let cbit = |i| bit(mv("c"), i);
    // Selected bits are disjoint, so ordinary addition is exactly OR.
    let selected = bits_value(w, |i| {
        add(
            mul(abit(i)?, cbit(i)?)?,
            mul(bbit(i)?, sub(mk_nat(1u64), cbit(i)?)?)?,
        )
    })?;
    out.push(clause(
        &["a", "b", "c", "r"],
        vec![
            in_carrier(mv("a"), w)?,
            in_carrier(mv("b"), w)?,
            in_carrier(mv("c"), w)?,
            in_carrier(mv("r"), w)?,
            mv("r").equals(selected)?,
        ],
        fn_graph(
            "ibitselect_",
            &[w_lit(w)?, ival(mv("a"))?, ival(mv("b"))?, ival(mv("c"))?],
            &ival(mv("r"))?,
        )?,
    ));
    Ok(out)
}

/// The encoded list spine used by SpecTec list literals: `list` followed by
/// its elements in source order. Serialization is little-endian, so element
/// zero is the least-significant bit/byte.
fn encoded_nat_list(ids: &[String]) -> Result<Term> {
    let mut out = con("list");
    for id in ids {
        out = app(out, wrap_nat(mv(id))?)?;
    }
    Ok(out)
}

/// Exact recursive graphs over the reified SpecTec list spine.
///
/// A list literal is the free `st$app` snoc spine
/// `list`, `app(list,x0)`, `app(app(list,x0),x1)`, ... .  These clauses inspect
/// that structure relationally, rather than assigning `st$app` any trusted
/// interpretation or enumerating a maximum arity.
///
/// `inv_concat_` consumes two spine cells at a time.  Its base and step
/// therefore derive exactly even-length inputs and preserve adjacent,
/// source-order pairs.
///
/// `inv_concatn_.split` is the reusable structural view for an exact suffix of
/// length `n`: `split(n, input, prefix, block)`.  The zero clause exposes an
/// empty block; the successor clause peels one input cell and reconstructs the
/// block in source order.  `inv_concatn_` repeatedly uses that view, requiring
/// `n > 0`; it consequently refuses zero, short final blocks, and
/// nonmultiples without a fixed bound.
fn inverse_sequence_clauses() -> Result<Vec<Clause>> {
    let pair = app(app(con("list"), mv("a"))?, mv("b"))?;
    let pair_base = Clause {
        metavars: Vec::new(),
        prems: Vec::new(),
        concl: fn_graph("inv_concat_", &[con("list")], &con("list"))?,
    };
    let pair_step = Clause {
        metavars: ["xs", "ys", "a", "b"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
        prems: vec![LowerPrem::Judgement(fn_graph(
            "inv_concat_",
            &[mv("xs")],
            &mv("ys"),
        )?)],
        concl: fn_graph(
            "inv_concat_",
            &[app(app(mv("xs"), mv("a"))?, mv("b"))?],
            &app(mv("ys"), pair)?,
        )?,
    };

    // split(0, prefix, prefix, []).
    // split(n, xs, prefix, block) =>
    // split(S n, xs·x, prefix, block·x).
    //
    // The graph's result is the pair `prefix, block`, represented by the same
    // ordinary `tup` spine used throughout the SpecTec encoding.
    let split_result = |prefix: Term, block: Term| app(app(con("tup"), prefix)?, block);
    let split_base = Clause {
        metavars: vec!["prefix".to_owned()],
        prems: Vec::new(),
        concl: fn_graph(
            "inv_concatn_.split",
            &[wrap_nat(mk_nat(0u64))?, mv("prefix")],
            &split_result(mv("prefix"), con("list"))?,
        )?,
    };
    let split_step = Clause {
        metavars: ["n", "n1", "xs", "prefix", "block", "x"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
        prems: vec![
            LowerPrem::Side(mv("n1").equals(nat::succ(mv("n")))?),
            LowerPrem::Judgement(fn_graph(
                "inv_concatn_.split",
                &[wrap_nat(mv("n"))?, mv("xs")],
                &split_result(mv("prefix"), mv("block"))?,
            )?),
        ],
        concl: fn_graph(
            "inv_concatn_.split",
            &[wrap_nat(mv("n1"))?, app(mv("xs"), mv("x"))?],
            &split_result(mv("prefix"), app(mv("block"), mv("x"))?)?,
        )?,
    };

    let chunks_base = Clause {
        metavars: vec!["n".to_owned()],
        prems: vec![LowerPrem::Side(lt(mk_nat(0u64), mv("n"))?)],
        concl: fn_graph(
            "inv_concatn_",
            &[wrap_nat(mv("n"))?, con("list")],
            &con("list"),
        )?,
    };
    let chunks_step = Clause {
        metavars: ["n", "input", "prefix", "block", "blocks"]
            .into_iter()
            .map(str::to_owned)
            .collect(),
        prems: vec![
            LowerPrem::Side(lt(mk_nat(0u64), mv("n"))?),
            LowerPrem::Judgement(fn_graph(
                "inv_concatn_.split",
                &[wrap_nat(mv("n"))?, mv("input")],
                &split_result(mv("prefix"), mv("block"))?,
            )?),
            LowerPrem::Judgement(fn_graph(
                "inv_concatn_",
                &[wrap_nat(mv("n"))?, mv("prefix")],
                &mv("blocks"),
            )?),
        ],
        concl: fn_graph(
            "inv_concatn_",
            &[wrap_nat(mv("n"))?, mv("input")],
            &app(mv("blocks"), mv("block"))?,
        )?,
    };

    Ok(vec![
        pair_base,
        pair_step,
        split_base,
        split_step,
        chunks_base,
        chunks_step,
    ])
}

/// The four integer SIMD shapes admitted by the WebAssembly 128-bit vector
/// carrier. Float shapes stay deliberately absent until HOL has an exact float
/// carrier; emitting no clause is the fail-closed interpretation.
const INTEGER_LANE_SHAPES: [(&str, u64, u64); 4] = [
    ("I8", 8, 16),
    ("I16", 16, 8),
    ("I32", 32, 4),
    ("I64", 64, 2),
];

/// Encoded `Lnn X M`: `case.X(tup(case.Lnn(tup), num.nat(M)))`.
fn lane_shape(lane: &str, dim: u64) -> Result<Term> {
    let lane = app(con(format!("case.{lane}")), con("tup"))?;
    let payload = app(app(con("tup"), lane)?, wrap_nat(mk_nat(dim))?)?;
    app(con("case.X"), payload)
}

/// Exact integer `lanes_` / `inv_lanes_` clauses for one 128-bit shape.
///
/// Lane zero is the least-significant lane, matching the spec's little-endian
/// `ibytes_` convention and WebAssembly's lane numbering. Both directions use
/// the same exposed lane metavariables and arithmetic reconstruction, making
/// malformed lengths, out-of-carrier lanes, and wrong vectors underivable.
fn integer_lanes(lane: &str, w: u64, dim: u64) -> Result<Vec<Clause>> {
    debug_assert_eq!(w * dim, 128);
    let ids: Vec<String> = (0..dim).map(|i| format!("lane{i}")).collect();
    let mut metavars = vec!["v".to_owned()];
    metavars.extend(ids.iter().cloned());
    let mut common = vec![in_carrier(mv("v"), 128)?];
    let base = p2(w)?;
    for id in &ids {
        common.push(lt(mv(id), base.clone())?);
    }
    let lanes = {
        let mut out = con("list");
        for id in &ids {
            out = app(out, ival(mv(id))?)?;
        }
        out
    };
    let shape = lane_shape(lane, dim)?;
    let names: Vec<&str> = metavars.iter().map(String::as_str).collect();

    let mut split_sides = common.clone();
    for (i, id) in ids.iter().enumerate() {
        split_sides.push(mv(id).equals(md(div(mv("v"), p2(w * i as u64)?)?, base.clone())?)?);
    }
    let split = clause(
        &names,
        split_sides,
        fn_graph("lanes_", &[shape.clone(), ival(mv("v"))?], &lanes)?,
    );

    let rebuilt = sum(ids
        .iter()
        .enumerate()
        .map(|(i, id)| Ok(mul(mv(id), p2(w * i as u64)?)?)))?;
    common.push(mv("v").equals(rebuilt)?);
    let join = clause(
        &names,
        common,
        fn_graph("inv_lanes_", &[shape, lanes], &ival(mv("v"))?)?,
    );
    Ok(vec![split, join])
}

/// Exact integer bit/byte serialization and its inverse at a fixed reachable
/// width. Each element is exposed as a conclusion metavariable and pinned by
/// kernel-computable arithmetic:
///
/// - `ibits_(N, i)` = `[bit(i, 0), …, bit(i, N-1)]`;
/// - `ibytes_(N, i)` = `[i mod 2^8, …]`, least-significant byte first;
/// - the inverse clauses accept exactly those fixed-length lists whose
///   elements are in the bit/byte carrier, and reassemble the integer.
///
/// This intentionally emits no clause for malformed lengths or unsupported
/// symbolic widths. It is a sound bounded family over all widths reachable
/// from scalar and SIMD integer call sites.
fn integer_serialization(w: u64) -> Result<Vec<Clause>> {
    fn one(op: &str, inverse: bool, w: u64, radix_bits: u64) -> Result<Clause> {
        let n = w / radix_bits;
        let ids: Vec<String> = (0..n).map(|i| format!("e{i}")).collect();
        let mut metavars = vec!["a".to_owned()];
        metavars.extend(ids.iter().cloned());
        let mut sides = vec![in_carrier(mv("a"), w)?];
        let base = p2(radix_bits)?;
        for (i, id) in ids.iter().enumerate() {
            sides.push(lt(mv(id), base.clone())?);
            if !inverse {
                sides.push(
                    mv(id).equals(md(div(mv("a"), p2(radix_bits * i as u64)?)?, base.clone())?)?,
                );
            }
        }
        if inverse {
            let rebuilt = sum(ids
                .iter()
                .enumerate()
                .map(|(i, id)| Ok(mul(mv(id), p2(radix_bits * i as u64)?)?)))?;
            sides.push(mv("a").equals(rebuilt)?);
        }
        let list = encoded_nat_list(&ids)?;
        let (args, result) = if inverse {
            (vec![w_lit(w)?, list], ival(mv("a"))?)
        } else {
            (vec![w_lit(w)?, ival(mv("a"))?], list)
        };
        let names: Vec<&str> = metavars.iter().map(String::as_str).collect();
        Ok(clause(&names, sides, fn_graph(op, &args, &result)?))
    }

    Ok(vec![
        one("ibits_", false, w, 1)?,
        one("inv_ibits_", true, w, 1)?,
        one("ibytes_", false, w, 8)?,
        one("inv_ibytes_", true, w, 8)?,
    ])
}

/// One exact IEEE representation case of SpecTec's structural
/// `fN(N)` carrier. `raw` is the corresponding unsigned `N`-bit payload.
fn float_case_named(
    w: u64,
    sign: u64,
    kind: &str,
    exp_sign: Option<u64>,
    prefix: &str,
) -> Result<FloatCase> {
    let name = |id: &str| format!("{prefix}{id}");
    let vm = || mv(&name("m"));
    let ve = || mv(&name("e"));
    let (m_bits, e_bits) = match w {
        32 => (23, 8),
        64 => (52, 11),
        _ => unreachable!("only WebAssembly scalar float widths"),
    };
    let mut names = Vec::new();
    let mut sides = Vec::new();
    let magnitude = match kind {
        "subnormal" => {
            names.push(name("m"));
            sides.push(lt(vm(), p2(m_bits)?)?);
            app(con("case.SUBNORM"), app(con("tup"), wrap_nat(vm())?)?)?
        }
        "normal" => {
            names.extend([name("m"), name("e")]);
            sides.push(lt(vm(), p2(m_bits)?)?);
            let es = exp_sign.expect("normal exponent sign");
            if es == 0 {
                sides.push(le(ve(), mk_nat(p2_u64(e_bits - 1) - 1))?);
            } else {
                // Canonical negative integers exclude negative zero. The
                // minimum normal exponent is 2 - 2^(E-1).
                sides.push(lt(mk_nat(0u64), ve())?);
                sides.push(le(ve(), mk_nat(p2_u64(e_bits - 1) - 2))?);
            }
            let payload = app(app(con("tup"), wrap_nat(vm())?)?, wrap_int(es, ve())?)?;
            app(con("case.NORM"), payload)?
        }
        "infinity" => app(con("case.INF"), con("tup"))?,
        "nan" => {
            names.push(name("m"));
            sides.push(lt(mk_nat(0u64), vm())?);
            sides.push(lt(vm(), p2(m_bits)?)?);
            app(con("case.NAN"), app(con("tup"), wrap_nat(vm())?)?)?
        }
        _ => unreachable!(),
    };
    let value = app(
        con(if sign == 0 { "case.POS" } else { "case.NEG" }),
        magnitude.clone(),
    )?;
    let sign_part = mul(mk_nat(sign), p2(w - 1)?)?;
    let raw = match kind {
        "subnormal" => add(sign_part, vm())?,
        "infinity" => add(
            sign_part,
            mul(sub(p2(e_bits)?, mk_nat(1u64))?, p2(m_bits)?)?,
        )?,
        "nan" => add(
            add(
                sign_part,
                mul(sub(p2(e_bits)?, mk_nat(1u64))?, p2(m_bits)?)?,
            )?,
            vm(),
        )?,
        "normal" => {
            let bias = p2_u64(e_bits - 1) - 1;
            let biased = if exp_sign == Some(0) {
                add(mk_nat(bias), ve())?
            } else {
                sub(mk_nat(bias), ve())?
            };
            add(add(sign_part, mul(biased, p2(m_bits)?)?)?, vm())?
        }
        _ => unreachable!(),
    };
    Ok((names, sides, sign, magnitude, value, raw))
}

const fn p2_u64(n: u64) -> u64 {
    1u64 << n
}

type FloatCase = (Vec<String>, Vec<Term>, u64, Term, Term, Term);

fn float_cases(w: u64) -> Result<Vec<FloatCase>> {
    float_cases_named(w, "")
}

fn float_cases_named(w: u64, prefix: &str) -> Result<Vec<FloatCase>> {
    let mut out = Vec::new();
    for sign in [0, 1] {
        out.push(float_case_named(w, sign, "subnormal", None, prefix)?);
        out.push(float_case_named(w, sign, "normal", Some(0), prefix)?);
        out.push(float_case_named(w, sign, "normal", Some(1), prefix)?);
        out.push(float_case_named(w, sign, "infinity", None, prefix)?);
        out.push(float_case_named(w, sign, "nan", None, prefix)?);
    }
    Ok(out)
}

fn encoded_digits(
    raw: Term,
    width: u64,
    radix_bits: u64,
) -> Result<(Vec<String>, Vec<Term>, Term)> {
    let ids: Vec<String> = (0..width / radix_bits).map(|i| format!("d{i}")).collect();
    let mut sides = Vec::new();
    let base = p2(radix_bits)?;
    for (i, id) in ids.iter().enumerate() {
        sides.push(lt(mv(id), base.clone())?);
        sides.push(mv(id).equals(md(
            div(raw.clone(), p2(radix_bits * i as u64)?)?,
            base.clone(),
        )?)?);
    }
    let list = encoded_nat_list(&ids)?;
    Ok((ids, sides, list))
}

/// Exact IEEE bit/byte isomorphisms for all finite values and infinities.
/// The representation is derived from the SpecTec sign/magnitude constructors
/// using natural arithmetic; no host floating-point operation participates.
fn float_serialization() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for w in [32, 64] {
        for (base_names, base_sides, _sign, _magnitude, value, raw) in float_cases(w)? {
            for (op, inverse, radix_bits) in [
                ("fbits_", false, 1),
                ("inv_fbits_", true, 1),
                ("fbytes_", false, 8),
                ("inv_fbytes_", true, 8),
            ] {
                let (digits, digit_sides, list) = encoded_digits(raw.clone(), w, radix_bits)?;
                let mut names = base_names.clone();
                names.extend(digits);
                let mut sides = base_sides.clone();
                sides.extend(digit_sides);
                let (args, result) = if inverse {
                    (vec![w_lit(w)?, list], value.clone())
                } else {
                    (vec![w_lit(w)?, value.clone()], list)
                };
                let refs: Vec<&str> = names.iter().map(String::as_str).collect();
                out.push(clause(&refs, sides, fn_graph(op, &args, &result)?));
            }
        }
    }
    Ok(out)
}

/// Float branches of the type-directed byte front doors. These share exactly
/// the primitive `fbytes_` equations above while preserving the source type
/// constructor.
fn composite_float_byte_serialization() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for (w, ty) in [(32, "F32"), (64, "F64")] {
        for (base_names, base_sides, _sign, _magnitude, value, raw) in float_cases(w)? {
            let (digits, digit_sides, bytes) = encoded_digits(raw, w, 8)?;
            let mut names = base_names;
            names.extend(digits);
            let mut sides = base_sides;
            sides.extend(digit_sides);
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            for (op, inverse) in [
                ("nbytes_", false),
                ("inv_nbytes_", true),
                ("zbytes_", false),
                ("inv_zbytes_", true),
                ("cbytes_", false),
                ("inv_cbytes_", true),
            ] {
                let (args, result) = if inverse {
                    (vec![numtype(ty)?, bytes.clone()], value.clone())
                } else {
                    (vec![numtype(ty)?, value.clone()], bytes.clone())
                };
                out.push(clause(&refs, sides.clone(), fn_graph(op, &args, &result)?));
            }
        }
    }
    Ok(out)
}

fn numtype(name: &str) -> Result<Term> {
    app(con(format!("case.{name}")), con("tup"))
}

/// Exact same-width integer/float reinterpretation on the structural IEEE
/// fragment. Both directions share the very same `raw` equation.
fn float_reinterpretation() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for (w, i, f) in [(32, "I32", "F32"), (64, "I64", "F64")] {
        for (mut names, mut sides, _sign, _magnitude, value, raw) in float_cases(w)? {
            names.push("raw".to_owned());
            sides.push(in_carrier(mv("raw"), w)?);
            sides.push(mv("raw").equals(raw)?);
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            out.push(clause(
                &refs,
                sides.clone(),
                fn_graph(
                    "reinterpret__",
                    &[numtype(i)?, numtype(f)?, ival(mv("raw"))?],
                    &value,
                )?,
            ));
            out.push(clause(
                &refs,
                sides,
                fn_graph(
                    "reinterpret__",
                    &[numtype(f)?, numtype(i)?, value],
                    &ival(mv("raw"))?,
                )?,
            ));
        }
    }
    Ok(out)
}

fn singleton(value: Term) -> Result<Term> {
    app(con("list"), value)
}

/// `fabs` and `fneg` are pure sign-bit transformations, so they need no
/// floating arithmetic, including for exact NaN payloads.
fn float_sign_ops() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for w in [32, 64] {
        for (names, sides, sign, magnitude, value, _raw) in float_cases(w)? {
            let pos = app(con("case.POS"), magnitude.clone())?;
            let flipped = app(
                con(if sign == 0 { "case.NEG" } else { "case.POS" }),
                magnitude,
            )?;
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            out.push(clause(
                &refs,
                sides.clone(),
                fn_graph("fabs_", &[w_lit(w)?, value.clone()], &singleton(pos)?)?,
            ));
            out.push(clause(
                &refs,
                sides,
                fn_graph("fneg_", &[w_lit(w)?, value], &singleton(flipped)?)?,
            ));
        }
    }
    Ok(out)
}

const FLOAT_SHAPES: [(&str, Option<u64>); 5] = [
    ("subnormal", None),
    ("normal", Some(0)),
    ("normal", Some(1)),
    ("infinity", None),
    ("nan", None),
];

fn float_order_key(w: u64, sign: u64, raw: Term) -> Result<Term> {
    if sign == 0 {
        add(p2(w - 1)?, raw)
    } else {
        sub(sub(p2(w)?, mk_nat(1u64))?, raw)
    }
}

fn float_comparison_concl(op: &str, w: u64, left: Term, right: Term, result: u64) -> Result<Term> {
    fn_graph(op, &[w_lit(w)?, left, right], &ival(mk_nat(result))?)
}

fn push_float_comparison(
    out: &mut Vec<Clause>,
    names: &[String],
    base: &[Term],
    op: &str,
    w: u64,
    left: &Term,
    right: &Term,
    result: u64,
    guard: Term,
) -> Result<()> {
    let mut sides = base.to_vec();
    sides.push(guard);
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    out.push(clause(
        &refs,
        sides,
        float_comparison_concl(op, w, left.clone(), right.clone(), result)?,
    ));
    Ok(())
}

fn float_selection_concl(op: &str, w: u64, left: Term, right: Term, result: Term) -> Result<Term> {
    fn_graph(op, &[w_lit(w)?, left, right], &singleton(result)?)
}

fn push_float_selection(
    out: &mut Vec<Clause>,
    names: &[String],
    base: &[Term],
    op: &str,
    w: u64,
    left: &Term,
    right: &Term,
    result: &Term,
    guard: Term,
) -> Result<()> {
    let mut sides = base.to_vec();
    sides.push(guard);
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    out.push(clause(
        &refs,
        sides,
        float_selection_concl(op, w, left.clone(), right.clone(), result.clone())?,
    ));
    Ok(())
}

fn push_binary_nan_result_set(
    out: &mut Vec<Clause>,
    names: &[String],
    base: &[Term],
    w: u64,
    left: &Term,
    right: &Term,
    left_nan: bool,
    right_nan: bool,
) -> Result<()> {
    debug_assert!(left_nan || right_nan);
    let p = if w == 32 { 23 } else { 52 };
    let canon = p2(p - 1)?;

    let mut canonical = base.to_vec();
    if left_nan {
        canonical.push(mv("a_m").equals(canon.clone())?);
    }
    if right_nan {
        canonical.push(mv("b_m").equals(canon.clone())?);
    }

    // Partition "at least one noncanonical NaN" without disjunction or
    // overlap: the left arithmetic branch has precedence, and the right
    // branch requires a canonical left NaN when both operands are NaNs.
    let mut arithmetic_inputs = Vec::new();
    if left_nan {
        for noncanonical in [lt(mv("a_m"), canon.clone())?, lt(canon.clone(), mv("a_m"))?] {
            let mut branch = base.to_vec();
            branch.push(noncanonical);
            arithmetic_inputs.push(branch);
        }
    }
    if right_nan {
        for noncanonical in [lt(mv("b_m"), canon.clone())?, lt(canon.clone(), mv("b_m"))?] {
            let mut branch = base.to_vec();
            if left_nan {
                branch.push(mv("a_m").equals(canon.clone())?);
            }
            branch.push(noncanonical);
            arithmetic_inputs.push(branch);
        }
    }

    for op in ["fmin_", "fmax_"] {
        for output_sign in [0, 1] {
            let mut sides = canonical.clone();
            sides.push(mv("dst_m").equals(canon.clone())?);
            let mut clause_names = names.to_vec();
            clause_names.push("dst_m".to_owned());
            let refs: Vec<&str> = clause_names.iter().map(String::as_str).collect();
            out.push(clause(
                &refs,
                sides,
                float_selection_concl(
                    op,
                    w,
                    left.clone(),
                    right.clone(),
                    structural_nan(output_sign, mv("dst_m"))?,
                )?,
            ));

            for mut sides in arithmetic_inputs.clone() {
                sides.push(le(canon.clone(), mv("dst_m"))?);
                sides.push(lt(mv("dst_m"), p2(p)?)?);
                out.push(clause(
                    &refs,
                    sides,
                    float_selection_concl(
                        op,
                        w,
                        left.clone(),
                        right.clone(),
                        structural_nan(output_sign, mv("dst_m"))?,
                    )?,
                ));
            }
        }
    }
    Ok(())
}

/// Exact IEEE comparisons and `copysign` over the complete structural
/// carrier. The monotone integer key reverses negative raw payloads and
/// shifts positive payloads above them; signed zeros are handled separately,
/// and every comparison with a NaN has the specified unordered result.
fn float_comparisons_and_copysign() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for w in [32, 64] {
        for left_sign in [0, 1] {
            for (left_kind, left_exp) in FLOAT_SHAPES {
                let (left_names, left_sides, _, left_mag, left, left_raw) =
                    float_case_named(w, left_sign, left_kind, left_exp, "a_")?;
                for right_sign in [0, 1] {
                    for (right_kind, right_exp) in FLOAT_SHAPES {
                        let (right_names, right_sides, _, _right_mag, right, right_raw) =
                            float_case_named(w, right_sign, right_kind, right_exp, "b_")?;
                        let mut names = left_names.clone();
                        names.extend(right_names);
                        let mut base = left_sides.clone();
                        base.extend(right_sides);
                        let refs: Vec<&str> = names.iter().map(String::as_str).collect();

                        // Copying the sign never performs arithmetic and
                        // preserves every payload, including NaNs.
                        let copied = app(
                            con(if right_sign == 0 {
                                "case.POS"
                            } else {
                                "case.NEG"
                            }),
                            left_mag.clone(),
                        )?;
                        out.push(clause(
                            &refs,
                            base.clone(),
                            fn_graph(
                                "fcopysign_",
                                &[w_lit(w)?, left.clone(), right.clone()],
                                &singleton(copied)?,
                            )?,
                        ));

                        if left_kind == "nan" || right_kind == "nan" {
                            for (op, result) in [
                                ("feq_", 0),
                                ("fne_", 1),
                                ("flt_", 0),
                                ("fgt_", 0),
                                ("fle_", 0),
                                ("fge_", 0),
                            ] {
                                out.push(clause(
                                    &refs,
                                    base.clone(),
                                    float_comparison_concl(
                                        op,
                                        w,
                                        left.clone(),
                                        right.clone(),
                                        result,
                                    )?,
                                ));
                            }
                            for op in ["fpmin_", "fpmax_"] {
                                out.push(clause(
                                    &refs,
                                    base.clone(),
                                    float_selection_concl(
                                        op,
                                        w,
                                        left.clone(),
                                        right.clone(),
                                        left.clone(),
                                    )?,
                                ));
                            }
                            push_binary_nan_result_set(
                                &mut out,
                                &names,
                                &base,
                                w,
                                &left,
                                &right,
                                left_kind == "nan",
                                right_kind == "nan",
                            )?;
                            continue;
                        }

                        // IEEE identifies the two structural zero encodings.
                        if left_kind == "subnormal" && right_kind == "subnormal" {
                            let mut zero_sides = base.clone();
                            zero_sides.push(mv("a_m").equals(mk_nat(0u64))?);
                            zero_sides.push(mv("b_m").equals(mk_nat(0u64))?);
                            for (op, result) in [
                                ("feq_", 1),
                                ("fne_", 0),
                                ("flt_", 0),
                                ("fgt_", 0),
                                ("fle_", 1),
                                ("fge_", 1),
                            ] {
                                out.push(clause(
                                    &refs,
                                    zero_sides.clone(),
                                    float_comparison_concl(
                                        op,
                                        w,
                                        left.clone(),
                                        right.clone(),
                                        result,
                                    )?,
                                ));
                            }
                            for op in ["fpmin_", "fpmax_"] {
                                out.push(clause(
                                    &refs,
                                    zero_sides.clone(),
                                    float_selection_concl(
                                        op,
                                        w,
                                        left.clone(),
                                        right.clone(),
                                        left.clone(),
                                    )?,
                                ));
                            }
                            let min_zero = structural_float(
                                u64::from(left_sign == 1 || right_sign == 1),
                                app(
                                    con("case.SUBNORM"),
                                    app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
                                )?,
                            )?;
                            let max_zero = structural_float(
                                u64::from(left_sign == 1 && right_sign == 1),
                                app(
                                    con("case.SUBNORM"),
                                    app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
                                )?,
                            )?;
                            for (op, result) in [("fmin_", min_zero), ("fmax_", max_zero)] {
                                out.push(clause(
                                    &refs,
                                    zero_sides.clone(),
                                    float_selection_concl(
                                        op,
                                        w,
                                        left.clone(),
                                        right.clone(),
                                        result,
                                    )?,
                                ));
                            }
                        }

                        let left_key = float_order_key(w, left_sign, left_raw.clone())?;
                        let right_key = float_order_key(w, right_sign, right_raw.clone())?;
                        // Exclude the double-zero point from key comparison:
                        // its adjacent keys reflect bit order, not IEEE value
                        // equality. Two branches express `(a != 0 || b != 0)`
                        // without adding a disjunctive or opaque premise.
                        let nonzero_branches =
                            if left_kind == "subnormal" && right_kind == "subnormal" {
                                vec![lt(mk_nat(0u64), mv("a_m"))?, lt(mk_nat(0u64), mv("b_m"))?]
                            } else {
                                vec![mk_nat(0u64).equals(mk_nat(0u64))?]
                            };
                        for nz in nonzero_branches {
                            let mut branch = base.clone();
                            branch.push(nz);
                            let eq = left_key.clone().equals(right_key.clone())?;
                            let lt_lr = lt(left_key.clone(), right_key.clone())?;
                            let lt_rl = lt(right_key.clone(), left_key.clone())?;
                            let le_lr = le(left_key.clone(), right_key.clone())?;
                            let le_rl = le(right_key.clone(), left_key.clone())?;
                            for (op, result, guard) in [
                                ("feq_", 1, eq.clone()),
                                ("feq_", 0, lt_lr.clone()),
                                ("feq_", 0, lt_rl.clone()),
                                ("fne_", 0, eq),
                                ("fne_", 1, lt_lr.clone()),
                                ("fne_", 1, lt_rl.clone()),
                                ("flt_", 1, lt_lr.clone()),
                                ("flt_", 0, le_rl.clone()),
                                ("fgt_", 1, lt_rl.clone()),
                                ("fgt_", 0, le_lr.clone()),
                                ("fle_", 1, le_lr.clone()),
                                ("fle_", 0, lt_rl.clone()),
                                ("fge_", 1, le_rl.clone()),
                                ("fge_", 0, lt_lr.clone()),
                            ] {
                                push_float_comparison(
                                    &mut out, &names, &branch, op, w, &left, &right, result, guard,
                                )?;
                            }
                            for (op, result, guard) in [
                                ("fpmin_", &right, lt_rl.clone()),
                                ("fpmin_", &left, le_lr.clone()),
                                ("fpmax_", &right, lt_lr.clone()),
                                ("fpmax_", &left, le_rl.clone()),
                                ("fmin_", &right, lt_rl.clone()),
                                ("fmin_", &left, le_lr.clone()),
                                ("fmax_", &right, lt_lr.clone()),
                                ("fmax_", &left, le_rl.clone()),
                            ] {
                                push_float_selection(
                                    &mut out, &names, &branch, op, w, &left, &right, result, guard,
                                )?;
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}

fn float_unary_concl(op: &str, w: u64, input: Term, output: Term) -> Result<Term> {
    fn_graph(op, &[w_lit(w)?, input], &singleton(output)?)
}

fn push_unary_nan_result_set(
    out: &mut Vec<Clause>,
    op: &str,
    w: u64,
    input_sign: u64,
) -> Result<()> {
    let p = if w == 32 { 23 } else { 52 };
    let (_, input_sides, _, _, input, _) = float_case_named(w, input_sign, "nan", None, "src_")?;
    let canon = p2(p - 1)?;
    for output_sign in [0, 1] {
        let mut canonical = input_sides.clone();
        canonical.push(mv("src_m").equals(canon.clone())?);
        canonical.push(mv("dst_m").equals(canon.clone())?);
        out.push(clause(
            &["src_m", "dst_m"],
            canonical,
            float_unary_concl(
                op,
                w,
                input.clone(),
                structural_nan(output_sign, mv("dst_m"))?,
            )?,
        ));
        for noncanonical in [
            lt(mv("src_m"), canon.clone())?,
            lt(canon.clone(), mv("src_m"))?,
        ] {
            let mut arithmetic = input_sides.clone();
            arithmetic.push(noncanonical);
            arithmetic.push(le(canon.clone(), mv("dst_m"))?);
            arithmetic.push(lt(mv("dst_m"), p2(p)?)?);
            out.push(clause(
                &["src_m", "dst_m"],
                arithmetic,
                float_unary_concl(
                    op,
                    w,
                    input.clone(),
                    structural_nan(output_sign, mv("dst_m"))?,
                )?,
            ));
        }
    }
    Ok(())
}

fn signed_zero(sign: u64) -> Result<Term> {
    structural_float(
        sign,
        app(
            con("case.SUBNORM"),
            app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
        )?,
    )
}

fn signed_one(sign: u64) -> Result<Term> {
    structural_normal(sign, mk_nat(0u64), 0, mk_nat(0u64))
}

fn push_integral_float_result(
    out: &mut Vec<Clause>,
    op: &str,
    w: u64,
    sign: u64,
    exponent: u64,
    input: Term,
    sides: Vec<Term>,
    rounded_significand: Term,
) -> Result<()> {
    let p = if w == 32 { 23 } else { 52 };
    let limit = p2(p + 1)?;

    let mut no_carry = sides.clone();
    no_carry.push(lt(rounded_significand.clone(), limit.clone())?);
    no_carry.push(mv("dst_m").equals(sub(rounded_significand.clone(), p2(p)?)?)?);
    out.push(clause(
        &["src_m", "src_e", "dst_m"],
        no_carry,
        float_unary_concl(
            op,
            w,
            input.clone(),
            structural_normal(sign, mv("dst_m"), 0, mk_nat(exponent))?,
        )?,
    ));

    let mut carry = sides;
    carry.push(rounded_significand.equals(limit)?);
    out.push(clause(
        &["src_m", "src_e"],
        carry,
        float_unary_concl(
            op,
            w,
            input,
            structural_normal(sign, mk_nat(0u64), 0, mk_nat(exponent + 1))?,
        )?,
    ));
    Ok(())
}

/// Exact ceil/floor/trunc/nearest over the complete structural float carrier.
fn float_integral_rounding() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    let ops = ["fceil_", "ffloor_", "ftrunc_", "fnearest_"];
    for w in [32, 64] {
        let p = if w == 32 { 23 } else { 52 };
        for sign in [0, 1] {
            for op in ops {
                push_unary_nan_result_set(&mut out, op, w, sign)?;
            }

            let (names, sides, _, _, infinity, _) =
                float_case_named(w, sign, "infinity", None, "src_")?;
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            for op in ops {
                out.push(clause(
                    &refs,
                    sides.clone(),
                    float_unary_concl(op, w, infinity.clone(), infinity.clone())?,
                ));
            }

            let (names, sides, _, _, subnormal, _) =
                float_case_named(w, sign, "subnormal", None, "src_")?;
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            let mut zero = sides.clone();
            zero.push(mv("src_m").equals(mk_nat(0u64))?);
            for op in ops {
                out.push(clause(
                    &refs,
                    zero.clone(),
                    float_unary_concl(op, w, subnormal.clone(), subnormal.clone())?,
                ));
            }
            let mut nonzero = sides;
            nonzero.push(lt(mk_nat(0u64), mv("src_m"))?);
            for (op, result) in [
                (
                    "fceil_",
                    if sign == 0 {
                        signed_one(sign)?
                    } else {
                        signed_zero(sign)?
                    },
                ),
                (
                    "ffloor_",
                    if sign == 0 {
                        signed_zero(sign)?
                    } else {
                        signed_one(sign)?
                    },
                ),
                ("ftrunc_", signed_zero(sign)?),
                ("fnearest_", signed_zero(sign)?),
            ] {
                out.push(clause(
                    &refs,
                    nonzero.clone(),
                    float_unary_concl(op, w, subnormal.clone(), result)?,
                ));
            }

            let (_, neg_sides, _, _, negative_exp, _) =
                float_case_named(w, sign, "normal", Some(1), "src_")?;
            for (mantissa_guard, nearest) in [
                (mv("src_m").equals(mk_nat(0u64))?, signed_zero(sign)?),
                (lt(mk_nat(0u64), mv("src_m"))?, signed_one(sign)?),
            ] {
                let mut half = neg_sides.clone();
                half.push(mv("src_e").equals(mk_nat(1u64))?);
                half.push(mantissa_guard);
                for (op, result) in [
                    (
                        "fceil_",
                        if sign == 0 {
                            signed_one(sign)?
                        } else {
                            signed_zero(sign)?
                        },
                    ),
                    (
                        "ffloor_",
                        if sign == 0 {
                            signed_zero(sign)?
                        } else {
                            signed_one(sign)?
                        },
                    ),
                    ("ftrunc_", signed_zero(sign)?),
                    ("fnearest_", nearest),
                ] {
                    out.push(clause(
                        &["src_m", "src_e"],
                        half.clone(),
                        float_unary_concl(op, w, negative_exp.clone(), result)?,
                    ));
                }
            }
            let mut below_half = neg_sides;
            below_half.push(lt(mk_nat(1u64), mv("src_e"))?);
            for (op, result) in [
                (
                    "fceil_",
                    if sign == 0 {
                        signed_one(sign)?
                    } else {
                        signed_zero(sign)?
                    },
                ),
                (
                    "ffloor_",
                    if sign == 0 {
                        signed_zero(sign)?
                    } else {
                        signed_one(sign)?
                    },
                ),
                ("ftrunc_", signed_zero(sign)?),
                ("fnearest_", signed_zero(sign)?),
            ] {
                out.push(clause(
                    &["src_m", "src_e"],
                    below_half.clone(),
                    float_unary_concl(op, w, negative_exp.clone(), result)?,
                ));
            }

            let (_, pos_sides, _, _, positive_exp, _) =
                float_case_named(w, sign, "normal", Some(0), "src_")?;
            let mut already_integral = pos_sides.clone();
            already_integral.push(le(mk_nat(p), mv("src_e"))?);
            for op in ops {
                out.push(clause(
                    &["src_m", "src_e"],
                    already_integral.clone(),
                    float_unary_concl(op, w, positive_exp.clone(), positive_exp.clone())?,
                ));
            }

            for exponent in 0..p {
                let shift = p - exponent;
                let unit = p2(shift)?;
                let significand = add(p2(p)?, mv("src_m"))?;
                let q = div(significand.clone(), unit.clone())?;
                let rem = md(significand, unit.clone())?;
                let down = mul(q.clone(), unit.clone())?;
                let up = mul(add(q.clone(), mk_nat(1u64))?, unit)?;
                let mut base = pos_sides.clone();
                base.push(mv("src_e").equals(mk_nat(exponent))?);

                let mut exact = base.clone();
                exact.push(rem.clone().equals(mk_nat(0u64))?);
                for op in ["fceil_", "ffloor_", "ftrunc_"] {
                    push_integral_float_result(
                        &mut out,
                        op,
                        w,
                        sign,
                        exponent,
                        positive_exp.clone(),
                        exact.clone(),
                        down.clone(),
                    )?;
                }
                let mut fractional = base.clone();
                fractional.push(lt(mk_nat(0u64), rem.clone())?);
                for (op, rounded) in [
                    ("ftrunc_", down.clone()),
                    ("fceil_", if sign == 0 { up.clone() } else { down.clone() }),
                    ("ffloor_", if sign == 0 { down.clone() } else { up.clone() }),
                ] {
                    push_integral_float_result(
                        &mut out,
                        op,
                        w,
                        sign,
                        exponent,
                        positive_exp.clone(),
                        fractional.clone(),
                        rounded,
                    )?;
                }

                for (nearest_sides, rounded_q) in
                    round_ties_even_candidates(&base, q.clone(), rem, p2(shift - 1)?)?
                {
                    push_integral_float_result(
                        &mut out,
                        "fnearest_",
                        w,
                        sign,
                        exponent,
                        positive_exp.clone(),
                        nearest_sides,
                        mul(rounded_q, p2(shift)?)?,
                    )?;
                }
            }
        }
    }
    Ok(out)
}

/// Exact relational graphs for implementation/profile choice parameters.
///
/// These are deliberately relations, not deterministic defaults: every
/// value admitted by the source syntax is derivable, and no other value is.
/// A proof selects a concrete profile parameter by supplying the corresponding
/// graph fact; no host-global flag or hidden oracle enters the theorem.
fn choice_parameter_clauses() -> Result<Vec<Clause>> {
    let mut out = vec![
        clause(&[], vec![], fn_graph("ND", &[], &con("bool.false"))?),
        clause(&[], vec![], fn_graph("ND", &[], &con("bool.true"))?),
    ];
    for (op, cardinality) in [
        ("R_fmadd", 2u64),
        ("R_fmin", 4),
        ("R_fmax", 4),
        ("R_idot", 2),
        ("R_iq15mulr", 2),
        ("R_trunc_u", 4),
        ("R_trunc_s", 2),
        ("R_swizzle", 2),
        ("R_laneselect", 2),
    ] {
        for i in 0..cardinality {
            out.push(clause(
                &[],
                vec![],
                fn_graph(op, &[], &wrap_nat(mk_nat(i))?)?,
            ));
        }
    }
    Ok(out)
}

fn float_to_int_concl(
    op: &str,
    source_w: u64,
    target_w: u64,
    sx: &str,
    value: Term,
    result: Term,
) -> Result<Term> {
    fn_graph(
        op,
        &[w_lit(source_w)?, w_lit(target_w)?, sx_case(sx)?, value],
        &result,
    )
}

fn push_float_to_int_some(
    out: &mut Vec<Clause>,
    mut names: Vec<String>,
    mut sides: Vec<Term>,
    op: &str,
    source_w: u64,
    target_w: u64,
    sx: &str,
    value: Term,
    result: Term,
) -> Result<()> {
    names.push("r".to_owned());
    sides.push(mv("r").equals(result)?);
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    out.push(clause(
        &refs,
        sides,
        float_to_int_concl(op, source_w, target_w, sx, value, some(ival(mv("r"))?)?)?,
    ));
    Ok(())
}

fn push_float_to_int_none(
    out: &mut Vec<Clause>,
    names: Vec<String>,
    sides: Vec<Term>,
    source_w: u64,
    target_w: u64,
    sx: &str,
    value: Term,
) -> Result<()> {
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    out.push(clause(
        &refs,
        sides,
        float_to_int_concl("trunc__", source_w, target_w, sx, value, con("opt.none"))?,
    ));
    Ok(())
}

/// Exact trapping and saturating float-to-integer conversions.
///
/// A normal finite magnitude is `(2^M + m) * 2^(e-M)`. Splitting at `e=M`
/// keeps that expression in natural arithmetic. NaNs/infinities and every
/// target-range boundary are explicit; no host float or rational oracle is
/// involved.
fn float_to_integer_conversions() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for source_w in [32, 64] {
        let m_bits = if source_w == 32 { 23 } else { 52 };
        for target_w in [32, 64] {
            for sx in ["U", "S"] {
                for sign in [0, 1] {
                    for (kind, exp_sign) in FLOAT_SHAPES {
                        let (names, sides, _, _magnitude, value, _raw) =
                            float_case_named(source_w, sign, kind, exp_sign, "")?;
                        let unsigned_limit = p2(target_w)?;
                        let signed_limit = p2(target_w - 1)?;
                        match kind {
                            "nan" => {
                                push_float_to_int_none(
                                    &mut out,
                                    names.clone(),
                                    sides.clone(),
                                    source_w,
                                    target_w,
                                    sx,
                                    value.clone(),
                                )?;
                                push_float_to_int_some(
                                    &mut out,
                                    names,
                                    sides,
                                    "trunc_sat__",
                                    source_w,
                                    target_w,
                                    sx,
                                    value,
                                    mk_nat(0u64),
                                )?;
                            }
                            "infinity" => {
                                push_float_to_int_none(
                                    &mut out,
                                    names.clone(),
                                    sides.clone(),
                                    source_w,
                                    target_w,
                                    sx,
                                    value.clone(),
                                )?;
                                let saturated = match (sx, sign) {
                                    ("U", 0) => sub(unsigned_limit, mk_nat(1u64))?,
                                    ("U", 1) => mk_nat(0u64),
                                    ("S", 0) => sub(signed_limit, mk_nat(1u64))?,
                                    ("S", 1) => signed_limit,
                                    _ => unreachable!(),
                                };
                                push_float_to_int_some(
                                    &mut out,
                                    names,
                                    sides,
                                    "trunc_sat__",
                                    source_w,
                                    target_w,
                                    sx,
                                    value,
                                    saturated,
                                )?;
                            }
                            "subnormal" => {
                                // Every subnormal and every normal with a
                                // negative exponent truncates to signed zero.
                                push_float_to_int_some(
                                    &mut out,
                                    names.clone(),
                                    sides.clone(),
                                    "trunc__",
                                    source_w,
                                    target_w,
                                    sx,
                                    value.clone(),
                                    mk_nat(0u64),
                                )?;
                                push_float_to_int_some(
                                    &mut out,
                                    names,
                                    sides,
                                    "trunc_sat__",
                                    source_w,
                                    target_w,
                                    sx,
                                    value,
                                    mk_nat(0u64),
                                )?;
                            }
                            "normal" if exp_sign == Some(1) => {
                                push_float_to_int_some(
                                    &mut out,
                                    names.clone(),
                                    sides.clone(),
                                    "trunc__",
                                    source_w,
                                    target_w,
                                    sx,
                                    value.clone(),
                                    mk_nat(0u64),
                                )?;
                                push_float_to_int_some(
                                    &mut out,
                                    names,
                                    sides,
                                    "trunc_sat__",
                                    source_w,
                                    target_w,
                                    sx,
                                    value,
                                    mk_nat(0u64),
                                )?;
                            }
                            "normal" => {
                                for (mut mag_sides, mag) in [
                                    (
                                        vec![le(mv("e"), mk_nat(m_bits))?],
                                        div(
                                            add(p2(m_bits)?, mv("m"))?,
                                            pow2(sub(mk_nat(m_bits), mv("e"))?)?,
                                        )?,
                                    ),
                                    (
                                        vec![lt(mk_nat(m_bits), mv("e"))?],
                                        mul(
                                            add(p2(m_bits)?, mv("m"))?,
                                            pow2(sub(mv("e"), mk_nat(m_bits))?)?,
                                        )?,
                                    ),
                                ] {
                                    mag_sides.extend(sides.clone());
                                    let limit = if sx == "U" {
                                        unsigned_limit.clone()
                                    } else {
                                        signed_limit.clone()
                                    };
                                    if sign == 0 {
                                        let mut fits = mag_sides.clone();
                                        fits.push(lt(mag.clone(), limit.clone())?);
                                        for op in ["trunc__", "trunc_sat__"] {
                                            push_float_to_int_some(
                                                &mut out,
                                                names.clone(),
                                                fits.clone(),
                                                op,
                                                source_w,
                                                target_w,
                                                sx,
                                                value.clone(),
                                                mag.clone(),
                                            )?;
                                        }
                                        let mut overflow = mag_sides.clone();
                                        overflow.push(le(limit.clone(), mag.clone())?);
                                        push_float_to_int_none(
                                            &mut out,
                                            names.clone(),
                                            overflow.clone(),
                                            source_w,
                                            target_w,
                                            sx,
                                            value.clone(),
                                        )?;
                                        push_float_to_int_some(
                                            &mut out,
                                            names.clone(),
                                            overflow,
                                            "trunc_sat__",
                                            source_w,
                                            target_w,
                                            sx,
                                            value.clone(),
                                            sub(limit, mk_nat(1u64))?,
                                        )?;
                                    } else if sx == "U" {
                                        push_float_to_int_none(
                                            &mut out,
                                            names.clone(),
                                            mag_sides.clone(),
                                            source_w,
                                            target_w,
                                            sx,
                                            value.clone(),
                                        )?;
                                        push_float_to_int_some(
                                            &mut out,
                                            names.clone(),
                                            mag_sides,
                                            "trunc_sat__",
                                            source_w,
                                            target_w,
                                            sx,
                                            value.clone(),
                                            mk_nat(0u64),
                                        )?;
                                    } else {
                                        let mut fits = mag_sides.clone();
                                        fits.push(le(mag.clone(), signed_limit.clone())?);
                                        let encoded =
                                            md(sub(p2(target_w)?, mag.clone())?, p2(target_w)?)?;
                                        for op in ["trunc__", "trunc_sat__"] {
                                            push_float_to_int_some(
                                                &mut out,
                                                names.clone(),
                                                fits.clone(),
                                                op,
                                                source_w,
                                                target_w,
                                                sx,
                                                value.clone(),
                                                encoded.clone(),
                                            )?;
                                        }
                                        let mut overflow = mag_sides.clone();
                                        overflow.push(lt(signed_limit.clone(), mag)?);
                                        push_float_to_int_none(
                                            &mut out,
                                            names.clone(),
                                            overflow.clone(),
                                            source_w,
                                            target_w,
                                            sx,
                                            value.clone(),
                                        )?;
                                        push_float_to_int_some(
                                            &mut out,
                                            names.clone(),
                                            overflow,
                                            "trunc_sat__",
                                            source_w,
                                            target_w,
                                            sx,
                                            value.clone(),
                                            signed_limit.clone(),
                                        )?;
                                    }
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}

fn int_to_float_concl(
    source_w: u64,
    target_w: u64,
    sx: &str,
    input: Term,
    output: Term,
) -> Result<Term> {
    fn_graph(
        "convert__",
        &[
            w_lit(source_w)?,
            w_lit(target_w)?,
            sx_case(sx)?,
            ival(input)?,
        ],
        &output,
    )
}

fn normal_float(sign: u64, exponent: u64, mantissa: Term) -> Result<Term> {
    let payload = app(
        app(con("tup"), wrap_nat(mantissa)?)?,
        wrap_int(0, mk_nat(exponent))?,
    )?;
    app(
        con(if sign == 0 { "case.POS" } else { "case.NEG" }),
        app(con("case.NORM"), payload)?,
    )
}

fn push_int_to_float(
    out: &mut Vec<Clause>,
    mut sides: Vec<Term>,
    source_w: u64,
    target_w: u64,
    sx: &str,
    sign: u64,
    exponent: u64,
    mantissa: Term,
) -> Result<()> {
    sides.push(mv("out_m").equals(mantissa)?);
    out.push(clause(
        &["a", "out_m"],
        sides,
        int_to_float_concl(
            source_w,
            target_w,
            sx,
            mv("a"),
            normal_float(sign, exponent, mv("out_m"))?,
        )?,
    ));
    Ok(())
}

/// Exact integer-to-float conversion with IEEE round-to-nearest,
/// ties-to-even. Source magnitudes are partitioned by their unique top bit.
/// When precision is insufficient, quotient/remainder and quotient parity
/// select the lower/upper candidate; a rounded significand carry increments
/// the exponent.
fn integer_to_float_conversions() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for source_w in [32, 64] {
        for target_w in [32, 64] {
            let p = if target_w == 32 { 23 } else { 52 };
            for sx in ["U", "S"] {
                let sign_classes: &[u64] = if sx == "U" { &[0] } else { &[0, 1] };
                for &sign in sign_classes {
                    let mut zero_sides = vec![mv("a").equals(mk_nat(0u64))?];
                    if sx == "S" && sign == 1 {
                        // There is no negative integer zero.
                        continue;
                    }
                    zero_sides.push(in_carrier(mv("a"), source_w)?);
                    out.push(clause(
                        &["a"],
                        zero_sides,
                        int_to_float_concl(
                            source_w,
                            target_w,
                            sx,
                            mv("a"),
                            app(
                                con("case.POS"),
                                app(
                                    con("case.SUBNORM"),
                                    app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
                                )?,
                            )?,
                        )?,
                    ));
                }

                for sign in sign_classes.iter().copied() {
                    let mag = if sign == 0 {
                        mv("a")
                    } else {
                        sub(p2(source_w)?, mv("a"))?
                    };
                    let mut class = vec![in_carrier(mv("a"), source_w)?];
                    if sx == "S" {
                        if sign == 0 {
                            class.push(lt(mv("a"), p2(source_w - 1)?)?);
                        } else {
                            class.push(le(p2(source_w - 1)?, mv("a"))?);
                        }
                    }
                    for k in 0..source_w {
                        let mut top_bit = class.clone();
                        top_bit.push(le(p2(k)?, mag.clone())?);
                        top_bit.push(lt(mag.clone(), p2(k + 1)?)?);
                        if k <= p {
                            let mantissa = mul(sub(mag.clone(), p2(k)?)?, p2(p - k)?)?;
                            push_int_to_float(
                                &mut out, top_bit, source_w, target_w, sx, sign, k, mantissa,
                            )?;
                            continue;
                        }

                        let shift = k - p;
                        let unit = p2(shift)?;
                        let half = p2(shift - 1)?;
                        let q = div(mag.clone(), unit.clone())?;
                        let rem = md(mag.clone(), unit)?;
                        let limit = p2(p + 1)?;

                        // Below half, and an even exact tie, round down.
                        for mut round_down in [
                            {
                                let mut s = top_bit.clone();
                                s.push(lt(rem.clone(), half.clone())?);
                                s
                            },
                            {
                                let mut s = top_bit.clone();
                                s.push(rem.clone().equals(half.clone())?);
                                s.push(md(q.clone(), mk_nat(2u64))?.equals(mk_nat(0u64))?);
                                s
                            },
                        ] {
                            round_down.push(lt(q.clone(), limit.clone())?);
                            push_int_to_float(
                                &mut out,
                                round_down,
                                source_w,
                                target_w,
                                sx,
                                sign,
                                k,
                                sub(q.clone(), p2(p)?)?,
                            )?;
                        }

                        // Above half, and an odd exact tie, round up. Split
                        // the significand carry because it increments `e`.
                        for round_up in [
                            {
                                let mut s = top_bit.clone();
                                s.push(lt(half.clone(), rem.clone())?);
                                s
                            },
                            {
                                let mut s = top_bit.clone();
                                s.push(rem.clone().equals(half.clone())?);
                                s.push(md(q.clone(), mk_nat(2u64))?.equals(mk_nat(1u64))?);
                                s
                            },
                        ] {
                            let rounded = add(q.clone(), mk_nat(1u64))?;
                            let mut no_carry = round_up.clone();
                            no_carry.push(lt(rounded.clone(), limit.clone())?);
                            push_int_to_float(
                                &mut out,
                                no_carry,
                                source_w,
                                target_w,
                                sx,
                                sign,
                                k,
                                sub(rounded.clone(), p2(p)?)?,
                            )?;
                            let mut carry = round_up;
                            carry.push(rounded.equals(limit.clone())?);
                            push_int_to_float(
                                &mut out,
                                carry,
                                source_w,
                                target_w,
                                sx,
                                sign,
                                k + 1,
                                mk_nat(0u64),
                            )?;
                        }
                    }
                }
            }
        }
    }
    Ok(out)
}

fn float_width_conversion_concl(
    op: &str,
    source_w: u64,
    target_w: u64,
    input: Term,
    output: Term,
) -> Result<Term> {
    fn_graph(
        op,
        &[w_lit(source_w)?, w_lit(target_w)?, input],
        &singleton(output)?,
    )
}

fn structural_float(sign: u64, magnitude: Term) -> Result<Term> {
    app(
        con(if sign == 0 { "case.POS" } else { "case.NEG" }),
        magnitude,
    )
}

fn structural_normal(sign: u64, mantissa: Term, exp_sign: u64, exponent: Term) -> Result<Term> {
    structural_float(
        sign,
        app(
            con("case.NORM"),
            app(
                app(con("tup"), wrap_nat(mantissa)?)?,
                wrap_int(exp_sign, exponent)?,
            )?,
        )?,
    )
}

fn structural_nan(sign: u64, payload: Term) -> Result<Term> {
    structural_float(
        sign,
        app(con("case.NAN"), app(con("tup"), wrap_nat(payload)?)?)?,
    )
}

/// Add the complete `nans_N` result relation for one NaN input.
///
/// Clause precedence in the numeric specification distinguishes canonical
/// payloads from all other arithmetic payloads. A canonical input admits both
/// signs of exactly `canon_N`; a noncanonical arithmetic input admits both
/// signs and every target payload in `[canon_N, 2^signif(N))`. The quantified
/// output payload is constrained by kernel natural order, so this represents
/// the full family without enumeration or representative selection.
fn push_nan_result_set(
    out: &mut Vec<Clause>,
    op: &str,
    source_w: u64,
    target_w: u64,
    input_sign: u64,
) -> Result<()> {
    let source_p = if source_w == 32 { 23 } else { 52 };
    let target_p = if target_w == 32 { 23 } else { 52 };
    let (_, input_sides, _, _, input, _) =
        float_case_named(source_w, input_sign, "nan", None, "src_")?;
    let source_canon = p2(source_p - 1)?;
    let target_canon = p2(target_p - 1)?;

    for output_sign in [0, 1] {
        let mut canonical = input_sides.clone();
        canonical.push(mv("src_m").equals(source_canon.clone())?);
        canonical.push(mv("dst_m").equals(target_canon.clone())?);
        out.push(clause(
            &["src_m", "dst_m"],
            canonical,
            float_width_conversion_concl(
                op,
                source_w,
                target_w,
                input.clone(),
                structural_nan(output_sign, mv("dst_m"))?,
            )?,
        ));

        for source_noncanonical in [
            lt(mv("src_m"), source_canon.clone())?,
            lt(source_canon.clone(), mv("src_m"))?,
        ] {
            let mut arithmetic = input_sides.clone();
            arithmetic.push(source_noncanonical);
            arithmetic.push(le(target_canon.clone(), mv("dst_m"))?);
            arithmetic.push(lt(mv("dst_m"), p2(target_p)?)?);
            out.push(clause(
                &["src_m", "dst_m"],
                arithmetic,
                float_width_conversion_concl(
                    op,
                    source_w,
                    target_w,
                    input.clone(),
                    structural_nan(output_sign, mv("dst_m"))?,
                )?,
            ));
        }
    }
    Ok(())
}

/// Exact F32-to-F64 promotion over the complete structural carrier.
///
/// Every finite F32 value is exactly representable at F64. Normal values keep
/// their unbiased exponent and shift the significand payload by 29 bits.
/// Nonzero subnormals are normalized by their unique top bit; signed zero and
/// infinities preserve their constructors. NaNs use the quantified result-set
/// relation above and therefore retain all source-permitted nondeterminism.
fn float_promotion() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for sign in [0, 1] {
        let (names, sides, _, _, input, _) = float_case_named(32, sign, "subnormal", None, "src_")?;
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let mut zero = sides.clone();
        zero.push(mv("src_m").equals(mk_nat(0u64))?);
        out.push(clause(
            &refs,
            zero,
            float_width_conversion_concl(
                "promote__",
                32,
                64,
                input.clone(),
                structural_float(
                    sign,
                    app(
                        con("case.SUBNORM"),
                        app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
                    )?,
                )?,
            )?,
        ));
        for k in 0..23 {
            let mut branch = sides.clone();
            branch.push(le(p2(k)?, mv("src_m"))?);
            branch.push(lt(mv("src_m"), p2(k + 1)?)?);
            branch.push(mv("dst_m").equals(mul(sub(mv("src_m"), p2(k)?)?, p2(52 - k)?)?)?);
            out.push(clause(
                &["src_m", "dst_m"],
                branch,
                float_width_conversion_concl(
                    "promote__",
                    32,
                    64,
                    input.clone(),
                    structural_normal(sign, mv("dst_m"), 1, mk_nat(149 - k))?,
                )?,
            ));
        }

        for exp_sign in [0, 1] {
            let (names, sides, _, _, input, _) =
                float_case_named(32, sign, "normal", Some(exp_sign), "src_")?;
            let mut names = names;
            names.push("dst_m".to_owned());
            let mut sides = sides;
            sides.push(mv("dst_m").equals(mul(mv("src_m"), p2(29)?)?)?);
            let refs: Vec<&str> = names.iter().map(String::as_str).collect();
            out.push(clause(
                &refs,
                sides,
                float_width_conversion_concl(
                    "promote__",
                    32,
                    64,
                    input,
                    structural_normal(sign, mv("dst_m"), exp_sign, mv("src_e"))?,
                )?,
            ));
        }

        let (names, sides, _, _, input, _) = float_case_named(32, sign, "infinity", None, "src_")?;
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        out.push(clause(
            &refs,
            sides,
            float_width_conversion_concl(
                "promote__",
                32,
                64,
                input,
                structural_float(sign, app(con("case.INF"), con("tup"))?)?,
            )?,
        ));

        push_nan_result_set(&mut out, "promote__", 32, 64, sign)?;
    }
    Ok(out)
}

fn round_ties_even_candidates(
    base: &[Term],
    quotient: Term,
    remainder: Term,
    half: Term,
) -> Result<Vec<(Vec<Term>, Term)>> {
    let mut below = base.to_vec();
    below.push(lt(remainder.clone(), half.clone())?);
    let mut even_tie = base.to_vec();
    even_tie.push(remainder.clone().equals(half.clone())?);
    even_tie.push(md(quotient.clone(), mk_nat(2u64))?.equals(mk_nat(0u64))?);
    let mut above = base.to_vec();
    above.push(lt(half.clone(), remainder.clone())?);
    let mut odd_tie = base.to_vec();
    odd_tie.push(remainder.equals(half)?);
    odd_tie.push(md(quotient.clone(), mk_nat(2u64))?.equals(mk_nat(1u64))?);
    let upper = add(quotient.clone(), mk_nat(1u64))?;
    Ok(vec![
        (below, quotient.clone()),
        (even_tie, quotient),
        (above, upper.clone()),
        (odd_tie, upper),
    ])
}

fn push_demote_normal(
    out: &mut Vec<Clause>,
    mut sides: Vec<Term>,
    input: Term,
    sign: u64,
    exp_sign: u64,
    exponent: Term,
    rounded: Term,
) -> Result<()> {
    sides.push(lt(rounded.clone(), p2(24)?)?);
    sides.push(mv("dst_m").equals(sub(rounded, p2(23)?)?)?);
    out.push(clause(
        &["src_m", "src_e", "dst_m"],
        sides,
        float_width_conversion_concl(
            "demote__",
            64,
            32,
            input,
            structural_normal(sign, mv("dst_m"), exp_sign, exponent)?,
        )?,
    ));
    Ok(())
}

/// Exact F64-to-F32 demotion with round-to-nearest, ties-to-even.
///
/// The normal-target corridor discards 29 significand bits. The subnormal
/// corridor scales by the exact F32 quantum `2^-149`, using the source
/// exponent to form a kernel-reducible quotient/remainder unit. Explicit
/// carry branches reach the adjacent exponent, minimum normal, or infinity.
/// Values below half the minimum subnormal become signed zero; all F64
/// subnormals are in that region. NaNs preserve the complete `nans_N` family.
fn float_demotion() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for sign in [0, 1] {
        let (names, sides, _, _, input, _) = float_case_named(64, sign, "subnormal", None, "src_")?;
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        out.push(clause(
            &refs,
            sides,
            float_width_conversion_concl(
                "demote__",
                64,
                32,
                input,
                structural_float(
                    sign,
                    app(
                        con("case.SUBNORM"),
                        app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
                    )?,
                )?,
            )?,
        ));

        // Nonnegative source exponents: normal F32 through e=127, then
        // overflow. Rounding carry at e=127 is exactly the infinity boundary.
        let (_, pos_sides, _, _, pos_input, _) =
            float_case_named(64, sign, "normal", Some(0), "src_")?;
        let significand = add(p2(52)?, mv("src_m"))?;
        let unit = p2(29)?;
        let q = div(significand.clone(), unit.clone())?;
        let rem = md(significand, unit)?;
        for (mut rounded_sides, rounded) in round_ties_even_candidates(&pos_sides, q, rem, p2(28)?)?
        {
            rounded_sides.push(le(mv("src_e"), mk_nat(127u64))?);
            push_demote_normal(
                &mut out,
                rounded_sides.clone(),
                pos_input.clone(),
                sign,
                0,
                mv("src_e"),
                rounded.clone(),
            )?;

            let mut carry_normal = rounded_sides.clone();
            carry_normal.push(lt(mv("src_e"), mk_nat(127u64))?);
            carry_normal.push(rounded.clone().equals(p2(24)?)?);
            carry_normal.push(mv("dst_e").equals(add(mv("src_e"), mk_nat(1u64))?)?);
            out.push(clause(
                &["src_m", "src_e", "dst_e"],
                carry_normal,
                float_width_conversion_concl(
                    "demote__",
                    64,
                    32,
                    pos_input.clone(),
                    structural_normal(sign, mk_nat(0u64), 0, mv("dst_e"))?,
                )?,
            ));

            let mut carry_inf = rounded_sides;
            carry_inf.push(mv("src_e").equals(mk_nat(127u64))?);
            carry_inf.push(rounded.equals(p2(24)?)?);
            out.push(clause(
                &["src_m", "src_e"],
                carry_inf,
                float_width_conversion_concl(
                    "demote__",
                    64,
                    32,
                    pos_input.clone(),
                    structural_float(sign, app(con("case.INF"), con("tup"))?)?,
                )?,
            ));
        }
        let mut overflow = pos_sides;
        overflow.push(lt(mk_nat(127u64), mv("src_e"))?);
        out.push(clause(
            &["src_m", "src_e"],
            overflow,
            float_width_conversion_concl(
                "demote__",
                64,
                32,
                pos_input,
                structural_float(sign, app(con("case.INF"), con("tup"))?)?,
            )?,
        ));

        let (_, neg_sides, _, _, neg_input, _) =
            float_case_named(64, sign, "normal", Some(1), "src_")?;

        // Exponents -1 through -126 still produce normal F32 values.
        let significand = add(p2(52)?, mv("src_m"))?;
        let unit = p2(29)?;
        let q = div(significand.clone(), unit.clone())?;
        let rem = md(significand, unit)?;
        for (mut rounded_sides, rounded) in round_ties_even_candidates(&neg_sides, q, rem, p2(28)?)?
        {
            rounded_sides.push(le(mv("src_e"), mk_nat(126u64))?);
            push_demote_normal(
                &mut out,
                rounded_sides.clone(),
                neg_input.clone(),
                sign,
                1,
                mv("src_e"),
                rounded.clone(),
            )?;

            let mut carry_to_zero = rounded_sides.clone();
            carry_to_zero.push(mv("src_e").equals(mk_nat(1u64))?);
            carry_to_zero.push(rounded.clone().equals(p2(24)?)?);
            out.push(clause(
                &["src_m", "src_e"],
                carry_to_zero,
                float_width_conversion_concl(
                    "demote__",
                    64,
                    32,
                    neg_input.clone(),
                    structural_normal(sign, mk_nat(0u64), 0, mk_nat(0u64))?,
                )?,
            ));

            let mut carry_negative = rounded_sides;
            carry_negative.push(lt(mk_nat(1u64), mv("src_e"))?);
            carry_negative.push(rounded.equals(p2(24)?)?);
            carry_negative.push(mv("dst_e").equals(sub(mv("src_e"), mk_nat(1u64))?)?);
            out.push(clause(
                &["src_m", "src_e", "dst_e"],
                carry_negative,
                float_width_conversion_concl(
                    "demote__",
                    64,
                    32,
                    neg_input.clone(),
                    structural_normal(sign, mk_nat(0u64), 1, mv("dst_e"))?,
                )?,
            ));
        }

        // Exponents -127 through -150 round in units of the F32 minimum
        // subnormal. A carry at the top of this corridor is minimum normal.
        let mut corridor = neg_sides.clone();
        corridor.push(le(mk_nat(127u64), mv("src_e"))?);
        corridor.push(le(mv("src_e"), mk_nat(150u64))?);
        let shift = sub(mv("src_e"), mk_nat(97u64))?;
        let unit = pow2(shift.clone())?;
        let q = div(add(p2(52)?, mv("src_m"))?, unit.clone())?;
        let rem = md(add(p2(52)?, mv("src_m"))?, unit)?;
        let half = pow2(sub(shift, mk_nat(1u64))?)?;
        for (mut rounded_sides, rounded) in round_ties_even_candidates(&corridor, q, rem, half)? {
            let mut subnormal = rounded_sides.clone();
            subnormal.push(lt(rounded.clone(), p2(23)?)?);
            subnormal.push(mv("dst_m").equals(rounded.clone())?);
            out.push(clause(
                &["src_m", "src_e", "dst_m"],
                subnormal,
                float_width_conversion_concl(
                    "demote__",
                    64,
                    32,
                    neg_input.clone(),
                    structural_float(
                        sign,
                        app(
                            con("case.SUBNORM"),
                            app(con("tup"), wrap_nat(mv("dst_m"))?)?,
                        )?,
                    )?,
                )?,
            ));

            rounded_sides.push(rounded.equals(p2(23)?)?);
            out.push(clause(
                &["src_m", "src_e"],
                rounded_sides,
                float_width_conversion_concl(
                    "demote__",
                    64,
                    32,
                    neg_input.clone(),
                    structural_normal(sign, mk_nat(0u64), 1, mk_nat(126u64))?,
                )?,
            ));
        }

        let mut underflow = neg_sides;
        underflow.push(lt(mk_nat(150u64), mv("src_e"))?);
        out.push(clause(
            &["src_m", "src_e"],
            underflow,
            float_width_conversion_concl(
                "demote__",
                64,
                32,
                neg_input,
                structural_float(
                    sign,
                    app(
                        con("case.SUBNORM"),
                        app(con("tup"), wrap_nat(mk_nat(0u64))?)?,
                    )?,
                )?,
            )?,
        ));

        let (names, sides, _, _, input, _) = float_case_named(64, sign, "infinity", None, "src_")?;
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        out.push(clause(
            &refs,
            sides,
            float_width_conversion_concl(
                "demote__",
                64,
                32,
                input,
                structural_float(sign, app(con("case.INF"), con("tup"))?)?,
            )?,
        ));
        push_nan_result_set(&mut out, "demote__", 64, 32, sign)?;
    }
    Ok(out)
}

/// Exact byte serialization for the composite numeric, vector, storage, and
/// constant-type front doors.
///
/// These builtins are type-directed wrappers around the primitive fixed-width
/// byte representation.  We spell out only the integer/vector cases whose
/// carrier is the exact unsigned `%` representation already used by
/// [`integer_serialization`]. This is pinned by the corpus itself:
/// `1.1-syntax.values.spectec` defines both `iN(N)` and `vN(N)` as `uN(N)`,
/// while `1.3-syntax.instructions.spectec` routes `num_(Inn)`, `vec_(Vnn)`,
/// and the integer/vector `lit_` branches to those carriers. The `case.I*` /
/// `case.V128` tags are the ordinary coproduct encoding used by the lowered
/// type arguments at the real load/store and array-data call sites.
/// Float cases deliberately receive no clause:
/// matching their distinct structural carrier as an integer would erase the
/// representation and silently invent float semantics.
fn composite_byte_serialization(
    op: &str,
    inverse: bool,
    type_case: &str,
    w: u64,
) -> Result<Clause> {
    debug_assert_eq!(w % 8, 0);
    let ids: Vec<String> = (0..w / 8).map(|i| format!("e{i}")).collect();
    let mut metavars = vec!["a".to_owned()];
    metavars.extend(ids.iter().cloned());
    let mut sides = vec![in_carrier(mv("a"), w)?];
    let base = p2(8)?;
    for (i, id) in ids.iter().enumerate() {
        sides.push(lt(mv(id), base.clone())?);
        if !inverse {
            sides.push(mv(id).equals(md(div(mv("a"), p2(8 * i as u64)?)?, base.clone())?)?);
        }
    }
    if inverse {
        let rebuilt = sum(ids
            .iter()
            .enumerate()
            .map(|(i, id)| Ok(mul(mv(id), p2(8 * i as u64)?)?)))?;
        sides.push(mv("a").equals(rebuilt)?);
    }
    let bytes = encoded_nat_list(&ids)?;
    let ty = app(con(format!("case.{type_case}")), con("tup"))?;
    let (args, result) = if inverse {
        (vec![ty, bytes], ival(mv("a"))?)
    } else {
        (vec![ty, ival(mv("a"))?], bytes)
    };
    let names: Vec<&str> = metavars.iter().map(String::as_str).collect();
    Ok(clause(&names, sides, fn_graph(op, &args, &result)?))
}

/// Every deterministic integer/vector branch of the four composite byte
/// families. Their float branches remain explicitly absent.
fn composite_byte_serializations() -> Result<Vec<Clause>> {
    let mut out = Vec::new();
    for (op, inverse, shapes) in [
        ("nbytes_", false, &[("I32", 32), ("I64", 64)][..]),
        ("inv_nbytes_", true, &[("I32", 32), ("I64", 64)][..]),
        ("vbytes_", false, &[("V128", 128)][..]),
        ("inv_vbytes_", true, &[("V128", 128)][..]),
        (
            "zbytes_",
            false,
            &[
                ("I8", 8),
                ("I16", 16),
                ("I32", 32),
                ("I64", 64),
                ("V128", 128),
            ][..],
        ),
        (
            "inv_zbytes_",
            true,
            &[
                ("I8", 8),
                ("I16", 16),
                ("I32", 32),
                ("I64", 64),
                ("V128", 128),
            ][..],
        ),
        (
            "cbytes_",
            false,
            &[("I32", 32), ("I64", 64), ("V128", 128)][..],
        ),
        (
            "inv_cbytes_",
            true,
            &[("I32", 32), ("I64", 64), ("V128", 128)][..],
        ),
    ] {
        for &(shape, w) in shapes {
            out.push(composite_byte_serialization(op, inverse, shape, w)?);
        }
    }
    Ok(out)
}

/// `mag(x)` for the negative sign class: `2^w − x`.
fn neg_mag(x: Term, w: u64) -> Result<Term> {
    sub(p2(w)?, x)
}

/// Negate a quotient/remainder magnitude back into the carrier:
/// `(2^w − m) mod 2^w` (the `mod` maps `m = 0` to `0`).
fn neg_result(m: Term, w: u64) -> Result<Term> {
    md(sub(p2(w)?, m)?, p2(w)?)
}

/// `idiv_` — partial (option results); by-zero stays with the spec's own
/// ground eps clauses (all clauses here carry `0 < b`-class guards).
fn idiv(w: u64) -> Result<Vec<Clause>> {
    let some_r = some(ival(mv("r"))?)?;
    let carrier =
        || -> Result<(Term, Term)> { Ok((in_carrier(mv("a"), w)?, in_carrier(mv("b"), w)?)) };
    let mut out = Vec::new();
    // U: r = a div b, b ≠ 0.
    let (ga, gb) = carrier()?;
    out.push(clause(
        &["a", "b", "r"],
        vec![
            ga,
            gb,
            lt(mk_nat(0u64), mv("b"))?,
            mv("r").equals(div(mv("a"), mv("b"))?)?,
        ],
        sx_concl("idiv_", w, "U", "a", "b", some_r.clone())?,
    ));
    // S, both nonnegative: r = a div b.
    out.push(clause(
        &["a", "b", "r"],
        vec![
            lt(mv("a"), p2(w - 1)?)?,
            lt(mv("b"), p2(w - 1)?)?,
            lt(mk_nat(0u64), mv("b"))?,
            mv("r").equals(div(mv("a"), mv("b"))?)?,
        ],
        sx_concl("idiv_", w, "S", "a", "b", some_r.clone())?,
    ));
    // S, both negative, no overflow: r = mag(a) div mag(b) with r < 2^(w−1).
    let q = div(neg_mag(mv("a"), w)?, neg_mag(mv("b"), w)?)?;
    let (ga, gb) = carrier()?;
    out.push(clause(
        &["a", "b", "r"],
        vec![
            ga.clone(),
            gb.clone(),
            le(p2(w - 1)?, mv("a"))?,
            le(p2(w - 1)?, mv("b"))?,
            mv("r").equals(q.clone())?,
            lt(mv("r"), p2(w - 1)?)?,
        ],
        sx_concl("idiv_", w, "S", "a", "b", some_r.clone())?,
    ));
    // S, both negative, overflow (`INT_MIN div −1`: q = 2^(w−1),
    // unrepresentable): eps.
    let (ga, gb) = carrier()?;
    out.push(clause(
        &["a", "b"],
        vec![
            ga,
            gb,
            le(p2(w - 1)?, mv("a"))?,
            le(p2(w - 1)?, mv("b"))?,
            q.equals(p2(w - 1)?)?,
        ],
        sx_concl("idiv_", w, "S", "a", "b", con("opt.none"))?,
    ));
    // S, nonneg / neg: r = −(a div mag(b)).
    let (ga, gb) = carrier()?;
    out.push(clause(
        &["a", "b", "r"],
        vec![
            ga,
            gb,
            lt(mv("a"), p2(w - 1)?)?,
            le(p2(w - 1)?, mv("b"))?,
            mv("r").equals(neg_result(div(mv("a"), neg_mag(mv("b"), w)?)?, w)?)?,
        ],
        sx_concl("idiv_", w, "S", "a", "b", some_r.clone())?,
    ));
    // S, neg / nonneg: r = −(mag(a) div b), b ≠ 0.
    let (ga, gb) = carrier()?;
    out.push(clause(
        &["a", "b", "r"],
        vec![
            ga,
            gb,
            le(p2(w - 1)?, mv("a"))?,
            lt(mv("b"), p2(w - 1)?)?,
            lt(mk_nat(0u64), mv("b"))?,
            mv("r").equals(neg_result(div(neg_mag(mv("a"), w)?, mv("b"))?, w)?)?,
        ],
        sx_concl("idiv_", w, "S", "a", "b", some_r)?,
    ));
    Ok(out)
}

/// `irem_` — remainder magnitude with the dividend's sign; no overflow case
/// (`INT_MIN rem −1 = 0` falls out of the formula).
fn irem(w: u64) -> Result<Vec<Clause>> {
    let some_r = some(ival(mv("r"))?)?;
    let mut out = Vec::new();
    let carrier =
        || -> Result<(Term, Term)> { Ok((in_carrier(mv("a"), w)?, in_carrier(mv("b"), w)?)) };
    // U: r = a mod b, b ≠ 0.
    let (ga, gb) = carrier()?;
    out.push(clause(
        &["a", "b", "r"],
        vec![
            ga,
            gb,
            lt(mk_nat(0u64), mv("b"))?,
            mv("r").equals(md(mv("a"), mv("b"))?)?,
        ],
        sx_concl("irem_", w, "U", "a", "b", some_r.clone())?,
    ));
    // S: (dividend sign, divisor sign) ∈ {(+,+), (+,−), (−,+), (−,−)}.
    let combos: [(bool, bool); 4] = [(false, false), (false, true), (true, false), (true, true)];
    for (a_neg, b_neg) in combos {
        let mag_a = if a_neg { neg_mag(mv("a"), w)? } else { mv("a") };
        let mag_b = if b_neg { neg_mag(mv("b"), w)? } else { mv("b") };
        let m = md(mag_a, mag_b)?;
        let r_def = if a_neg {
            mv("r").equals(neg_result(m, w)?)?
        } else {
            mv("r").equals(m)?
        };
        let mut sides = Vec::new();
        let (ga, gb) = carrier()?;
        if a_neg {
            sides.push(ga);
            sides.push(le(p2(w - 1)?, mv("a"))?);
        } else {
            sides.push(lt(mv("a"), p2(w - 1)?)?);
        }
        if b_neg {
            sides.push(gb);
            sides.push(le(p2(w - 1)?, mv("b"))?);
        } else {
            sides.push(lt(mv("b"), p2(w - 1)?)?);
            sides.push(lt(mk_nat(0u64), mv("b"))?);
        }
        sides.push(r_def);
        out.push(clause(
            &["a", "b", "r"],
            sides,
            sx_concl("irem_", w, "S", "a", "b", some_r.clone())?,
        ));
    }
    Ok(out)
}

// ===========================================================================
// The leg
// ===========================================================================

/// What the builtin leg emitted (headline numbers for [`super::total`]).
#[derive(Debug, Clone, Copy, Default)]
pub struct BuiltinReport {
    /// Clauses emitted.
    pub clauses: usize,
    /// Integer ops given defining clauses (`OPS.len()`).
    pub ops: usize,
    /// Zero-clause builtin tags gaining their first clauses.
    pub zero_clause_ops: usize,
}

/// **The integer-builtin clause list** (deterministic order: op families in
/// [`OPS`] order, widths ascending). All premises are computable `Side`
/// antecedents; no judgement premises, no opaques, zero axioms.
pub fn builtin_clauses() -> Result<(Vec<Clause>, BuiltinReport)> {
    let mut out = Vec::new();
    for carrier in [false, true] {
        out.extend(rational_rounding("truncz", false, carrier)?);
        out.extend(rational_rounding("ceilz", true, carrier)?);
    }
    for w in WIDTHS {
        out.push(isub(w)?);
    }
    for w in WIDTHS {
        out.extend(equality("ieq_", w, false)?);
    }
    for w in WIDTHS {
        out.extend(equality("ine_", w, true)?);
    }
    for (op, swap, strict) in [
        ("ilt_", false, true),
        ("igt_", true, true),
        ("ile_", false, false),
        ("ige_", true, false),
    ] {
        for sx in ["U", "S"] {
            for w in WIDTHS {
                out.extend(ordering(op, w, sx, swap, strict)?);
            }
        }
    }
    for w in WIDTHS {
        out.extend(ieqz(w)?);
    }
    for w in WIDTHS {
        out.push(ishl(w)?);
    }
    for w in WIDTHS {
        out.extend(ishr(w)?);
    }
    for w in WIDTHS {
        out.push(rotate("irotl_", w, true)?);
    }
    for w in WIDTHS {
        out.push(rotate("irotr_", w, false)?);
    }
    for w in WIDTHS {
        out.extend(count_zeros("iclz_", w, true)?);
    }
    for w in WIDTHS {
        out.extend(count_zeros("ictz_", w, false)?);
    }
    for w in DIV_WIDTHS {
        out.extend(idiv(w)?);
    }
    for w in DIV_WIDTHS {
        out.extend(irem(w)?);
    }
    for w in WIDTHS {
        out.extend(bit_structure(w)?);
    }
    for w in SERIALIZATION_WIDTHS {
        out.extend(integer_serialization(w)?);
    }
    out.extend(composite_byte_serializations()?);
    for (lane, w, dim) in INTEGER_LANE_SHAPES {
        out.extend(integer_lanes(lane, w, dim)?);
    }
    for (m, n) in width_pairs() {
        out.push(wrap_conversion(m, n)?);
        if m < n {
            for sx in ["U", "S"] {
                out.extend(extend_conversion(m, n, sx)?);
                out.extend(integer_extend(n, m, sx)?);
            }
        } else if n < m {
            for sx in ["U", "S"] {
                out.extend(narrow_conversion(m, n, sx)?);
            }
        }
    }
    for w in [8, 16] {
        out.push(unsigned_average(w)?);
    }
    out.extend(q15mulr_sat()?);
    out.extend(inverse_sequence_clauses()?);
    out.extend(float_serialization()?);
    out.extend(composite_float_byte_serialization()?);
    out.extend(float_reinterpretation()?);
    out.extend(float_sign_ops()?);
    out.extend(float_comparisons_and_copysign()?);
    out.extend(float_integral_rounding()?);
    out.extend(choice_parameter_clauses()?);
    out.extend(float_to_integer_conversions()?);
    out.extend(integer_to_float_conversions()?);
    out.extend(float_promotion()?);
    out.extend(float_demotion()?);
    let report = BuiltinReport {
        clauses: out.len(),
        ops: OPS.len(),
        zero_clause_ops: ZERO_CLAUSE_OPS_COVERED,
    };
    Ok((out, report))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use covalence_core::Var;
    use covalence_core::subst::subst_free;
    use covalence_hol_eval::EvalThm as Thm;

    use crate::wasm::encode::{metavar_name, phi};
    use crate::wasm::lower::flatten::prove_side;
    use crate::{metalogic, metalogic::Premise};

    /// First-order match of a clause conclusion (metavars are
    /// consistently-bound wildcards) against a ground target.
    fn matches(pat: &Term, tgt: &Term, binds: &mut BTreeMap<String, Term>) -> bool {
        if let Some(v) = pat.as_free()
            && let Some(name) = v.name().strip_prefix("st$v$")
        {
            if let Some(b) = binds.get(name) {
                return b == tgt;
            }
            binds.insert(name.to_owned(), tgt.clone());
            return true;
        }
        match (pat.as_app(), tgt.as_app()) {
            (Some((f1, a1)), Some((f2, a2))) => matches(f1, f2, binds) && matches(a1, a2, binds),
            _ => pat == tgt,
        }
    }

    /// Whether the builtin leg derives the ground graph fact `target`: some
    /// clause's conclusion matches it and **every** `Side` antecedent
    /// (instantiated through the match bindings) is kernel-provable. This is
    /// exactly the `derive_mixed` discharge obligation for premise-free
    /// judgement chains, checked clause-locally.
    fn derivable_at(clauses: &[Clause], target: &Term) -> bool {
        'clauses: for c in clauses {
            let mut binds = BTreeMap::new();
            if !matches(&c.concl, target, &mut binds) {
                continue;
            }
            // Every metavar must be pinned by the conclusion (true for this
            // whole leg — asserted, since an unpinned var would need search).
            for mvn in &c.metavars {
                assert!(
                    binds.contains_key(mvn),
                    "metavar {mvn} not pinned by conclusion"
                );
            }
            for p in &c.prems {
                let LowerPrem::Side(s) = p else {
                    unreachable!("builtin clauses are Side-only")
                };
                let mut inst = s.clone();
                for (name, val) in &binds {
                    inst = subst_free(&inst, &Var::new(metavar_name(name), phi()), val);
                }
                if prove_side(&inst).is_err() {
                    continue 'clauses;
                }
            }
            return true;
        }
        false
    }

    fn nat(n: u64) -> Term {
        mk_nat(n)
    }

    #[test]
    fn signed_bin_addition_and_quantum_scaling_are_exact() {
        for (ln, a, rn, b, carry, outn, expected) in [
            (false, 3, false, 4, 1, false, 8),
            (false, 3, true, 5, 1, true, 1),
            (true, 3, false, 5, 1, false, 3),
            (true, 1, true, 1, 2, false, 0),
            (true, 4, true, 7, 1, true, 10),
        ] {
            let cases = signed_bin_add_cases(
                &[],
                SignedNatTerm {
                    negative: ln,
                    magnitude: nat(a),
                },
                SignedNatTerm {
                    negative: rn,
                    magnitude: nat(b),
                },
                carry,
            )
            .unwrap();
            assert!(cases.iter().any(|case| {
                case.value.negative == outn
                    && prove_side(&case.value.magnitude.clone().equals(nat(expected)).unwrap())
                        .is_ok()
                    && case.sides.iter().all(|side| prove_side(side).is_ok())
            }));
        }

        let normal = scale_ratio_to_quantum(
            &[],
            ExactRatioTerms {
                sign: 0,
                numerator: nat(3),
                denominator: nat(5),
                exp2: SignedNatTerm {
                    negative: false,
                    magnitude: nat(4),
                },
            },
            SignedNatTerm {
                negative: false,
                magnitude: nat(2),
            },
            QuantumClass::Normal,
        )
        .unwrap();
        assert!(normal.iter().any(|case| {
            case.sign == 0
                && matches!(case.class, QuantumClass::Normal)
                && prove_side(&case.numerator.clone().equals(nat(12)).unwrap()).is_ok()
                && prove_side(&case.denominator.clone().equals(nat(5)).unwrap()).is_ok()
                && case.sides.iter().all(|side| prove_side(side).is_ok())
        }));

        // Positive exponent zero must remain canonical when negated.
        let subnormal = scale_ratio_to_quantum(
            &[],
            ExactRatioTerms {
                sign: 1,
                numerator: nat(3),
                denominator: nat(5),
                exp2: SignedNatTerm {
                    negative: true,
                    magnitude: nat(3),
                },
            },
            SignedNatTerm {
                negative: false,
                magnitude: nat(0),
            },
            QuantumClass::Subnormal,
        )
        .unwrap();
        assert!(subnormal.iter().any(|case| {
            case.sign == 1
                && matches!(case.class, QuantumClass::Subnormal)
                && prove_side(&case.numerator.clone().equals(nat(3)).unwrap()).is_ok()
                && prove_side(&case.denominator.clone().equals(nat(40)).unwrap()).is_ok()
                && case.sides.iter().all(|side| prove_side(side).is_ok())
        }));
    }

    fn spine(xs: &[Term]) -> Term {
        xs.iter().cloned().try_fold(con("list"), app).unwrap()
    }

    /// Exhaustive driver for the two `inv_concat_` clauses. `None` means
    /// neither base nor step can conclude at this ground spine length.
    fn derive_pairs(rs: &metalogic::RuleSet<'_>, n_clauses: usize, xs: &[Term]) -> Option<Thm> {
        if xs.is_empty() {
            return metalogic::derive_mixed(rs, 0, n_clauses, &[], vec![]).ok();
        }
        let (prefix, pair) = xs.split_at(xs.len().checked_sub(2)?);
        let prior = derive_pairs(rs, n_clauses, prefix)?;
        let prior_result = prefix.chunks_exact(2).map(spine).collect::<Vec<_>>();
        metalogic::derive_mixed(
            rs,
            1,
            n_clauses,
            &[
                spine(prefix),
                spine(&prior_result),
                pair[0].clone(),
                pair[1].clone(),
            ],
            vec![Premise::Derivation(prior)],
        )
        .ok()
    }

    fn derive_split(
        rs: &metalogic::RuleSet<'_>,
        n_clauses: usize,
        prefix: &[Term],
        block: &[Term],
    ) -> Option<Thm> {
        let prefix_term = spine(prefix);
        let mut proof =
            metalogic::derive_mixed(rs, 2, n_clauses, &[prefix_term.clone()], vec![]).ok()?;
        let mut input = prefix_term.clone();
        let mut block_term = con("list");
        for (i, x) in block.iter().enumerate() {
            let succ = mk_nat(i as u64 + 1)
                .equals(nat::succ(mk_nat(i as u64)))
                .ok()
                .and_then(|p| prove_side(&p).ok())?;
            proof = metalogic::derive_mixed(
                rs,
                3,
                n_clauses,
                &[
                    mk_nat(i as u64),
                    mk_nat(i as u64 + 1),
                    input.clone(),
                    prefix_term.clone(),
                    block_term.clone(),
                    x.clone(),
                ],
                vec![Premise::Side(succ), Premise::Derivation(proof)],
            )
            .ok()?;
            input = app(input, x.clone()).ok()?;
            block_term = app(block_term, x.clone()).ok()?;
        }
        Some(proof)
    }

    /// Exhaustive ground driver for the `inv_concatn_` base/step choice.
    /// The step's exact suffix view makes zero and nonmultiples fail before
    /// any theorem can be assembled.
    fn derive_chunks(
        rs: &metalogic::RuleSet<'_>,
        n_clauses: usize,
        width: usize,
        xs: &[Term],
    ) -> Option<Thm> {
        if width == 0 || xs.len() % width != 0 {
            return None;
        }
        let positive = prove_side(&lt(mk_nat(0u64), mk_nat(width as u64)).ok()?).ok()?;
        if xs.is_empty() {
            return metalogic::derive_mixed(
                rs,
                4,
                n_clauses,
                &[mk_nat(width as u64)],
                vec![Premise::Side(positive)],
            )
            .ok();
        }
        let split_at = xs.len() - width;
        let (prefix, block) = xs.split_at(split_at);
        let split = derive_split(rs, n_clauses, prefix, block)?;
        let prior = derive_chunks(rs, n_clauses, width, prefix)?;
        let prior_blocks = prefix.chunks_exact(width).map(spine).collect::<Vec<_>>();
        metalogic::derive_mixed(
            rs,
            5,
            n_clauses,
            &[
                mk_nat(width as u64),
                spine(xs),
                spine(prefix),
                spine(block),
                spine(&prior_blocks),
            ],
            vec![
                Premise::Side(positive),
                Premise::Derivation(split),
                Premise::Derivation(prior),
            ],
        )
        .ok()
    }

    /// The sequence inverses replay through the ordinary RuleSet engine at
    /// arbitrary recursive depth.  This is a kernel-checked exercise of both
    /// the two-cell graph and the indexed suffix structural view, not merely a
    /// host matcher over a finite list census.
    #[test]
    fn inverse_sequences_replay_unbounded_recursive_graphs() {
        let clauses = inverse_sequence_clauses().unwrap();
        let rs = super::super::rule_set_of(clauses);
        let n_clauses = rs.n_clauses().unwrap();
        assert_eq!(n_clauses, 6);
        let derive = |idx, args: &[Term], prems| {
            metalogic::derive_mixed(&rs, idx, n_clauses, args, prems).unwrap()
        };
        let side = |p: Term| Premise::Side(prove_side(&p).unwrap());
        let succ_side = |n: u64| side(mk_nat(n + 1).equals(nat::succ(mk_nat(n))).unwrap());
        let pos_side = |n: u64| side(lt(mk_nat(0u64), mk_nat(n)).unwrap());

        let [a, b, c, d, e, f] = [11, 12, 13, 14, 15, 16].map(|i| con(format!("elem.{i}")));

        // inv_concat_([a,b,c,d]) = [[a,b],[c,d]].
        let pair_nil = derive(0, &[], vec![]);
        let ab = spine(&[a.clone(), b.clone()]);
        let cd = spine(&[c.clone(), d.clone()]);
        let pair_ab = derive(
            1,
            &[con("list"), con("list"), a.clone(), b.clone()],
            vec![Premise::Derivation(pair_nil)],
        );
        let pair_abcd = derive(
            1,
            &[
                spine(&[a.clone(), b.clone()]),
                spine(std::slice::from_ref(&ab)),
                c.clone(),
                d.clone(),
            ],
            vec![Premise::Derivation(pair_ab)],
        );
        assert_eq!(
            pair_abcd.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph(
                    "inv_concat_",
                    &[spine(&[a.clone(), b.clone(), c.clone(), d.clone()])],
                    &spine(&[ab.clone(), cd]),
                )
                .unwrap(),
            )
            .unwrap()
        );

        // split(3, [a,b,c], [], [a,b,c]), then chunk it.
        let split0 = derive(2, &[con("list")], vec![]);
        let split1 = derive(
            3,
            &[
                mk_nat(0u64),
                mk_nat(1u64),
                con("list"),
                con("list"),
                con("list"),
                a.clone(),
            ],
            vec![succ_side(0), Premise::Derivation(split0)],
        );
        let split2 = derive(
            3,
            &[
                mk_nat(1u64),
                mk_nat(2u64),
                spine(std::slice::from_ref(&a)),
                con("list"),
                spine(std::slice::from_ref(&a)),
                b.clone(),
            ],
            vec![succ_side(1), Premise::Derivation(split1)],
        );
        let split3 = derive(
            3,
            &[
                mk_nat(2u64),
                mk_nat(3u64),
                spine(&[a.clone(), b.clone()]),
                con("list"),
                spine(&[a.clone(), b.clone()]),
                c.clone(),
            ],
            vec![succ_side(2), Premise::Derivation(split2)],
        );
        let chunks0 = derive(4, &[mk_nat(3u64)], vec![pos_side(3)]);
        let chunks1 = derive(
            5,
            &[
                mk_nat(3u64),
                spine(&[a.clone(), b.clone(), c.clone()]),
                con("list"),
                spine(&[a.clone(), b.clone(), c.clone()]),
                con("list"),
            ],
            vec![
                pos_side(3),
                Premise::Derivation(split3),
                Premise::Derivation(chunks0),
            ],
        );

        // A second suffix split demonstrates that recursion is not tied to a
        // single block or fixed total length.
        let prefix = spine(&[a.clone(), b.clone(), c.clone()]);
        let split0b = derive(2, std::slice::from_ref(&prefix), vec![]);
        let mut split = split0b;
        let mut xs = prefix.clone();
        let mut block = con("list");
        for (i, x) in [d.clone(), e.clone(), f.clone()].into_iter().enumerate() {
            let next_xs = app(xs.clone(), x.clone()).unwrap();
            split = derive(
                3,
                &[
                    mk_nat(i as u64),
                    mk_nat(i as u64 + 1),
                    xs,
                    prefix.clone(),
                    block.clone(),
                    x.clone(),
                ],
                vec![succ_side(i as u64), Premise::Derivation(split)],
            );
            xs = next_xs;
            block = app(block, x).unwrap();
        }
        let chunks2 = derive(
            5,
            &[
                mk_nat(3u64),
                spine(&[a, b, c, d, e, f]),
                prefix,
                block.clone(),
                spine(&[spine(&[con("elem.11"), con("elem.12"), con("elem.13")])]),
            ],
            vec![
                pos_side(3),
                Premise::Derivation(split),
                Premise::Derivation(chunks1),
            ],
        );
        assert_eq!(
            chunks2.concl(),
            &metalogic::derivable(
                &rs,
                &fn_graph(
                    "inv_concatn_",
                    &[
                        wrap_nat(mk_nat(3u64)).unwrap(),
                        spine(&[
                            con("elem.11"),
                            con("elem.12"),
                            con("elem.13"),
                            con("elem.14"),
                            con("elem.15"),
                            con("elem.16"),
                        ])
                    ],
                    &spine(&[
                        spine(&[con("elem.11"), con("elem.12"), con("elem.13")]),
                        block,
                    ]),
                )
                .unwrap(),
            )
            .unwrap()
        );

        // Exhaustive ground drivers over the graph's only base/step choices
        // establish the important refusal boundary. No clause can finish an
        // odd pair spine, a zero-width request, or a final short block.
        assert!(derive_pairs(&rs, n_clauses, &[con("odd")]).is_none());
        assert!(derive_chunks(&rs, n_clauses, 0, &[]).is_none());
        assert!(
            derive_chunks(
                &rs,
                n_clauses,
                3,
                &[con("x0"), con("x1"), con("x2"), con("short")]
            )
            .is_none()
        );
        // Positive drivers also cross more than one recursive block and keep
        // each block in source order.
        assert!(
            derive_chunks(
                &rs,
                n_clauses,
                2,
                &[con("x0"), con("x1"), con("x2"), con("x3")]
            )
            .is_some()
        );
    }

    /// Ground graph fact builders (w = 8 keeps kernel arithmetic fast; the
    /// clause *shapes* are identical at every width).
    fn bin_fact(op: &str, w: u64, a: u64, b: u64, r: u64) -> Term {
        fn_graph(
            op,
            &[
                w_lit(w).unwrap(),
                ival(nat(a)).unwrap(),
                ival(nat(b)).unwrap(),
            ],
            &ival(nat(r)).unwrap(),
        )
        .unwrap()
    }
    fn sx_fact(op: &str, w: u64, sx: &str, a: u64, b: u64, r: u64) -> Term {
        fn_graph(
            op,
            &[
                w_lit(w).unwrap(),
                sx_case(sx).unwrap(),
                ival(nat(a)).unwrap(),
                ival(nat(b)).unwrap(),
            ],
            &ival(nat(r)).unwrap(),
        )
        .unwrap()
    }
    fn sx_opt_fact(op: &str, w: u64, sx: &str, a: u64, b: u64, r: Option<u64>) -> Term {
        let res = match r {
            Some(r) => some(ival(nat(r)).unwrap()).unwrap(),
            None => con("opt.none"),
        };
        fn_graph(
            op,
            &[
                w_lit(w).unwrap(),
                sx_case(sx).unwrap(),
                ival(nat(a)).unwrap(),
                ival(nat(b)).unwrap(),
            ],
            &res,
        )
        .unwrap()
    }
    fn un_fact(op: &str, w: u64, a: u64, r: u64) -> Term {
        fn_graph(
            op,
            &[w_lit(w).unwrap(), ival(nat(a)).unwrap()],
            &ival(nat(r)).unwrap(),
        )
        .unwrap()
    }
    fn tern_fact(op: &str, w: u64, a: u64, b: u64, c: u64, r: u64) -> Term {
        fn_graph(
            op,
            &[
                w_lit(w).unwrap(),
                ival(nat(a)).unwrap(),
                ival(nat(b)).unwrap(),
                ival(nat(c)).unwrap(),
            ],
            &ival(nat(r)).unwrap(),
        )
        .unwrap()
    }
    fn nat_list(xs: &[u64]) -> Term {
        let mut out = con("list");
        for &x in xs {
            out = app(out, wrap_nat(nat(x)).unwrap()).unwrap();
        }
        out
    }
    fn serialize_fact(op: &str, w: u64, a: u64, xs: &[u64]) -> Term {
        serialize_term_fact(op, w, nat(a), xs)
    }
    fn serialize_term_fact(op: &str, w: u64, a: Term, xs: &[u64]) -> Term {
        fn_graph(op, &[w_lit(w).unwrap(), ival(a).unwrap()], &nat_list(xs)).unwrap()
    }
    fn inverse_serialize_fact(op: &str, w: u64, xs: &[u64], a: u64) -> Term {
        inverse_serialize_term_fact(op, w, xs, nat(a))
    }
    fn inverse_serialize_term_fact(op: &str, w: u64, xs: &[u64], a: Term) -> Term {
        fn_graph(op, &[w_lit(w).unwrap(), nat_list(xs)], &ival(a).unwrap()).unwrap()
    }
    fn composite_serialize_fact(op: &str, type_case: &str, a: Term, xs: &[u64]) -> Term {
        let ty = app(con(format!("case.{type_case}")), con("tup")).unwrap();
        fn_graph(op, &[ty, ival(a).unwrap()], &nat_list(xs)).unwrap()
    }
    fn inverse_composite_serialize_fact(op: &str, type_case: &str, xs: &[u64], a: Term) -> Term {
        let ty = app(con(format!("case.{type_case}")), con("tup")).unwrap();
        fn_graph(op, &[ty, nat_list(xs)], &ival(a).unwrap()).unwrap()
    }
    fn lane_list(xs: &[u64]) -> Term {
        let mut out = con("list");
        for &x in xs {
            out = app(out, ival(nat(x)).unwrap()).unwrap();
        }
        out
    }
    fn lanes_fact(lane: &str, dim: u64, v: Term, xs: &[u64]) -> Term {
        fn_graph(
            "lanes_",
            &[lane_shape(lane, dim).unwrap(), ival(v).unwrap()],
            &lane_list(xs),
        )
        .unwrap()
    }
    fn inv_lanes_fact(lane: &str, dim: u64, xs: &[u64], v: Term) -> Term {
        fn_graph(
            "inv_lanes_",
            &[lane_shape(lane, dim).unwrap(), lane_list(xs)],
            &ival(v).unwrap(),
        )
        .unwrap()
    }
    fn wrap_fact(m: u64, n: u64, a: u64, r: u64) -> Term {
        fn_graph(
            "wrap__",
            &[w_lit(m).unwrap(), w_lit(n).unwrap(), ival(nat(a)).unwrap()],
            &ival(nat(r)).unwrap(),
        )
        .unwrap()
    }
    fn rational_fact(
        op: &str,
        carrier: bool,
        negative: bool,
        n: u64,
        d: u64,
        result_sign: u64,
        result_magnitude: u64,
    ) -> Term {
        let ratio = if carrier {
            carrier_ratio(nat(n), nat(d)).unwrap()
        } else {
            nat_ratio(nat(n), nat(d)).unwrap()
        };
        let arg = if negative {
            app(con("un.Minus"), ratio).unwrap()
        } else {
            ratio
        };
        fn_graph(
            op,
            &[arg],
            &wrap_int(result_sign, nat(result_magnitude)).unwrap(),
        )
        .unwrap()
    }
    fn extend_fact(op: &str, m: u64, n: u64, sx: &str, a: u64, r: u64) -> Term {
        let widths = if op == "iextend_" { (n, m) } else { (m, n) };
        fn_graph(
            op,
            &[
                w_lit(widths.0).unwrap(),
                w_lit(widths.1).unwrap(),
                sx_case(sx).unwrap(),
                ival(nat(a)).unwrap(),
            ],
            &ival(nat(r)).unwrap(),
        )
        .unwrap()
    }

    /// Assert the graph fires **exactly** at `expected` and refuses the
    /// perturbed results `expected ± 1` (mod the carrier).
    fn assert_exact(clauses: &[Clause], fact: impl Fn(u64) -> Term, expected: u64, w: u64) {
        let m = 1u64 << w;
        assert!(
            derivable_at(clauses, &fact(expected)),
            "expected result {expected} underivable"
        );
        for wrong in [(expected + 1) % m, (expected + m - 1) % m] {
            if wrong == expected {
                continue;
            }
            assert!(
                !derivable_at(clauses, &fact(wrong)),
                "wrong result {wrong} derivable (expected {expected})"
            );
        }
    }

    /// **The oracle cross-check** (module-doc contract): every op of the leg
    /// against Rust's independent two's-complement arithmetic at w = 8, over
    /// a grid covering both sign classes, wraparound, and the special points
    /// (0, INT_MIN, −1). Fires exactly at the oracle result; refuses ±1.
    #[test]
    fn builtin_clauses_match_rust_oracle_w8() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, clauses.len());
        let sample: [u8; 7] = [0, 1, 2, 127, 128, 200, 255];
        let w = 8u64;
        for &a in &sample {
            for &b in &sample {
                let (an, bn) = (a as u64, b as u64);
                let (sa, sb) = (a as i8, b as i8);
                // isub_ vs wrapping_sub.
                assert_exact(
                    &clauses,
                    |r| bin_fact("isub_", w, an, bn, r),
                    a.wrapping_sub(b) as u64,
                    w,
                );
                // ieq_/ine_.
                assert_exact(
                    &clauses,
                    |r| bin_fact("ieq_", w, an, bn, r),
                    (a == b) as u64,
                    w,
                );
                assert_exact(
                    &clauses,
                    |r| bin_fact("ine_", w, an, bn, r),
                    (a != b) as u64,
                    w,
                );
                // Orderings, unsigned and signed.
                let cases: [(&str, bool, bool); 4] = [
                    ("ilt_", a < b, sa < sb),
                    ("igt_", a > b, sa > sb),
                    ("ile_", a <= b, sa <= sb),
                    ("ige_", a >= b, sa >= sb),
                ];
                for (op, u_res, s_res) in cases {
                    assert_exact(
                        &clauses,
                        |r| sx_fact(op, w, "U", an, bn, r),
                        u_res as u64,
                        w,
                    );
                    assert_exact(
                        &clauses,
                        |r| sx_fact(op, w, "S", an, bn, r),
                        s_res as u64,
                        w,
                    );
                }
                // Shifts and rotates (b as count; the spec and Rust both
                // take the count mod the width for shl/rotl/rotr; Rust `>>`
                // on u8/i8 requires count < 8, so reduce first).
                let k = (b % 8) as u32;
                assert_exact(
                    &clauses,
                    |r| bin_fact("ishl_", w, an, bn, r),
                    (a.wrapping_shl(k)) as u64,
                    w,
                );
                assert_exact(
                    &clauses,
                    |r| sx_fact("ishr_", w, "U", an, bn, r),
                    (a >> k) as u64,
                    w,
                );
                assert_exact(
                    &clauses,
                    |r| sx_fact("ishr_", w, "S", an, bn, r),
                    ((sa >> k) as u8) as u64,
                    w,
                );
                assert_exact(
                    &clauses,
                    |r| bin_fact("irotl_", w, an, bn, r),
                    a.rotate_left(k) as u64,
                    w,
                );
                assert_exact(
                    &clauses,
                    |r| bin_fact("irotr_", w, an, bn, r),
                    a.rotate_right(k) as u64,
                    w,
                );
            }
            // Unary: ieqz_/iclz_/ictz_ (ictz_(0) = w by the ground clause,
            // matching Rust's trailing_zeros on the exact-width type).
            let an = a as u64;
            assert_exact(&clauses, |r| un_fact("ieqz_", w, an, r), (a == 0) as u64, w);
            assert_exact(
                &clauses,
                |r| un_fact("iclz_", w, an, r),
                a.leading_zeros() as u64,
                w,
            );
            assert_exact(
                &clauses,
                |r| un_fact("ictz_", w, an, r),
                a.trailing_zeros() as u64,
                w,
            );
        }
    }

    #[test]
    fn integer_conversion_matrix_is_exact_and_fail_closed() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        // Complete reachable wrap matrix, checked against an independent
        // bit-mask oracle. Use inputs with both kept and discarded high bits.
        for m in WIDTHS {
            for n in WIDTHS {
                let mask_m = if m == 64 { u64::MAX } else { (1u64 << m) - 1 };
                let mask_n = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
                let a = 0xa5a5_f00f_dead_beefu64 & mask_m;
                let expected = a & mask_n;
                assert!(derivable_at(&clauses, &wrap_fact(m, n, a, expected)));
                let wrong = expected.wrapping_add(1) & mask_n;
                if wrong != expected {
                    assert!(!derivable_at(&clauses, &wrap_fact(m, n, a, wrong)));
                }
            }
        }

        // Saturating narrowing, including values around both signed bounds.
        for m in WIDTHS {
            for n in WIDTHS {
                if m <= n {
                    continue;
                }
                let source_mask = if m == 64 { u64::MAX } else { (1u64 << m) - 1 };
                let target_mask = (1u64 << n) - 1;
                let umax = target_mask;
                let smin = -(1i128 << (n - 1));
                let smax = (1i128 << (n - 1)) - 1;
                let samples = [
                    0,
                    1,
                    umax,
                    umax.saturating_add(1) & source_mask,
                    (1u64 << (m - 1)) - 1,
                    1u64 << (m - 1),
                    source_mask,
                ];
                for a in samples {
                    let u_expected = a.min(umax);
                    let signed_source = if a & (1u64 << (m - 1)) == 0 {
                        a as i128
                    } else {
                        a as i128 - (1i128 << m)
                    };
                    let signed_clamped = signed_source.clamp(smin, smax);
                    let s_expected = if signed_clamped < 0 {
                        ((1i128 << n) + signed_clamped) as u64
                    } else {
                        signed_clamped as u64
                    };
                    for (sx, expected) in [("U", u_expected), ("S", s_expected)] {
                        assert!(
                            derivable_at(&clauses, &extend_fact("narrow__", m, n, sx, a, expected)),
                            "narrow__ {m}->{n} {sx} at {a:#x}"
                        );
                        let wrong = expected.wrapping_add(1) & target_mask;
                        assert!(
                            !derivable_at(&clauses, &extend_fact("narrow__", m, n, sx, a, wrong)),
                            "narrow__ accepted wrong {m}->{n} {sx} result"
                        );
                    }
                }
            }
        }

        // Cross-carrier extension and in-place low-bit extension share the
        // same oracle. Exercise both source sign classes at every m<n pair.
        for m in WIDTHS {
            for n in WIDTHS {
                if m >= n {
                    continue;
                }
                let source_mask = (1u64 << m) - 1;
                let target_mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
                for a in [0u64, 1, (1u64 << (m - 1)) - 1, 1u64 << (m - 1), source_mask] {
                    let unsigned = a;
                    let signed = if a & (1u64 << (m - 1)) == 0 {
                        a
                    } else {
                        a | (target_mask ^ source_mask)
                    };
                    for (sx, expected) in [("U", unsigned), ("S", signed)] {
                        for op in ["extend__", "iextend_"] {
                            assert!(
                                derivable_at(&clauses, &extend_fact(op, m, n, sx, a, expected)),
                                "{op} {m}->{n} {sx} at {a:#x}"
                            );
                            let wrong = expected.wrapping_add(1) & target_mask;
                            assert!(
                                !derivable_at(&clauses, &extend_fact(op, m, n, sx, a, wrong)),
                                "{op} accepted wrong {m}->{n} {sx} result"
                            );
                        }
                    }
                }
            }
        }

        // No convenient totalisation: ill-typed source carriers and
        // unsupported same-width `extend__` calls derive nothing.
        assert!(!derivable_at(&clauses, &wrap_fact(8, 32, 256, 256)));
        assert!(!derivable_at(
            &clauses,
            &extend_fact("extend__", 32, 32, "U", 7, 7)
        ));
        assert!(!derivable_at(
            &clauses,
            &extend_fact("narrow__", 16, 32, "U", 7, 7)
        ));
        // A float-shaped payload cannot match the integer `%` carrier.
        let float_payload = app(con("case.F32"), con("tup")).unwrap();
        let float_attempt = fn_graph(
            "wrap__",
            &[w_lit(32).unwrap(), w_lit(32).unwrap(), float_payload],
            &ival(nat(0)).unwrap(),
        )
        .unwrap();
        assert!(!derivable_at(&clauses, &float_attempt));
    }

    /// Exhaustive 8-bit oracle for the fixed-width bit-structure clauses.
    ///
    /// Every unary input and binary input pair is checked at the unique Rust
    /// result. `ibitselect_` additionally exhausts all 256 masks over an
    /// edge-complete operand grid; its clause uses the same independently
    /// checked per-bit selector expression. Wrong-result refusal is exercised
    /// for every operation by the full-width edge test below (doing three
    /// kernel reductions at all 278k exhaustive points would make this narrow
    /// test needlessly slow).
    #[test]
    #[ignore = "explicit exhaustive HOL replay (~minutes); fast width/edge oracle runs by default"]
    fn bit_structure_matches_rust_oracle_exhaustive_w8() {
        let clauses = bit_structure(8).unwrap();
        for a in 0u64..=u8::MAX as u64 {
            let au = a as u8;
            for (op, expected) in [
                ("inot_", (!au) as u64),
                ("irev_", au.reverse_bits() as u64),
                ("ipopcnt_", au.count_ones() as u64),
            ] {
                assert!(
                    derivable_at(&clauses, &un_fact(op, 8, a, expected)),
                    "{op}({a}) = {expected}"
                );
            }
            for b in 0u64..=u8::MAX as u64 {
                let bu = b as u8;
                for (op, expected) in [
                    ("iand_", (au & bu) as u64),
                    ("iandnot_", (au & !bu) as u64),
                    ("ior_", (au | bu) as u64),
                    ("ixor_", (au ^ bu) as u64),
                ] {
                    assert!(
                        derivable_at(&clauses, &bin_fact(op, 8, a, b, expected)),
                        "{op}({a}, {b}) = {expected}"
                    );
                }
            }
        }

        let edge = [0u64, 1, 0x55, 0xaa, 0x7f, 0x80, 0xfe, 0xff];
        for a in edge {
            for b in edge {
                for c in 0u64..=u8::MAX as u64 {
                    let expected = ((a & c) | (b & !c)) & 0xff;
                    assert!(
                        derivable_at(&clauses, &tern_fact("ibitselect_", 8, a, b, c, expected)),
                        "ibitselect_({a}, {b}, {c}) = {expected}"
                    );
                }
            }
        }
    }

    /// Fast exhaustive arithmetic-oracle check for all 8-bit inputs. This is
    /// independent Rust arithmetic over the same per-bit identities used by
    /// the HOL clauses; the tests around it replay those clause terms through
    /// the kernel at every width.
    #[test]
    fn bit_structure_formulas_exhaustive_w8() {
        let bit = |x: u8, i: u32| (x >> i) & 1;
        let assemble = |f: &dyn Fn(u32) -> u8| -> u8 { (0..8).fold(0, |r, i| r | (f(i) << i)) };
        for a in u8::MIN..=u8::MAX {
            let reverse = (0..8).fold(0u8, |r, i| r | (bit(a, i) << (7 - i)));
            let popcount = (0..8).map(|i| bit(a, i) as u32).sum::<u32>();
            assert_eq!(!a, 255 - a);
            assert_eq!(a.reverse_bits(), reverse);
            assert_eq!(a.count_ones(), popcount);
            for b in u8::MIN..=u8::MAX {
                let and = assemble(&|i| bit(a, i) * bit(b, i));
                let andnot = assemble(&|i| bit(a, i) * (1 - bit(b, i)));
                let or = assemble(&|i| bit(a, i) + bit(b, i) - bit(a, i) * bit(b, i));
                let xor = assemble(&|i| bit(a, i) + bit(b, i) - 2 * bit(a, i) * bit(b, i));
                assert_eq!(a & b, and);
                assert_eq!(a & !b, andnot);
                assert_eq!(a | b, or);
                assert_eq!(a ^ b, xor);
            }
        }
        // Exhaust every mask over an edge-complete pair grid for ternary
        // bitselect; the all-a/all-b endpoints and alternating masks expose
        // operand-order and complement mistakes immediately.
        let edge = [0u8, 1, 0x55, 0xaa, 0x7f, 0x80, 0xfe, 0xff];
        for a in edge {
            for b in edge {
                for c in u8::MIN..=u8::MAX {
                    let selected =
                        assemble(&|i| bit(a, i) * bit(c, i) + bit(b, i) * (1 - bit(c, i)));
                    assert_eq!((a & c) | (b & !c), selected);
                }
            }
        }
    }

    /// Representative full-width edge vectors ensure the emitted 16/32/64
    /// clauses use the requested carrier width (rather than accidentally
    /// inheriting the compact w=8 oracle's arithmetic).
    #[test]
    fn bit_structure_full_width_edges() {
        let (clauses, _) = builtin_clauses().unwrap();
        let cases = [
            (16, 0xa55a, 0x0ff0, 0x3333),
            (32, 0x8000_0001, 0xffff_0000, 0xaaaa_5555),
            (
                64,
                0x8000_0000_0000_0001,
                0xffff_0000_ffff_0000,
                0xaaaa_5555_aaaa_5555,
            ),
        ];
        for (w, a, b, c) in cases {
            let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
            let checks = [
                ("iand_", a & b),
                ("iandnot_", a & !b & mask),
                ("ior_", a | b),
                ("ixor_", a ^ b),
            ];
            for (op, expected) in checks {
                assert!(derivable_at(&clauses, &bin_fact(op, w, a, b, expected)));
                assert!(!derivable_at(
                    &clauses,
                    &bin_fact(op, w, a, b, expected ^ 1)
                ));
            }
            for (op, expected) in [
                ("inot_", !a & mask),
                ("irev_", a.reverse_bits() >> (64 - w)),
                ("ipopcnt_", a.count_ones() as u64),
            ] {
                assert!(derivable_at(&clauses, &un_fact(op, w, a, expected)));
                assert!(!derivable_at(&clauses, &un_fact(op, w, a, expected ^ 1)));
            }
            let selected = (a & c) | (b & !c);
            assert!(derivable_at(
                &clauses,
                &tern_fact("ibitselect_", w, a, b, c, selected)
            ));
            assert!(!derivable_at(
                &clauses,
                &tern_fact("ibitselect_", w, a, b, c, selected ^ 1)
            ));
        }
    }

    /// Integer serialization is exact in both directions: little-endian
    /// bit/byte lists round-trip at every reachable width, while a changed
    /// element, result, length, or out-of-range element is rejected by the
    /// same kernel-side arithmetic that defines the graph.
    #[test]
    fn integer_serialization_round_trips_and_refuses_wrong_results() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        for (w, a) in [
            (8, 0xa5),
            (16, 0xa55a),
            (32, 0x8000_00a5),
            (64, 0x8000_0000_0000_00a5),
        ] {
            let bits: Vec<u64> = (0..w).map(|i| (a >> i) & 1).collect();
            let bytes: Vec<u64> = (0..w / 8).map(|i| (a >> (8 * i)) & 0xff).collect();
            for (fwd, inv, xs) in [
                ("ibits_", "inv_ibits_", bits.as_slice()),
                ("ibytes_", "inv_ibytes_", bytes.as_slice()),
            ] {
                assert!(derivable_at(&clauses, &serialize_fact(fwd, w, a, xs)));
                assert!(derivable_at(
                    &clauses,
                    &inverse_serialize_fact(inv, w, xs, a)
                ));

                let mut changed = xs.to_vec();
                changed[0] ^= 1;
                assert!(!derivable_at(
                    &clauses,
                    &serialize_fact(fwd, w, a, &changed)
                ));
                assert!(!derivable_at(
                    &clauses,
                    &inverse_serialize_fact(inv, w, xs, a ^ 1)
                ));
                assert!(!derivable_at(
                    &clauses,
                    &inverse_serialize_fact(inv, w, &xs[..xs.len() - 1], a)
                ));
            }

            let mut bad_bit = bits.clone();
            bad_bit[0] = 2;
            assert!(!derivable_at(
                &clauses,
                &inverse_serialize_fact("inv_ibits_", w, &bad_bit, a)
            ));
            let mut bad_byte = bytes.clone();
            bad_byte[0] = 256;
            assert!(!derivable_at(
                &clauses,
                &inverse_serialize_fact("inv_ibytes_", w, &bad_byte, a)
            ));
        }

        // Real corpus width: `v128.const` calls `inv_ibytes_(128, ...)`.
        // Put a byte beyond the u64 range (byte 15 = 2^120) to prove the
        // clause genuinely reconstructs all 128 bits rather than truncating.
        let mut high = vec![0u64; 16];
        high[15] = 1;
        assert!(derivable_at(
            &clauses,
            &serialize_term_fact("ibytes_", 128, p2(120).unwrap(), &high)
        ));
        assert!(derivable_at(
            &clauses,
            &inverse_serialize_term_fact("inv_ibytes_", 128, &high, p2(120).unwrap())
        ));
        let mut wrong_place = high.clone();
        wrong_place[15] = 0;
        wrong_place[7] = 1;
        assert!(!derivable_at(
            &clauses,
            &inverse_serialize_term_fact("inv_ibytes_", 128, &wrong_place, p2(120).unwrap())
        ));
    }

    /// The composite byte front doors agree with Rust little-endian bytes on
    /// every integer/vector branch and reject wrong bytes, malformed lengths,
    /// carrier overflow, unsupported type/op combinations, and all float
    /// carriers.
    #[test]
    fn composite_byte_serialization_is_exact_and_fail_closed() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let families: [(&str, &str, &[(&str, u64)]); 4] = [
            ("nbytes_", "inv_nbytes_", &[("I32", 32), ("I64", 64)]),
            ("vbytes_", "inv_vbytes_", &[("V128", 128)]),
            (
                "zbytes_",
                "inv_zbytes_",
                &[
                    ("I8", 8),
                    ("I16", 16),
                    ("I32", 32),
                    ("I64", 64),
                    ("V128", 128),
                ],
            ),
            (
                "cbytes_",
                "inv_cbytes_",
                &[("I32", 32), ("I64", 64), ("V128", 128)],
            ),
        ];
        for (fwd, inv, shapes) in families {
            for &(shape, w) in shapes {
                // A byte in every position catches endianness, truncation, and
                // accidental host-u64 assumptions at V128.
                let xs: Vec<u64> = (0..w / 8).map(|i| (17 * i + 3) & 0xff).collect();
                let value = sum(xs
                    .iter()
                    .enumerate()
                    .map(|(i, x)| Ok(mul(nat(*x), p2(8 * i as u64)?)?)))
                .unwrap();
                assert!(derivable_at(
                    &clauses,
                    &composite_serialize_fact(fwd, shape, value.clone(), &xs)
                ));
                assert!(derivable_at(
                    &clauses,
                    &inverse_composite_serialize_fact(inv, shape, &xs, value.clone())
                ));

                let mut wrong = xs.clone();
                wrong[0] ^= 1;
                assert!(!derivable_at(
                    &clauses,
                    &composite_serialize_fact(fwd, shape, value.clone(), &wrong)
                ));
                assert!(!derivable_at(
                    &clauses,
                    &inverse_composite_serialize_fact(inv, shape, &xs, add(value, nat(1)).unwrap())
                ));
                assert!(!derivable_at(
                    &clauses,
                    &inverse_composite_serialize_fact(inv, shape, &xs[..xs.len() - 1], nat(0))
                ));
            }
        }

        let bytes32 = [0u64; 4];
        for op in ["nbytes_", "vbytes_", "zbytes_", "cbytes_"] {
            assert!(!derivable_at(
                &clauses,
                &composite_serialize_fact(op, "F32", nat(0), &bytes32)
            ));
        }
        // Each wrapper accepts only its real type family.
        assert!(!derivable_at(
            &clauses,
            &composite_serialize_fact("nbytes_", "V128", nat(0), &[0; 16])
        ));
        assert!(!derivable_at(
            &clauses,
            &composite_serialize_fact("vbytes_", "I32", nat(0), &bytes32)
        ));
        // Erased carriers and byte elements still fail closed.
        assert!(!derivable_at(
            &clauses,
            &composite_serialize_fact("nbytes_", "I32", p2(32).unwrap(), &bytes32)
        ));
        let mut bad_byte = bytes32;
        bad_byte[0] = 256;
        assert!(!derivable_at(
            &clauses,
            &inverse_composite_serialize_fact("inv_nbytes_", "I32", &bad_byte, nat(0))
        ));
    }

    /// Integer SIMD lane decomposition is an exact shape-indexed isomorphism:
    /// all four integer shapes round-trip; changed lanes/vectors, malformed
    /// lengths, lane overflow, and unsupported float shapes are rejected.
    #[test]
    fn integer_lanes_round_trip_and_fail_closed() {
        let (clauses, _) = builtin_clauses().unwrap();
        for (lane, w, dim) in INTEGER_LANE_SHAPES {
            let xs: Vec<u64> = (0..dim).map(|i| i + 1).collect();
            let v = sum(xs
                .iter()
                .enumerate()
                .map(|(i, x)| Ok(mul(nat(*x), p2(w * i as u64)?)?)))
            .unwrap();
            assert!(derivable_at(
                &clauses,
                &lanes_fact(lane, dim, v.clone(), &xs)
            ));
            assert!(derivable_at(
                &clauses,
                &inv_lanes_fact(lane, dim, &xs, v.clone())
            ));

            let mut changed = xs.clone();
            changed[0] += 1;
            assert!(!derivable_at(
                &clauses,
                &lanes_fact(lane, dim, v.clone(), &changed)
            ));
            assert!(!derivable_at(
                &clauses,
                &inv_lanes_fact(lane, dim, &xs, add(v.clone(), nat(1)).unwrap())
            ));
            assert!(!derivable_at(
                &clauses,
                &inv_lanes_fact(lane, dim, &xs[..xs.len() - 1], v.clone())
            ));

            let mut overflow = xs.clone();
            overflow[0] = 1u64 << w.min(63);
            if w == 64 {
                // `u64` cannot spell 2^64; malformed lengths and wrong vectors
                // already exercise fail-closed I64. Other widths hit the live
                // lane carrier guard directly.
                continue;
            }
            assert!(!derivable_at(
                &clauses,
                &inv_lanes_fact(lane, dim, &overflow, v)
            ));
        }

        let xs = [1, 2, 3, 4];
        let v = nat(0x0000_0004_0000_0003);
        assert!(!derivable_at(
            &clauses,
            &fn_graph(
                "lanes_",
                &[lane_shape("F32", 4).unwrap(), ival(v).unwrap()],
                &lane_list(&xs),
            )
            .unwrap()
        ));

        // A live bit above u64 proves the 128-bit carrier is not truncated.
        let mut high = vec![0u64; 16];
        high[15] = 1;
        assert!(derivable_at(
            &clauses,
            &inv_lanes_fact("I8", 16, &high, p2(120).unwrap())
        ));
    }

    /// `idiv_`/`irem_` vs Rust: truncating division, dividend-sign
    /// remainder, by-zero eps (covered by the spec's own clauses — here we
    /// only assert **our** clauses refuse b = 0), and the signed-overflow
    /// eps at (INT_MIN, −1). Note w = 8: INT_MIN = 128 (= −128), −1 = 255.
    #[test]
    fn div_rem_match_rust_oracle_w8() {
        // Emit a w = 8 instance directly (the shipped DIV_WIDTHS are 32/64 —
        // scalar — but the clause builders are width-generic; testing at 8
        // keeps the kernel arithmetic snappy while exercising every branch).
        let mut clauses = idiv(8).unwrap();
        clauses.extend(irem(8).unwrap());
        let w = 8u64;
        let sample: [u8; 7] = [0, 1, 2, 127, 128, 200, 255];
        for &a in &sample {
            for &b in &sample {
                let (an, bn) = (a as u64, b as u64);
                let (sa, sb) = (a as i8, b as i8);
                // Unsigned.
                let udiv = if b == 0 { None } else { Some((a / b) as u64) };
                let urem = if b == 0 { None } else { Some((a % b) as u64) };
                for (op, expect) in [("idiv_", udiv), ("irem_", urem)] {
                    match expect {
                        Some(r) => {
                            assert!(derivable_at(
                                &clauses,
                                &sx_opt_fact(op, w, "U", an, bn, Some(r))
                            ));
                            assert!(!derivable_at(
                                &clauses,
                                &sx_opt_fact(op, w, "U", an, bn, Some((r + 1) % 256))
                            ));
                            assert!(!derivable_at(
                                &clauses,
                                &sx_opt_fact(op, w, "U", an, bn, None)
                            ));
                        }
                        None => {
                            // By-zero: OUR clauses must refuse everything
                            // (the eps fact is the spec's own ground clause).
                            for r in [None, Some(0)] {
                                assert!(!derivable_at(
                                    &clauses,
                                    &sx_opt_fact(op, w, "U", an, bn, r)
                                ));
                            }
                        }
                    }
                }
                // Signed (checked_div/checked_rem are exactly the spec's
                // partiality: None on by-zero and on INT_MIN / −1 overflow —
                // except rem, where Rust's checked_rem(INT_MIN, -1) is None
                // but WASM irem_s yields 0; the spec formula gives 0 too).
                let sdiv = sa.checked_div(sb).map(|q| (q as u8) as u64);
                let srem = if sb == 0 {
                    None
                } else {
                    Some((sa.wrapping_rem(sb) as u8) as u64)
                };
                match sdiv {
                    Some(r) => {
                        assert!(derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, Some(r))
                        ));
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, Some((r + 1) % 256))
                        ));
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, None)
                        ));
                    }
                    None if b != 0 => {
                        // Signed overflow (INT_MIN / −1): eps derivable,
                        // every value refused.
                        assert!(derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, None)
                        ));
                        for r in 0..=3u64 {
                            assert!(!derivable_at(
                                &clauses,
                                &sx_opt_fact("idiv_", w, "S", an, bn, Some(r))
                            ));
                        }
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, Some(128))
                        ));
                    }
                    None => {
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, None)
                        ));
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("idiv_", w, "S", an, bn, Some(0))
                        ));
                    }
                }
                match srem {
                    Some(r) => {
                        assert!(derivable_at(
                            &clauses,
                            &sx_opt_fact("irem_", w, "S", an, bn, Some(r))
                        ));
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("irem_", w, "S", an, bn, Some((r + 1) % 256))
                        ));
                    }
                    None => {
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("irem_", w, "S", an, bn, None)
                        ));
                        assert!(!derivable_at(
                            &clauses,
                            &sx_opt_fact("irem_", w, "S", an, bn, Some(0))
                        ));
                    }
                }
            }
        }
    }

    /// Junk points refuse: out-of-carrier operands (`a ≥ 2^w`) discharge no
    /// clause — the carrier guards are live.
    #[test]
    fn out_of_carrier_operands_refused() {
        let (clauses, _) = builtin_clauses().unwrap();
        let w = 8u64;
        // 300 ≥ 2^8: no result derivable for isub_/ilt_ even at the
        // "correct-looking" wraparound values.
        for r in [0u64, 44, 255] {
            assert!(!derivable_at(&clauses, &bin_fact("isub_", w, 300, 0, r)));
        }
        for r in [0u64, 1] {
            assert!(!derivable_at(&clauses, &sx_fact("ilt_", w, "U", 300, 5, r)));
        }
    }

    #[test]
    fn structural_rational_rounding_is_exact_and_fail_closed() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        // Independent integer-arithmetic oracle, including integral,
        // fractional, sub-unit, and zero points in both sign classes.
        for (n, d) in [(0, 1), (1, 3), (2, 2), (7, 3), (10, 5), (17, 8)] {
            let floor = n / d;
            let ceil = (n + d - 1) / d;
            for (op, carrier, negative, sign, magnitude) in
                [false, true].into_iter().flat_map(|carrier| {
                    [
                        ("truncz", carrier, false, 0, floor),
                        ("ceilz", carrier, false, 0, ceil),
                        ("truncz", carrier, true, u64::from(floor != 0), floor),
                        ("ceilz", carrier, true, u64::from(floor != 0), floor),
                    ]
                })
            {
                assert!(
                    derivable_at(
                        &clauses,
                        &rational_fact(op, carrier, negative, n, d, sign, magnitude)
                    ),
                    "{op} negative={negative} {n}/{d} -> ({sign},{magnitude})"
                );
                assert!(!derivable_at(
                    &clauses,
                    &rational_fact(op, carrier, negative, n, d, sign, magnitude + 1)
                ));
                // Negative zero is never a canonical integer result.
                if magnitude == 0 {
                    assert!(!derivable_at(
                        &clauses,
                        &rational_fact(op, carrier, negative, n, d, 1, 0)
                    ));
                }
            }
        }

        // Division by zero, invented result signs, and representation-erased
        // opaque rationals receive no fact.
        for op in ["truncz", "ceilz"] {
            assert!(!derivable_at(
                &clauses,
                &rational_fact(op, false, false, 7, 0, 0, 0)
            ));
            assert!(!derivable_at(
                &clauses,
                &rational_fact(op, false, false, 7, 3, 1, 2)
            ));
            let opaque =
                fn_graph(op, &[con("num.rat.7/3")], &wrap_int(0, nat(2)).unwrap()).unwrap();
            assert!(!derivable_at(&clauses, &opaque));
        }
    }

    #[test]
    fn unsigned_rounded_average_is_exact_and_fail_closed() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        for (w, points) in [
            (8, vec![(0, 0), (0, 1), (1, 1), (17, 42), (255, 255)]),
            (
                16,
                vec![(0, 0), (0, 1), (1, 1), (1234, 5678), (65535, 65535)],
            ),
        ] {
            let modulus = 1u64 << w;
            for (a, b) in points {
                let expected = (a + b + 1) / 2;
                assert!(derivable_at(
                    &clauses,
                    &sx_fact("iavgr_", w, "U", a, b, expected)
                ));
                assert!(!derivable_at(
                    &clauses,
                    &sx_fact("iavgr_", w, "U", a, b, (expected + 1) % modulus)
                ));
                assert!(!derivable_at(
                    &clauses,
                    &sx_fact("iavgr_", w, "S", a, b, expected)
                ));
            }
        }

        // AVGR exists only for the I8x16 and I16x8 instruction shapes.
        assert!(!derivable_at(
            &clauses,
            &sx_fact("iavgr_", 32, "U", 1, 2, 2)
        ));
        // Erased HOL encodings still get explicit carrier checks.
        assert!(!derivable_at(
            &clauses,
            &sx_fact("iavgr_", 8, "U", 256, 0, 128)
        ));
    }

    #[test]
    fn signed_q15mulr_sat_is_exact_and_fail_closed() {
        let (clauses, _) = builtin_clauses().unwrap();
        let encode = |x: i32| -> u64 { (x as i16) as u16 as u64 };
        let oracle = |a: i32, b: i32| -> u64 {
            let product = a * b;
            let rounded = (product + (1 << 14)) >> 15;
            encode(rounded.clamp(i16::MIN as i32, i16::MAX as i32))
        };

        // Cross every sign class, both half-way boundaries, ordinary extrema,
        // and the unique saturating product.
        for (a, b) in [
            (0, 0),
            (1, 16384),
            (1, 16385),
            (-1, 16384),
            (-1, 16385),
            (12345, 23456),
            (-12345, 23456),
            (12345, -23456),
            (-12345, -23456),
            (i16::MAX as i32, i16::MAX as i32),
            (i16::MIN as i32, i16::MAX as i32),
            (i16::MIN as i32, i16::MIN as i32),
        ] {
            let expected = oracle(a, b);
            let fact = |r| sx_fact("iq15mulr_sat_", 16, "S", encode(a), encode(b), r);
            assert!(derivable_at(&clauses, &fact(expected)), "{a} × {b}");
            assert!(
                !derivable_at(&clauses, &fact((expected + 1) & 0xffff)),
                "wrong result accepted for {a} × {b}"
            );
        }

        // This SpecTec primitive is instruction-reachable only at I16/S.
        assert!(!derivable_at(
            &clauses,
            &sx_fact("iq15mulr_sat_", 16, "U", 1, 1, 0)
        ));
        assert!(!derivable_at(
            &clauses,
            &sx_fact("iq15mulr_sat_", 8, "S", 1, 1, 0)
        ));
        assert!(!derivable_at(
            &clauses,
            &sx_fact("iq15mulr_sat_", 16, "S", 65536, 1, 2)
        ));
    }

    fn tuple1(x: Term) -> Term {
        app(con("tup"), x).unwrap()
    }

    fn tuple2(x: Term, y: Term) -> Term {
        app(app(con("tup"), x).unwrap(), y).unwrap()
    }

    fn fmag_subnormal(m: u64) -> Term {
        app(con("case.SUBNORM"), tuple1(wrap_nat(nat(m)).unwrap())).unwrap()
    }

    fn fmag_normal(m: u64, sign: u64, exponent: u64) -> Term {
        app(
            con("case.NORM"),
            tuple2(
                wrap_nat(nat(m)).unwrap(),
                wrap_int(sign, nat(exponent)).unwrap(),
            ),
        )
        .unwrap()
    }

    fn fmag_inf() -> Term {
        app(con("case.INF"), con("tup")).unwrap()
    }

    fn fval(sign: u64, magnitude: Term) -> Term {
        app(
            con(if sign == 0 { "case.POS" } else { "case.NEG" }),
            magnitude,
        )
        .unwrap()
    }

    fn float_serialize_fact(op: &str, w: u64, value: Term, digits: &[u64]) -> Term {
        fn_graph(op, &[w_lit(w).unwrap(), value], &nat_list(digits)).unwrap()
    }

    fn inverse_float_serialize_fact(op: &str, w: u64, digits: &[u64], value: Term) -> Term {
        fn_graph(op, &[w_lit(w).unwrap(), nat_list(digits)], &value).unwrap()
    }

    fn le_bytes(raw: u64, width: usize) -> Vec<u64> {
        (0..width).map(|i| (raw >> (8 * i)) & 0xff).collect()
    }

    fn low_bits_first(raw: u64, width: usize) -> Vec<u64> {
        (0..width).map(|i| (raw >> i) & 1).collect()
    }

    fn float_cmp_fact(op: &str, w: u64, left: Term, right: Term, result: u64) -> Term {
        float_comparison_concl(op, w, left, right, result).unwrap()
    }

    #[test]
    fn structural_float_representation_is_exact_and_fail_closed() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let cases = [
            (32, fval(0, fmag_subnormal(0)), 0),
            (32, fval(1, fmag_subnormal(0)), 1u64 << 31),
            (32, fval(0, fmag_subnormal(1)), 1),
            (32, fval(0, fmag_normal(0, 0, 0)), 0x3f80_0000),
            (32, fval(0, fmag_normal(0, 1, 126)), 0x0080_0000),
            (32, fval(1, fmag_inf()), 0xff80_0000),
            (64, fval(0, fmag_normal(0, 0, 0)), 0x3ff0_0000_0000_0000),
            (64, fval(1, fmag_inf()), 0xfff0_0000_0000_0000),
        ];
        for (w, value, raw) in cases {
            let bytes = le_bytes(raw, (w / 8) as usize);
            let bits = low_bits_first(raw, w as usize);
            assert!(derivable_at(
                &clauses,
                &float_serialize_fact("fbits_", w, value.clone(), &bits)
            ));
            assert!(derivable_at(
                &clauses,
                &inverse_float_serialize_fact("inv_fbits_", w, &bits, value.clone())
            ));
            assert!(derivable_at(
                &clauses,
                &float_serialize_fact("fbytes_", w, value.clone(), &bytes)
            ));
            assert!(derivable_at(
                &clauses,
                &inverse_float_serialize_fact("inv_fbytes_", w, &bytes, value.clone())
            ));
            for (forward, inverse) in [
                ("nbytes_", "inv_nbytes_"),
                ("zbytes_", "inv_zbytes_"),
                ("cbytes_", "inv_cbytes_"),
            ] {
                let ty = if w == 32 { "F32" } else { "F64" };
                assert!(derivable_at(
                    &clauses,
                    &fn_graph(
                        forward,
                        &[numtype(ty).unwrap(), value.clone()],
                        &nat_list(&bytes),
                    )
                    .unwrap()
                ));
                assert!(derivable_at(
                    &clauses,
                    &fn_graph(inverse, &[numtype(ty).unwrap(), nat_list(&bytes)], &value,).unwrap()
                ));
            }
            let mut wrong = bytes.clone();
            wrong[0] ^= 1;
            assert!(!derivable_at(
                &clauses,
                &float_serialize_fact("fbytes_", w, value.clone(), &wrong)
            ));

            let (ity, fty) = if w == 32 {
                ("I32", "F32")
            } else {
                ("I64", "F64")
            };
            assert!(derivable_at(
                &clauses,
                &fn_graph(
                    "reinterpret__",
                    &[numtype(fty).unwrap(), numtype(ity).unwrap(), value.clone()],
                    &ival(nat(raw)).unwrap(),
                )
                .unwrap()
            ));
            assert!(derivable_at(
                &clauses,
                &fn_graph(
                    "reinterpret__",
                    &[
                        numtype(ity).unwrap(),
                        numtype(fty).unwrap(),
                        ival(nat(raw)).unwrap()
                    ],
                    &value,
                )
                .unwrap()
            ));
        }

        let one = fval(0, fmag_normal(0, 0, 0));
        let neg_one = fval(1, fmag_normal(0, 0, 0));
        assert!(derivable_at(
            &clauses,
            &fn_graph(
                "fabs_",
                &[w_lit(32).unwrap(), neg_one.clone()],
                &singleton(one.clone()).unwrap(),
            )
            .unwrap()
        ));
        assert!(derivable_at(
            &clauses,
            &fn_graph(
                "fneg_",
                &[w_lit(32).unwrap(), one],
                &singleton(neg_one).unwrap(),
            )
            .unwrap()
        ));

        // Representation and sign operations preserve exact NaN payloads;
        // they do not make any choice for arithmetic NaN results.
        let nan = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(1)).unwrap())).unwrap(),
        );
        assert!(derivable_at(
            &clauses,
            &float_serialize_fact("fbytes_", 32, nan.clone(), &[1, 0, 0x80, 0x7f])
        ));
        assert!(derivable_at(
            &clauses,
            &fn_graph(
                "fabs_",
                &[w_lit(32).unwrap(), nan.clone()],
                &singleton(nan).unwrap(),
            )
            .unwrap()
        ));

        // Invalid exponent, significand, and NaN shapes do not inherit a raw
        // value.
        for junk in [
            fval(0, fmag_normal(0, 0, 128)),
            fval(0, fmag_normal(1 << 23, 0, 0)),
            fval(0, fmag_normal(0, 1, 0)),
            fval(
                0,
                app(con("case.NAN"), tuple1(wrap_nat(nat(0)).unwrap())).unwrap(),
            ),
            fval(
                0,
                app(con("case.NAN"), tuple1(wrap_nat(nat(1 << 23)).unwrap())).unwrap(),
            ),
        ] {
            assert!(!derivable_at(
                &clauses,
                &float_serialize_fact("fbytes_", 32, junk, &[0; 4])
            ));
        }
    }

    #[test]
    fn structural_float_comparisons_and_copysign_are_exact() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let pz = fval(0, fmag_subnormal(0));
        let nz = fval(1, fmag_subnormal(0));
        let pone = fval(0, fmag_normal(0, 0, 0));
        let none = fval(1, fmag_normal(0, 0, 0));
        let pinf = fval(0, fmag_inf());
        let ninf = fval(1, fmag_inf());
        let nan = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(7)).unwrap())).unwrap(),
        );

        let ordered = [
            ninf.clone(),
            none.clone(),
            nz.clone(),
            pz.clone(),
            pone.clone(),
            pinf.clone(),
        ];
        for (i, left) in ordered.iter().enumerate() {
            for (j, right) in ordered.iter().enumerate() {
                let equal = (i == j) || ((i == 2 || i == 3) && (j == 2 || j == 3));
                let less = !equal && i < j;
                for (op, expected) in [
                    ("feq_", equal),
                    ("fne_", !equal),
                    ("flt_", less),
                    ("fgt_", !equal && i > j),
                    ("fle_", equal || less),
                    ("fge_", equal || i > j),
                ] {
                    let result = u64::from(expected);
                    assert!(
                        derivable_at(
                            &clauses,
                            &float_cmp_fact(op, 32, left.clone(), right.clone(), result)
                        ),
                        "{op} at ordered positions {i},{j}"
                    );
                    assert!(!derivable_at(
                        &clauses,
                        &float_cmp_fact(op, 32, left.clone(), right.clone(), 1 - result)
                    ));
                }
                let min_result = if !equal && j < i { right } else { left };
                let max_result = if !equal && i < j { right } else { left };
                for (op, result) in [("fpmin_", min_result), ("fpmax_", max_result)] {
                    assert!(
                        derivable_at(
                            &clauses,
                            &float_selection_concl(
                                op,
                                32,
                                left.clone(),
                                right.clone(),
                                result.clone(),
                            )
                            .unwrap()
                        ),
                        "{op} at ordered positions {i},{j}"
                    );
                }
                let opposite_zero = (i == 2 && j == 3) || (i == 3 && j == 2);
                let regular_min = if opposite_zero { &nz } else { min_result };
                let regular_max = if opposite_zero { &pz } else { max_result };
                for (op, result) in [("fmin_", regular_min), ("fmax_", regular_max)] {
                    assert!(
                        derivable_at(
                            &clauses,
                            &float_selection_concl(
                                op,
                                32,
                                left.clone(),
                                right.clone(),
                                result.clone(),
                            )
                            .unwrap()
                        ),
                        "regular {op} at ordered positions {i},{j}"
                    );
                }
            }
        }

        for ordinary in [pz.clone(), nz.clone(), pone.clone(), ninf] {
            for (op, expected) in [
                ("feq_", 0),
                ("fne_", 1),
                ("flt_", 0),
                ("fgt_", 0),
                ("fle_", 0),
                ("fge_", 0),
            ] {
                for (left, right) in [
                    (nan.clone(), ordinary.clone()),
                    (ordinary.clone(), nan.clone()),
                    (nan.clone(), nan.clone()),
                ] {
                    assert!(derivable_at(
                        &clauses,
                        &float_cmp_fact(op, 32, left, right, expected)
                    ));
                }
            }
            for (left, right) in [
                (nan.clone(), ordinary.clone()),
                (ordinary.clone(), nan.clone()),
                (nan.clone(), nan.clone()),
            ] {
                for op in ["fpmin_", "fpmax_"] {
                    assert!(derivable_at(
                        &clauses,
                        &float_selection_concl(op, 32, left.clone(), right.clone(), left.clone(),)
                            .unwrap()
                    ));
                }
            }
        }

        let canonical_nan = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(1 << 22)).unwrap())).unwrap(),
        );
        let signaling_nan = fval(
            1,
            app(con("case.NAN"), tuple1(wrap_nat(nat(7)).unwrap())).unwrap(),
        );
        let arithmetic_result = fval(
            0,
            app(
                con("case.NAN"),
                tuple1(wrap_nat(nat((1 << 22) + 9)).unwrap()),
            )
            .unwrap(),
        );
        for op in ["fmin_", "fmax_"] {
            for sign in [0, 1] {
                let canonical_result = fval(
                    sign,
                    app(con("case.NAN"), tuple1(wrap_nat(nat(1 << 22)).unwrap())).unwrap(),
                );
                assert!(derivable_at(
                    &clauses,
                    &float_selection_concl(
                        op,
                        32,
                        canonical_nan.clone(),
                        pone.clone(),
                        canonical_result,
                    )
                    .unwrap()
                ));
            }
            assert!(derivable_at(
                &clauses,
                &float_selection_concl(
                    op,
                    32,
                    signaling_nan.clone(),
                    canonical_nan.clone(),
                    arithmetic_result.clone(),
                )
                .unwrap()
            ));
            assert!(!derivable_at(
                &clauses,
                &float_selection_concl(
                    op,
                    32,
                    canonical_nan.clone(),
                    canonical_nan.clone(),
                    arithmetic_result.clone(),
                )
                .unwrap()
            ));
        }

        let copied = fval(1, fmag_normal(0, 0, 0));
        assert!(derivable_at(
            &clauses,
            &fn_graph(
                "fcopysign_",
                &[w_lit(32).unwrap(), pone.clone(), nz.clone()],
                &singleton(copied.clone()).unwrap(),
            )
            .unwrap()
        ));
        assert!(!derivable_at(
            &clauses,
            &fn_graph(
                "fcopysign_",
                &[w_lit(32).unwrap(), pone, nz],
                &singleton(pz).unwrap(),
            )
            .unwrap()
        ));
        // Copying a sign onto a NaN preserves its exact payload.
        let neg_nan = fval(
            1,
            app(con("case.NAN"), tuple1(wrap_nat(nat(7)).unwrap())).unwrap(),
        );
        assert!(derivable_at(
            &clauses,
            &fn_graph(
                "fcopysign_",
                &[w_lit(32).unwrap(), nan, copied],
                &singleton(neg_nan).unwrap(),
            )
            .unwrap()
        ));
    }

    #[test]
    fn profile_choice_parameters_are_exact_relations() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        for value in [con("bool.false"), con("bool.true")] {
            assert!(derivable_at(
                &clauses,
                &fn_graph("ND", &[], &value).unwrap()
            ));
        }
        assert!(!derivable_at(
            &clauses,
            &fn_graph("ND", &[], &wrap_nat(nat(0)).unwrap()).unwrap()
        ));

        for (op, cardinality) in [
            ("R_fmadd", 2u64),
            ("R_fmin", 4),
            ("R_fmax", 4),
            ("R_idot", 2),
            ("R_iq15mulr", 2),
            ("R_trunc_u", 4),
            ("R_trunc_s", 2),
            ("R_swizzle", 2),
            ("R_laneselect", 2),
        ] {
            for i in 0..cardinality {
                assert!(derivable_at(
                    &clauses,
                    &fn_graph(op, &[], &wrap_nat(nat(i)).unwrap()).unwrap()
                ));
            }
            assert!(!derivable_at(
                &clauses,
                &fn_graph(op, &[], &wrap_nat(nat(cardinality)).unwrap()).unwrap()
            ));
            assert!(!derivable_at(
                &clauses,
                &fn_graph(op, &[], &con("bool.false")).unwrap()
            ));
        }
    }

    fn float_to_int_fact(
        op: &str,
        source_w: u64,
        target_w: u64,
        sx: &str,
        value: Term,
        result: Option<u64>,
    ) -> Term {
        let result = match result {
            Some(r) => some(ival(nat(r)).unwrap()).unwrap(),
            None => con("opt.none"),
        };
        float_to_int_concl(op, source_w, target_w, sx, value, result).unwrap()
    }

    fn int_to_float_fact(source_w: u64, target_w: u64, sx: &str, input: u64, output: Term) -> Term {
        int_to_float_concl(source_w, target_w, sx, nat(input), output).unwrap()
    }

    fn float_width_conversion_fact(
        op: &str,
        source_w: u64,
        target_w: u64,
        input: Term,
        output: Term,
    ) -> Term {
        float_width_conversion_concl(op, source_w, target_w, input, output).unwrap()
    }

    fn float_unary_fact(op: &str, w: u64, input: Term, output: Term) -> Term {
        float_unary_concl(op, w, input, output).unwrap()
    }

    #[test]
    fn structural_float_integral_rounding_is_exact() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let pz = fval(0, fmag_subnormal(0));
        let nz = fval(1, fmag_subnormal(0));
        let pone = fval(0, fmag_normal(0, 0, 0));
        let none = fval(1, fmag_normal(0, 0, 0));
        let ptwo = fval(0, fmag_normal(0, 0, 1));
        let ntwo = fval(1, fmag_normal(0, 0, 1));

        for (op, input, expected) in [
            ("fceil_", fval(0, fmag_subnormal(1)), pone.clone()),
            ("ffloor_", fval(0, fmag_subnormal(1)), pz.clone()),
            ("fceil_", fval(1, fmag_subnormal(1)), nz.clone()),
            ("ffloor_", fval(1, fmag_subnormal(1)), none.clone()),
            ("ftrunc_", fval(1, fmag_subnormal(1)), nz.clone()),
            ("fnearest_", fval(1, fmag_subnormal(1)), nz.clone()),
            ("fnearest_", fval(0, fmag_normal(0, 1, 1)), pz.clone()),
            ("fnearest_", fval(0, fmag_normal(1, 1, 1)), pone.clone()),
            ("fnearest_", fval(1, fmag_normal(0, 1, 1)), nz.clone()),
            ("fnearest_", fval(1, fmag_normal(1, 1, 1)), none.clone()),
            // 1.5 ties upward to even 2; directed operations split by sign.
            (
                "fnearest_",
                fval(0, fmag_normal(1 << 22, 0, 0)),
                ptwo.clone(),
            ),
            ("ftrunc_", fval(0, fmag_normal(1 << 22, 0, 0)), pone.clone()),
            ("fceil_", fval(1, fmag_normal(1 << 22, 0, 0)), none.clone()),
            ("ffloor_", fval(1, fmag_normal(1 << 22, 0, 0)), ntwo.clone()),
            // 2.5 ties down to even 2; 3.5 ties up to even 4.
            (
                "fnearest_",
                fval(0, fmag_normal(1 << 21, 0, 1)),
                ptwo.clone(),
            ),
            (
                "fnearest_",
                fval(0, fmag_normal(3 << 21, 0, 1)),
                fval(0, fmag_normal(0, 0, 2)),
            ),
            (
                "fceil_",
                fval(1, fmag_normal(7, 0, 23)),
                fval(1, fmag_normal(7, 0, 23)),
            ),
        ] {
            assert!(
                derivable_at(
                    &clauses,
                    &float_unary_fact(op, 32, input.clone(), expected.clone())
                ),
                "{op} structural rounding"
            );
        }
        assert!(!derivable_at(
            &clauses,
            &float_unary_fact("fnearest_", 32, fval(0, fmag_normal(1 << 22, 0, 0)), pone,)
        ));

        let canonical = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(1 << 22)).unwrap())).unwrap(),
        );
        let signaling = fval(
            1,
            app(con("case.NAN"), tuple1(wrap_nat(nat(7)).unwrap())).unwrap(),
        );
        for op in ["fceil_", "ffloor_", "ftrunc_", "fnearest_"] {
            assert!(derivable_at(
                &clauses,
                &float_unary_fact(
                    op,
                    32,
                    canonical.clone(),
                    fval(
                        1,
                        app(con("case.NAN"), tuple1(wrap_nat(nat(1 << 22)).unwrap())).unwrap()
                    )
                )
            ));
            assert!(derivable_at(
                &clauses,
                &float_unary_fact(
                    op,
                    32,
                    signaling.clone(),
                    fval(
                        0,
                        app(
                            con("case.NAN"),
                            tuple1(wrap_nat(nat((1 << 22) + 5)).unwrap())
                        )
                        .unwrap()
                    )
                )
            ));
        }
    }

    #[test]
    fn structural_promotion_preserves_values_and_complete_nan_sets() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let cases = [
            (fval(0, fmag_subnormal(0)), fval(0, fmag_subnormal(0))),
            (fval(1, fmag_subnormal(0)), fval(1, fmag_subnormal(0))),
            // Smallest F32 subnormal = 2^-149, normalized exactly at F64.
            (fval(0, fmag_subnormal(1)), fval(0, fmag_normal(0, 1, 149))),
            (
                fval(0, fmag_normal(1 << 22, 0, 0)),
                fval(0, fmag_normal(1 << 51, 0, 0)),
            ),
            (
                fval(1, fmag_normal(7, 1, 12)),
                fval(1, fmag_normal(7 << 29, 1, 12)),
            ),
            (fval(1, fmag_inf()), fval(1, fmag_inf())),
        ];
        for (index, (input, expected)) in cases.into_iter().enumerate() {
            assert!(
                derivable_at(
                    &clauses,
                    &float_width_conversion_fact(
                        "promote__",
                        32,
                        64,
                        input.clone(),
                        expected.clone()
                    )
                ),
                "promotion derivation case {index}"
            );
            assert!(
                !derivable_at(
                    &clauses,
                    &float_width_conversion_fact(
                        "promote__",
                        32,
                        64,
                        input,
                        fval(1, fmag_normal(0, 0, 0))
                    )
                ),
                "promotion case {index}"
            );
        }

        let src_canon = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(1 << 22)).unwrap())).unwrap(),
        );
        let src_arithmetic = fval(
            1,
            app(
                con("case.NAN"),
                tuple1(wrap_nat(nat((1 << 22) + 7)).unwrap()),
            )
            .unwrap(),
        );
        let src_signaling = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(7)).unwrap())).unwrap(),
        );
        let nan = |sign, payload| {
            fval(
                sign,
                app(con("case.NAN"), tuple1(wrap_nat(nat(payload)).unwrap())).unwrap(),
            )
        };

        // Canonical input permits both signs, but only the target canonical
        // payload. A noncanonical arithmetic input permits both signs and
        // every arithmetic target payload.
        for sign in [0, 1] {
            assert!(derivable_at(
                &clauses,
                &float_width_conversion_fact(
                    "promote__",
                    32,
                    64,
                    src_canon.clone(),
                    nan(sign, 1 << 51)
                )
            ));
            assert!(!derivable_at(
                &clauses,
                &float_width_conversion_fact(
                    "promote__",
                    32,
                    64,
                    src_canon.clone(),
                    nan(sign, (1 << 51) + 1)
                )
            ));
            for payload in [1 << 51, (1 << 51) + 1, (1u64 << 52) - 1] {
                assert!(derivable_at(
                    &clauses,
                    &float_width_conversion_fact(
                        "promote__",
                        32,
                        64,
                        src_arithmetic.clone(),
                        nan(sign, payload)
                    )
                ));
            }
            assert!(!derivable_at(
                &clauses,
                &float_width_conversion_fact(
                    "promote__",
                    32,
                    64,
                    src_arithmetic.clone(),
                    nan(sign, (1 << 51) - 1)
                )
            ));
            assert!(derivable_at(
                &clauses,
                &float_width_conversion_fact(
                    "promote__",
                    32,
                    64,
                    src_signaling.clone(),
                    nan(sign, (1 << 51) + 3)
                )
            ));
        }
    }

    #[test]
    fn structural_demotion_rounds_every_region_and_preserves_nan_sets() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let cases = [
            (fval(1, fmag_subnormal(1)), fval(1, fmag_subnormal(0))),
            (
                fval(0, fmag_normal(1 << 51, 0, 0)),
                fval(0, fmag_normal(1 << 22, 0, 0)),
            ),
            // Halfway above 1.0 rounds down to the even significand.
            (
                fval(0, fmag_normal(1 << 28, 0, 0)),
                fval(0, fmag_normal(0, 0, 0)),
            ),
            // The next halfway point has an odd lower significand and rounds
            // upward by two F32 mantissa units.
            (
                fval(0, fmag_normal(3 << 28, 0, 0)),
                fval(0, fmag_normal(2, 0, 0)),
            ),
            // Exact half-minimum-subnormal ties to signed zero; the next F64
            // value rounds to the minimum F32 subnormal.
            (fval(0, fmag_normal(0, 1, 150)), fval(0, fmag_subnormal(0))),
            (fval(0, fmag_normal(1, 1, 150)), fval(0, fmag_subnormal(1))),
            (fval(1, fmag_normal(0, 1, 149)), fval(1, fmag_subnormal(1))),
            // Carry from the subnormal corridor reaches minimum normal.
            (
                fval(0, fmag_normal((1u64 << 52) - (1 << 29), 1, 127)),
                fval(0, fmag_normal(0, 1, 126)),
            ),
            // The overflow midpoint rounds to infinity; its predecessor
            // remains the maximum finite F32 value.
            (
                fval(0, fmag_normal((1u64 << 52) - (1 << 28), 0, 127)),
                fval(0, fmag_inf()),
            ),
            (
                fval(0, fmag_normal((1u64 << 52) - (1 << 28) - 1, 0, 127)),
                fval(0, fmag_normal((1 << 23) - 1, 0, 127)),
            ),
            (fval(1, fmag_inf()), fval(1, fmag_inf())),
        ];
        for (index, (input, expected)) in cases.into_iter().enumerate() {
            assert!(
                derivable_at(
                    &clauses,
                    &float_width_conversion_fact("demote__", 64, 32, input.clone(), expected)
                ),
                "demotion case {index}"
            );
        }

        let nan = |sign, payload| {
            fval(
                sign,
                app(con("case.NAN"), tuple1(wrap_nat(nat(payload)).unwrap())).unwrap(),
            )
        };
        let canonical = nan(0, 1 << 51);
        let arithmetic = nan(1, (1 << 51) + 1);
        for sign in [0, 1] {
            assert!(derivable_at(
                &clauses,
                &float_width_conversion_fact(
                    "demote__",
                    64,
                    32,
                    canonical.clone(),
                    nan(sign, 1 << 22)
                )
            ));
            assert!(!derivable_at(
                &clauses,
                &float_width_conversion_fact(
                    "demote__",
                    64,
                    32,
                    canonical.clone(),
                    nan(sign, (1 << 22) + 1)
                )
            ));
            for payload in [1 << 22, (1 << 22) + 1, (1 << 23) - 1] {
                assert!(derivable_at(
                    &clauses,
                    &float_width_conversion_fact(
                        "demote__",
                        64,
                        32,
                        arithmetic.clone(),
                        nan(sign, payload)
                    )
                ));
            }
        }
    }

    #[test]
    fn structural_integer_to_float_conversions_round_ties_to_even() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let cases = [
            (32, 32, "U", 0, fval(0, fmag_subnormal(0))),
            (32, 32, "U", 1, fval(0, fmag_normal(0, 0, 0))),
            (32, 32, "S", u32::MAX as u64, fval(1, fmag_normal(0, 0, 0))),
            // At 2^24 the F32 spacing is two. These exercise an even
            // downward tie, an exactly representable value, and an odd
            // upward tie respectively.
            (32, 32, "U", (1 << 24) + 1, fval(0, fmag_normal(0, 0, 24))),
            (32, 32, "U", (1 << 24) + 2, fval(0, fmag_normal(1, 0, 24))),
            (32, 32, "U", (1 << 24) + 3, fval(0, fmag_normal(2, 0, 24))),
            // Sign is applied after exact magnitude rounding.
            (
                32,
                32,
                "S",
                (u32::MAX as u64 + 1) - ((1 << 24) + 3),
                fval(1, fmag_normal(2, 0, 24)),
            ),
            // Rounding can carry into the next exponent at each 64-bit
            // endpoint; F64 still represents the resulting powers exactly.
            (64, 64, "S", i64::MAX as u64, fval(0, fmag_normal(0, 0, 63))),
            (64, 64, "U", u64::MAX, fval(0, fmag_normal(0, 0, 64))),
            (64, 64, "U", (1 << 52) + 1, fval(0, fmag_normal(1, 0, 52))),
        ];

        for (source_w, target_w, sx, input, expected) in cases {
            let fact = int_to_float_fact(source_w, target_w, sx, input, expected.clone());
            assert!(
                derivable_at(&clauses, &fact),
                "convert {source_w}->{target_w} {sx} {input}"
            );
            let wrong_sign = if expected == fval(0, fmag_subnormal(0)) {
                fval(1, fmag_subnormal(0))
            } else {
                // Every nonzero expected case above is finite and has a
                // uniquely determined sign; flipping it must fail closed.
                let expected_negative = sx == "S" && input >= (1u64 << (source_w - 1));
                if expected_negative {
                    fval(0, fmag_normal(0, 0, 0))
                } else {
                    fval(1, fmag_normal(0, 0, 0))
                }
            };
            assert!(!derivable_at(
                &clauses,
                &int_to_float_fact(source_w, target_w, sx, input, wrong_sign)
            ));
        }

        // Erased numeric encodings retain their exact source carrier.
        assert!(!derivable_at(
            &clauses,
            &int_to_float_fact(32, 32, "U", 1u64 << 32, fval(0, fmag_normal(0, 0, 32)))
        ));
    }

    #[test]
    fn structural_float_to_integer_conversions_are_exact() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.clauses, 10498);
        assert_eq!(report.ops, 85);
        assert_eq!(report.zero_clause_ops, 74);

        let nan = fval(
            0,
            app(con("case.NAN"), tuple1(wrap_nat(nat(7)).unwrap())).unwrap(),
        );
        let pinf = fval(0, fmag_inf());
        let ninf = fval(1, fmag_inf());
        let plus_one_half = fval(0, fmag_normal(1 << 22, 0, 0));
        let minus_one_half = fval(1, fmag_normal(1 << 22, 0, 0));
        let plus_i32_limit = fval(0, fmag_normal(0, 0, 31));
        let minus_i32_limit = fval(1, fmag_normal(0, 0, 31));
        let plus_u32_limit = fval(0, fmag_normal(0, 0, 32));
        let negative_subnormal = fval(1, fmag_subnormal(1));

        for (op, value, sx, expected) in [
            ("trunc__", nan.clone(), "U", None),
            ("trunc__", pinf.clone(), "S", None),
            ("trunc__", plus_one_half.clone(), "U", Some(1)),
            (
                "trunc__",
                minus_one_half.clone(),
                "S",
                Some(u32::MAX as u64),
            ),
            ("trunc__", minus_one_half.clone(), "U", None),
            ("trunc__", plus_i32_limit.clone(), "U", Some(1u64 << 31)),
            ("trunc__", plus_i32_limit.clone(), "S", None),
            ("trunc__", minus_i32_limit.clone(), "S", Some(1u64 << 31)),
            ("trunc__", plus_u32_limit.clone(), "U", None),
            ("trunc__", negative_subnormal.clone(), "S", Some(0)),
            ("trunc_sat__", nan, "U", Some(0)),
            ("trunc_sat__", pinf, "U", Some(u32::MAX as u64)),
            ("trunc_sat__", ninf, "S", Some(1u64 << 31)),
            ("trunc_sat__", plus_one_half, "U", Some(1)),
            ("trunc_sat__", minus_one_half, "U", Some(0)),
            ("trunc_sat__", plus_i32_limit, "S", Some(i32::MAX as u64)),
            ("trunc_sat__", minus_i32_limit, "S", Some(1u64 << 31)),
            ("trunc_sat__", plus_u32_limit, "U", Some(u32::MAX as u64)),
            ("trunc_sat__", negative_subnormal, "S", Some(0)),
        ] {
            assert!(
                derivable_at(
                    &clauses,
                    &float_to_int_fact(op, 32, 32, sx, value.clone(), expected)
                ),
                "{op} {sx} expected {expected:?}"
            );
            if let Some(expected) = expected {
                assert!(!derivable_at(
                    &clauses,
                    &float_to_int_fact(
                        op,
                        32,
                        32,
                        sx,
                        value,
                        Some(expected.wrapping_add(1) & 0xffff_ffff),
                    )
                ));
            }
        }
    }
}
