//! **Integer-builtin defining clauses** — per-width supplementary `fn.*`
//! clauses for the WASM integer numerics (spec §4.3.2, *Integer Operations*),
//! the biggest fireability unlock of the Dec leg: arithmetic execution.
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
//! re-checks the arithmetic itself each time a clause fires.
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
//!   `r ≥ N`, which contradicts the bounds). `ipopcnt_` has no similarly
//!   clean single-antecedent shape — it stays frontier (censused).
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
use super::evalrel::wrap_nat;
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

/// Integer ops given defining clauses by this leg.
pub const OPS: [&str; 36] = [
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
];

/// How many of the 91 zero-clause builtin tags gain their **first** clauses
/// here: the six shift/rotate/count-zero operations, eight exact bit-structure
/// operations, four integer serialization/inverse operations, the exact
/// integer SIMD lane isomorphism, and three integer conversions. The other
/// eleven [`OPS`] supplement blocked spec lowerings.
pub const ZERO_CLAUSE_OPS_COVERED: usize = 25;

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

    use crate::wasm::encode::{metavar_name, phi};
    use crate::wasm::lower::flatten::prove_side;

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
        assert_eq!(report.ops, 36);
        assert_eq!(report.zero_clause_ops, 25);

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
        assert_eq!(report.clauses, 309);
        assert_eq!(report.ops, 36);
        assert_eq!(report.zero_clause_ops, 25);

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
    fn unsigned_rounded_average_is_exact_and_fail_closed() {
        let (clauses, report) = builtin_clauses().unwrap();
        assert_eq!(report.ops, 36);
        assert_eq!(report.zero_clause_ops, 25);

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
}
