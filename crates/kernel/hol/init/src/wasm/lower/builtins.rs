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
/// Widths for the scalar-only partial ops `idiv_` / `irem_`.
pub const DIV_WIDTHS: [u64; 2] = [32, 64];

/// Integer ops given defining clauses by this leg.
pub const OPS: [&str; 16] = [
    "isub_", "ieq_", "ine_", "ilt_", "igt_", "ile_", "ige_", "ieqz_", "ishl_", "ishr_", "irotl_",
    "irotr_", "iclz_", "ictz_", "idiv_", "irem_",
];

/// How many of the 91 zero-clause builtin tags gain their **first** clauses
/// here (`ishl_`, `ishr_`, `irotl_`, `irotr_`, `iclz_`, `ictz_`); the other
/// ten [`OPS`] supplement blocked spec lowerings.
pub const ZERO_CLAUSE_OPS_COVERED: usize = 6;

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
}
