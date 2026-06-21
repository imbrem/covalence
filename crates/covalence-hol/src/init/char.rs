//! `char` theorems: the `defs/text.rs` `char` type re-exported, the
//! `nat`-subtype `abs`/`rep` seam, and the basic codepoint round-trip
//! lemmas. Same abstraction-barrier shape as [`init::list`] /
//! [`init::option`].
//!
//! [`init::list`]: crate::init::list
//! [`init::option`]: crate::init::option
//!
//! ## What `char` is
//!
//! ```text
//! char := { c : nat | c < 0xD800 ∨ (0xDFFF < c ∧ c < 0x110000) }
//! ```
//!
//! A Unicode **scalar value**: the natural numbers carved down to the
//! Unicode scalar range `0 ..= 0x10FFFF` **excluding** the UTF-16
//! surrogate block `0xD800 ..= 0xDFFF`. The selector predicate is
//! disjunctive (below the surrogate block, or above it and in range),
//! matching Rust's `char`.
//!
//! The named coercions are
//!
//! - [`char_code`] `: char → nat` — the `rep` coercion (`λc. rep c`),
//! - [`char_mk`] `: nat → char` — the `abs` coercion (`λn. abs n`).
//!
//! Because `char` is a genuine **subtype** (not a newtype), the
//! carrier-side round-trip [`Thm::spec_rep_abs_fwd`] is *conditional* on
//! the scalar-value selector predicate — exactly like the finiteness
//! gate in [`init::list`]. For a *literal* codepoint that premise is a
//! closed `nat.lt`/`∧`/`∨` proposition, decided by [`reduce`], so
//! [`code_mk`] is genuine (hypothesis- and oracle-free) at every Unicode
//! scalar value (and **errors on surrogates** and out-of-range
//! codepoints — the predicate reduces to `F`). The wrapper-side
//! round-trip [`mk_code`] is unconditional ([`Thm::spec_abs_rep`]).

use covalence_core::{Error, Result, Term, Thm};

use crate::init::ext::{TermExt, ThmExt};

pub use covalence_core::defs::{
    CHAR_MAX_EXCL, SURROGATE_HI, SURROGATE_LO, char_code, char_mk, char_spec, char_ty,
};

use covalence_core::defs::{and, char_code_spec, char_mk_spec, nat_lt, or};

// ============================================================================
// Term helpers (private — the public surface is the lemmas + builders).
// ============================================================================

/// `char.code c : nat` — codepoint access as a builder.
fn code(c: &Term) -> Term {
    Term::app(char_code(), c.clone())
}

/// `char.mk n : char` — character construction as a builder.
fn mk(n: &Term) -> Term {
    Term::app(char_mk(), n.clone())
}

/// `(n < 0xD800) ∨ (0xDFFF < n ∧ n < 0x110000) : bool` — the
/// scalar-value selector predicate body at `n`. Must match the
/// β-reduction of `defs::char` predicate at `n` exactly (so the
/// `spec_rep_abs_fwd` premise bridges).
fn in_range(n: &Term) -> Term {
    let lt = |a: Term, b: Term| Term::app(Term::app(nat_lt(), a), b);
    // n < 0xD800
    let below = lt(n.clone(), Term::nat_lit(SURROGATE_LO));
    // 0xDFFF < n  ∧  n < 0x110000
    let above = Term::app(
        Term::app(and(), lt(Term::nat_lit(SURROGATE_HI), n.clone())),
        lt(n.clone(), Term::nat_lit(CHAR_MAX_EXCL)),
    );
    Term::app(Term::app(or(), below), above)
}

// ============================================================================
// THE SEAM — the only code aware that `char` is a subtype of `nat`
// carved by `λc. c < 0x110000`.
//
//   abs : nat → char       rep : char → nat
//
// `char.code = λc. rep c` and `char.mk = λn. abs n`, so `code (mk n)`
// unfolds to `rep (abs n)`, whose `= n` collapse is *conditional* on
// `n < 0x110000` (the subtype premise — dischargeable by `reduce` for a
// literal `n`).
// ============================================================================

/// `⊢ char.code (char.mk n) = rep (abs n)` — unfold both named
/// coercions to the raw `nat`-subtype `abs`/`rep`. No round-trip
/// collapse yet, so `n` stays opaque.
fn code_mk_unfold(n: &Term) -> Result<Thm> {
    // char.code (char.mk n) = char.code (char.mk n), then δ-unfold the
    // two `let`-defined coercions and β-reduce.
    code(&mk(n))
        .delta_all(char_code_spec().symbol())?
        .rhs_conv(|t| t.delta_all(char_mk_spec().symbol()))?
        .rhs_conv(|t| t.reduce())
}

/// `⊢ rep (abs n) = n`, given `prem : ⊢ n < 0x110000` (the bare
/// in-range comparison) — the carrier-side round-trip with the subtype
/// premise discharged. From the kernel's conditional
/// [`Thm::spec_rep_abs_fwd`].
fn rep_abs_in_range(n: &Term, prem: Thm) -> Result<Thm> {
    let fwd = Thm::spec_rep_abs_fwd(char_spec(), Vec::new(), n.clone())?;
    // The premise of `fwd` is the un-β-reduced `(λc. c < 0x110000) n`;
    // bridge `⊢ comparison` across `β : ⊢ (λc…) n = comparison`.
    let (imp_p, _eq) = fwd.concl().as_app().ok_or(Error::NotAnEquation)?;
    let (_imp, beta_prem) = imp_p.as_app().ok_or(Error::NotAnEquation)?;
    let prem_thm = Thm::beta_conv(beta_prem.clone())?.sym()?.eq_mp(prem)?;
    fwd.imp_elim(prem_thm)
}

// ============================================================================
// Round-trip lemmas — the high-level computational surface.
// ============================================================================

/// `⊢ char.code (char.mk n) = n` for a literal `n` that is a Unicode
/// **scalar value** (`n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)`).
/// Genuine: hypothesis- and oracle-free — the subtype premise is a
/// closed `nat.lt`/`∧`/`∨` proposition, decided by [`reduce`]. Errors if
/// `n` is a surrogate (`0xD800 ..= 0xDFFF`) or out of range (the
/// predicate reduces to `F`, so the round-trip does not hold).
pub fn code_mk(n: &Term) -> Result<Thm> {
    // Reduce the closed predicate: the `nat.lt` atoms fold to bool
    // literals, but `reduce` does NOT decide the `∧`/`∨` connectives
    // (defined constants), so the result is a bool-literal combination
    // like `(T ∨ (F ∧ T))`. Decide that combination = T with `prop_eq`
    // (the complete propositional decider) — the `init/prop.rs` pattern.
    let red = in_range(n).reduce()?; // ⊢ predicate(n) = <bool-literal combination>
    let reduced = red.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let to_t = crate::init::logic::prop_eq(&reduced, &Term::bool_lit(true)).map_err(|_| {
        Error::ConnectiveRule(
            "char::code_mk: codepoint is not a Unicode scalar value \
             (must be < 0xD800 or in 0xE000..0x110000)"
                .into(),
        )
    })?; // ⊢ <combination> = T  (errors if it is F — surrogate / out of range)
    let prem = red.trans(to_t)?.eqt_elim()?; // ⊢ predicate(n)
    let unfold = code_mk_unfold(n)?; // char.code (char.mk n) = rep (abs n)
    let collapse = rep_abs_in_range(n, prem)?; // rep (abs n) = n
    unfold.trans(collapse)
}

/// `⊢ char.mk (char.code c) = c` for any `c : char` — the
/// **unconditional** wrapper-side round-trip (`char.mk ∘ char.code =
/// id`), from the kernel's [`Thm::spec_abs_rep`]. `c` stays opaque (no
/// constructor needed). Genuine: hypothesis- and oracle-free.
pub fn mk_code(c: &Term) -> Result<Thm> {
    // char.mk (char.code c) = char.mk (char.code c); unfold both named
    // coercions to `abs (rep c)`, then collapse via `spec_abs_rep`.
    let unfold = mk(&code(c))
        .delta_all(char_mk_spec().symbol())?
        .rhs_conv(|t| t.delta_all(char_code_spec().symbol()))?
        .rhs_conv(|t| t.reduce())?; // char.mk (char.code c) = abs (rep c)
    let collapse = Thm::spec_abs_rep(char_spec(), Vec::new(), c.clone())?; // abs (rep c) = c
    unfold.trans(collapse)
}

// ============================================================================
// High-level term builders (pure construction — no proof).
// ============================================================================

/// `char.mk k : char` — the character literal for codepoint `k`. Builds
/// the term only (no in-range proof); pair with [`code_mk`] to discharge
/// the round-trip when `k < 0x110000`.
pub fn char_lit(k: u64) -> Term {
    mk(&Term::nat_lit(k))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat_lit(k: u64) -> Term {
        Term::nat_lit(k)
    }

    #[test]
    fn char_lit_is_well_typed() {
        // 'A' = char.mk 65 : char
        let a = char_lit(65);
        assert_eq!(a.type_of().unwrap(), char_ty());
    }

    #[test]
    fn code_mk_round_trips_for_ascii() {
        // ⊢ char.code (char.mk 65) = 65   ('A')
        let n = nat_lit(65);
        let thm = code_mk(&n).unwrap();
        assert!(thm.hyps().is_empty(), "code_mk is proved, not postulated");
        assert!(thm.has_no_obs(), "code_mk is oracle-free");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &code(&mk(&n)));
        assert_eq!(rhs, &n);
    }

    #[test]
    fn code_mk_round_trips_at_max_codepoint() {
        // ⊢ char.code (char.mk 0x10FFFF) = 0x10FFFF — the largest valid
        // codepoint (0x110000 - 1).
        let n = nat_lit(CHAR_MAX_EXCL - 1);
        let thm = code_mk(&n).unwrap();
        assert!(thm.hyps().is_empty() && thm.has_no_obs());
        assert_eq!(thm.concl().as_eq().unwrap().1, &n);
    }

    #[test]
    fn code_mk_rejects_out_of_range() {
        // char.mk 0x110000 is out of range — the round-trip must NOT be a
        // theorem (the predicate reduces to F).
        assert!(code_mk(&nat_lit(CHAR_MAX_EXCL)).is_err());
        // And a clearly-too-large codepoint.
        assert!(code_mk(&nat_lit(0xFFFFFF)).is_err());
    }

    #[test]
    fn code_mk_rejects_surrogates() {
        // The UTF-16 surrogate block 0xD800..=0xDFFF is NOT a scalar value:
        // char.mk on any surrogate must reject (predicate reduces to F).
        assert!(code_mk(&nat_lit(SURROGATE_LO)).is_err()); // 0xD800
        assert!(code_mk(&nat_lit(0xDABC)).is_err()); // mid-block
        assert!(code_mk(&nat_lit(SURROGATE_HI)).is_err()); // 0xDFFF
    }

    #[test]
    fn code_mk_round_trips_around_the_surrogate_block() {
        // The scalar values bracketing the surrogate gap both round-trip:
        // 0xD7FF (last before) and 0xE000 (first after).
        for &k in &[SURROGATE_LO - 1, SURROGATE_HI + 1] {
            let n = nat_lit(k);
            let thm = code_mk(&n).unwrap();
            assert!(thm.hyps().is_empty() && thm.has_no_obs());
            assert_eq!(thm.concl().as_eq().unwrap().1, &n);
        }
    }

    #[test]
    fn mk_code_round_trips_for_opaque_char() {
        // ⊢ char.mk (char.code c) = c for an arbitrary c : char.
        let c = Term::free("c", char_ty());
        let thm = mk_code(&c).unwrap();
        assert!(thm.hyps().is_empty(), "mk_code is proved, not postulated");
        assert!(thm.has_no_obs(), "mk_code is oracle-free");
        let (lhs, rhs) = thm.concl().as_eq().unwrap();
        assert_eq!(lhs, &mk(&code(&c)));
        assert_eq!(rhs, &c);
    }
}
