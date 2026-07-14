//! The **Farkas certificate checker** — pure rational linear algebra,
//! backend-independent. This is the arithmetic heart of Alethe's `la_generic`
//! rule (and `la_tautology`'s inequality case): given the asserted linear
//! literals (the negations of a tautological clause) already normalised to the
//! spec's `s ⋈ d` orientation, plus one rational coefficient per literal, it
//! checks that the nonnegative combination sums to a manifest falsehood
//! (`0 > 0`, `0 ≥ d>0`, `0 = d≠0`).
//!
//! It implements the Alethe specification's checking procedure — step 4
//! (integer strengthening) and step 5 (scaling), then the sum-to-contradiction
//! test. Steps 1–3 (negate / strip / normalise each literal into `s ⋈ d`
//! form) are the frontend's job (they need to read the concrete term syntax);
//! this module takes over once every literal is a [`NormLit`].
//!
//! Checking the certificate is entirely separate from *re-deriving* it in the
//! kernel: this module answers "is the cvc5/veriT certificate arithmetically
//! valid?" as data; [`crate::replay`] turns a valid certificate into `⊢ ⊥`
//! through the ordered-ring proof primitives. Keeping them apart is what lets
//! the same checker serve every backend (HOL, internal-PA, …).
//!
//! Reference: Alethe spec `la_generic` (steps 1–5); Carcara
//! `checker/rules/linear_arithmetic.rs`.

use crate::lincomb::LinComb;
use crate::rational::Rational;

/// A linear relation, in the spec's post-normalisation orientation (only `>`,
/// `≥`, `≈` occur after steps 1–2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel {
    /// strict `>`
    Gt,
    /// non-strict `≥`
    Ge,
    /// equality `≈`
    Eq,
}

impl Rel {
    /// The "most strict" relation of a sum of rows: `>` dominates, then `≥`,
    /// else `≈` (the accumulator identity).
    fn combine(self, other: Rel) -> Rel {
        match (self, other) {
            (Rel::Gt, _) | (_, Rel::Gt) => Rel::Gt,
            (Rel::Ge, _) | (_, Rel::Ge) => Rel::Ge,
            (Rel::Eq, Rel::Eq) => Rel::Eq,
        }
    }
}

/// A normalised arithmetic literal `s ⋈ d`: `s` a linear combination of atoms,
/// `⋈` one of `>`/`≥`/`≈`, `d` a rational constant. This is the output of the
/// frontend's steps 1–3.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormLit<A: Ord + Clone> {
    pub s: LinComb<A>,
    pub rel: Rel,
    pub d: Rational,
}

/// Why a Farkas certificate failed to check.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FarkasError {
    #[error("Farkas: {got} coefficients for {want} literals")]
    CoeffArity { want: usize, got: usize },
    #[error("Farkas: coefficient/constant arithmetic overflowed i128")]
    Overflow,
    #[error("Farkas: rows do not sum to a contradiction (residual left-hand side is non-zero)")]
    ResidualNonZero,
    #[error("Farkas: summed to `0 {rel:?} {d:?}`, which is not a contradiction")]
    NotContradiction { rel: Rel, d: Rational },
}

/// A checked certificate: each literal after strengthening + scaling, plus the
/// summed relation and constant (the manifest contradiction `0 sum_rel sum_d`).
/// [`crate::replay`] consumes this to build the kernel refutation.
#[derive(Clone, Debug)]
pub struct FarkasCert<A: Ord + Clone> {
    /// Per-input-literal, after step 4 (strengthen) and step 5 (scale by its
    /// coefficient). Summing the `s` fields gives `0`; summing the `d` fields
    /// gives `sum_d`.
    pub scaled: Vec<NormLit<A>>,
    pub sum_rel: Rel,
    pub sum_d: Rational,
}

/// Integer strengthening (spec step 4) of a single literal, when all variables
/// are integer-sorted. `>`/`≥` with a non-integer bound tighten to the next
/// integer; `>` with an integer bound tightens by `+1`. `≈` is unchanged.
///
/// This is the simple per-spec strengthening. The stronger GCD variant Carcara
/// uses (`d ↦ ⌊d⌋ + gcd(coeffs)`) is not yet applied — see `SKELETONS.md`.
fn strengthen(lit: &NormLit<impl Ord + Clone>) -> (Rel, Rational) {
    match lit.rel {
        Rel::Eq => (Rel::Eq, lit.d),
        Rel::Gt if lit.d.is_integer() => (Rel::Ge, Rational::from_int(lit.d.num() + 1)),
        Rel::Gt | Rel::Ge if !lit.d.is_integer() => {
            (Rel::Ge, Rational::from_int(lit.d.floor() + 1))
        }
        // `≥` with an integer bound: already tight.
        Rel::Ge => (Rel::Ge, lit.d),
        Rel::Gt => unreachable!("integer Gt handled above"),
    }
}

/// Check a Farkas certificate.
///
/// `lits` are the asserted literals (already in `s ⋈ d` orientation, spec steps
/// 1–3 done by the frontend), each paired with its rational coefficient. Over
/// the integers set `integer = true` to enable the strengthening step. On
/// success returns the processed [`FarkasCert`]; on failure a [`FarkasError`]
/// explaining why the certificate is not a valid refutation.
pub fn check<A: Ord + Clone>(
    lits: &[(NormLit<A>, Rational)],
    integer: bool,
) -> Result<FarkasCert<A>, FarkasError> {
    let mut scaled = Vec::with_capacity(lits.len());
    let mut sum_s: LinComb<A> = LinComb::new();
    let mut sum_d = Rational::ZERO;
    let mut sum_rel = Rel::Eq;

    for (lit, coeff) in lits {
        // Step 4: strengthen (integers only).
        let (rel, d) = if integer {
            strengthen(lit)
        } else {
            (lit.rel, lit.d)
        };

        // Step 5: scale by `coeff` (equalities keep the sign; inequalities use
        // `|coeff|`, since the orientation is fixed to `>`/`≥`).
        let factor = if rel == Rel::Eq { *coeff } else { coeff.abs() };
        let mut s = lit.s.clone();
        if !s.scale(factor) {
            return Err(FarkasError::Overflow);
        }
        let d = d.mul(&factor).ok_or(FarkasError::Overflow)?;

        // Accumulate.
        if !sum_s.add_assign(&s) {
            return Err(FarkasError::Overflow);
        }
        sum_d = sum_d.add(&d).ok_or(FarkasError::Overflow)?;
        // A zero-coefficient row drops out of the relation (it contributes
        // nothing); otherwise it participates in the most-strict fold.
        if !factor.is_zero() {
            sum_rel = sum_rel.combine(rel);
        }
        scaled.push(NormLit { s, rel, d });
    }

    // The variable part must cancel to zero.
    if !sum_s.is_empty() {
        return Err(FarkasError::ResidualNonZero);
    }
    // `0 sum_rel sum_d` must be false: `≥ d` needs d > 0; `> d` needs d ≥ 0;
    // `= d` needs d ≠ 0.
    let contradictory = match sum_rel {
        Rel::Ge => sum_d.signum() > 0,
        Rel::Gt => sum_d.signum() >= 0,
        Rel::Eq => sum_d.signum() != 0,
    };
    if !contradictory {
        return Err(FarkasError::NotContradiction {
            rel: sum_rel,
            d: sum_d,
        });
    }
    Ok(FarkasCert {
        scaled,
        sum_rel,
        sum_d,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lc(pairs: &[(&str, i128)]) -> LinComb<String> {
        let mut lc = LinComb::new();
        for (a, c) in pairs {
            assert!(lc.add_term(a.to_string(), Rational::from_int(*c)));
        }
        lc
    }
    fn q(n: i128, d: i128) -> Rational {
        Rational::new(n, d).unwrap()
    }

    /// Spec LRA example: `(f a) > (f b) ∧ (f a) = (f b)`, coeffs `(1, -1)`,
    /// sums to `0 > 0`.
    #[test]
    fn lra_gt_eq_cycle() {
        let lits = vec![
            (
                NormLit {
                    s: lc(&[("fa", 1), ("fb", -1)]),
                    rel: Rel::Gt,
                    d: Rational::ZERO,
                },
                Rational::ONE,
            ),
            (
                NormLit {
                    s: lc(&[("fa", 1), ("fb", -1)]),
                    rel: Rel::Eq,
                    d: Rational::ZERO,
                },
                Rational::from_int(-1),
            ),
        ];
        let cert = check(&lits, false).expect("valid Farkas");
        assert_eq!(cert.sum_rel, Rel::Gt);
        assert_eq!(cert.sum_d, Rational::ZERO);
    }

    /// Spec QF_UFLIA example: `−f3 ≥ 0 ∧ 4·f3 > 0`, coeffs `(1, 1/4)`.
    /// Strengthen `4f3 > 0 ↦ 4f3 ≥ 1`, scale by 1/4 ↦ `f3 ≥ 1/4`, sum `0 ≥ 1/4`.
    #[test]
    fn uflia_strengthening() {
        let lits = vec![
            (
                NormLit {
                    s: lc(&[("f3", -1)]),
                    rel: Rel::Ge,
                    d: Rational::ZERO,
                },
                Rational::ONE,
            ),
            (
                NormLit {
                    s: lc(&[("f3", 4)]),
                    rel: Rel::Gt,
                    d: Rational::ZERO,
                },
                q(1, 4),
            ),
        ];
        let cert = check(&lits, true).expect("valid Farkas");
        assert_eq!(cert.sum_rel, Rel::Ge);
        assert_eq!(cert.sum_d, q(1, 4));
    }

    /// Without strengthening the same certificate does NOT check (`4f3 > 0`
    /// scaled by 1/4 gives `f3 > 0`, summing to `0 > 0` — but the coefficient
    /// makes the constant 0, and `−f3 ≥ 0` + `f3 > 0` → `0 > 0`, which *is*
    /// contradictory; so this instead confirms strengthening is what turns the
    /// `≥ 1/4` bound tight). Here we check a genuinely non-contradictory combo.
    #[test]
    fn rejects_non_contradiction() {
        // `x ≥ 0` alone, coeff 1: sums to `0 ≥ 0` — not a contradiction.
        let lits = vec![(
            NormLit {
                s: lc(&[("x", 1)]),
                rel: Rel::Ge,
                d: Rational::ZERO,
            },
            Rational::ONE,
        )];
        // Residual `x` is non-zero, so it fails on the residual check first.
        assert!(matches!(
            check(&lits, false),
            Err(FarkasError::ResidualNonZero)
        ));
    }

    /// Two strict opposed bounds `x > 0 ∧ −x > 0` sum to `0 > 0`.
    #[test]
    fn strict_opposed() {
        let lits = vec![
            (
                NormLit {
                    s: lc(&[("x", 1)]),
                    rel: Rel::Gt,
                    d: Rational::ZERO,
                },
                Rational::ONE,
            ),
            (
                NormLit {
                    s: lc(&[("x", -1)]),
                    rel: Rel::Gt,
                    d: Rational::ZERO,
                },
                Rational::ONE,
            ),
        ];
        let cert = check(&lits, false).expect("valid");
        assert_eq!(cert.sum_rel, Rel::Gt);
        assert_eq!(cert.sum_d, Rational::ZERO);
    }
}
