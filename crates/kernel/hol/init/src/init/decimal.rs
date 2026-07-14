//! `decimal` — finite decimals `m / 10^k` (denominator a power of ten),
//! sitting between [`init::int`](crate::init::int) and
//! [`init::rat`](crate::init::rat) in the numeric tower
//! `nat ⊂ int ⊂ decimal ⊂ rat ⊂ real`.
//!
//! ## The construction
//!
//! A finite decimal is a pair `(m, k) : int × nat` denoting the rational
//! `m / 10^k` — an integer numerator `m` scaled down by a power of ten. This
//! is a *structural* builder (not a quotient): distinct pairs `(15, 1)` and
//! `(150, 2)` name the same decimal `1.5`, and the identification is deferred
//! to the rational injection [`to_rat`] rather than being carved into the
//! carrier. (Normalisation — reducing `(m, k)` so `10 ∤ m` — is a separate,
//! optional operation; the *value* is fixed by [`to_rat`].)
//!
//! - **Carrier.** [`dec_ty`] `= int × nat`; [`mk_dec`] `m k = pair m k`.
//! - **Injection.** [`to_rat`] `d = (of_int (fst d)) / (of_int (natToInt
//!   (10 ^ snd d)))` — the numerator embedded through `int ↪ rat` divided by
//!   the power-of-ten denominator promoted `nat → int → rat`. This is the
//!   canonical map into the rationals, and it is where two representations of
//!   the same decimal become equal.
//!
//! ## Status
//!
//! The injection lemma [`to_rat_mk_dec`] — `⊢ toRat (mkDec m k) =
//! of_int m / of_int (natToInt (10 ^ k))` — is **genuinely proved**
//! (hypothesis-free) by β-reduction plus the proved product projections
//! [`fst_pair`](crate::init::prod::fst_pair) /
//! [`snd_pair`](crate::init::prod::snd_pair); no new kernel rule, axiom, or
//! oracle is introduced. It is the defining property of `toRat` on a built
//! decimal.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::defs::{fst, nat_pow, nat_to_int, pair, snd};
use covalence_hol_eval::mk_nat;

use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::{TermExt, ThmExt};
use crate::init::{prod, rat};

// ============================================================================
// Carrier + builder
// ============================================================================

/// `decimal = int × nat` — a finite decimal `(m, k)` denoting `m / 10^k`.
pub fn dec_ty() -> Type {
    prod::prod(Type::int(), Type::nat())
}

/// `mkDec m k = pair m k : decimal` — the structural builder for `m / 10^k`.
pub fn mk_dec(m: &Term, k: &Term) -> Term {
    Term::app(
        Term::app(pair(Type::int(), Type::nat()), m.clone()),
        k.clone(),
    )
}

// ============================================================================
// The rational injection `toRat : decimal → rat`
// ============================================================================

/// `10 : nat` — the base of the decimal exponent.
fn ten() -> Term {
    mk_nat(10u32)
}

/// `10 ^ e : nat` — the power-of-ten denominator (before the `nat → int`
/// promotion), for an exponent term `e : nat`.
fn pow10(e: Term) -> Term {
    Term::app(Term::app(nat_pow(), ten()), e)
}

/// `of_int (natToInt (10 ^ e)) : rat` — the denominator `10^e` promoted
/// `nat → int → rat`.
fn den_rat(e: Term) -> Term {
    let as_int = Term::app(nat_to_int(), pow10(e));
    Term::app(rat::of_int(), as_int)
}

/// `of_int n : rat` — the numerator `n : int` embedded into the rationals.
fn num_rat(n: Term) -> Term {
    Term::app(rat::of_int(), n)
}

/// The body of [`to_rat`] applied to a numerator `n : int` and exponent
/// `e : nat`: `ratDiv (of_int n) (of_int (natToInt (10 ^ e)))`.
fn to_rat_body(n: Term, e: Term) -> Term {
    Term::app(Term::app(rat::rat_div(), num_rat(n)), den_rat(e))
}

/// `toRat : decimal → rat` ≡
/// `λd. (of_int (fst d)) / (of_int (natToInt (10 ^ snd d)))` — the canonical
/// injection of a finite decimal into the rationals. Two decimals with the
/// same value (e.g. `(15, 1)` and `(150, 2)`) map to equal rationals.
pub fn to_rat() -> Term {
    let d = Term::free("d", dec_ty());
    let n = Term::app(fst(Type::int(), Type::nat()), d.clone());
    let e = Term::app(snd(Type::int(), Type::nat()), d.clone());
    let body = to_rat_body(n, e);
    Term::abs(dec_ty(), subst::close(&body, "d"))
}

/// `⊢ toRat (mkDec m k) = of_int m / of_int (natToInt (10 ^ k))` — the
/// **proved** defining property of [`to_rat`] on a built decimal, for free
/// `m : int`, `k : nat`. β-reduce `toRat` at `mkDec m k`, then resolve the
/// stuck `fst (pair m k)` / `snd (pair m k)` projections by the proved
/// [`prod::fst_pair`] / [`prod::snd_pair`]. Hypothesis- and oracle-free.
pub fn to_rat_at(m: &Term, k: &Term) -> Result<Thm> {
    let applied = Term::app(to_rat(), mk_dec(m, k));
    // β: toRat (mkDec m k) = ratDiv (of_int (fst (pair m k)))
    //                                (of_int (natToInt (10 ^ snd (pair m k))))
    let beta = Thm::beta_conv(applied)?;
    let (i, n) = (Type::int(), Type::nat());
    let fst_eq = prod::fst_pair(&i, &n, m, k)?; // fst (pair m k) = m
    let snd_eq = prod::snd_pair(&i, &n, m, k)?; // snd (pair m k) = k
    // Rewrite the projections in the RHS to get the canonical `m / 10^k` form.
    beta.rhs_conv(|t| {
        let e1 = t.rw_all(&fst_eq)?; // t = t[fst(pair m k) := m]
        let t1 = e1
            .concl()
            .as_eq()
            .ok_or(covalence_core::Error::NotAnEquation)?
            .1
            .clone();
        let e2 = t1.rw_all(&snd_eq)?; // = t[…][snd(pair m k) := k]
        e1.trans(e2)
    })
}

cached_thm! {
    /// `⊢ ∀(m:int)(k:nat). toRat (mkDec m k) = of_int m / of_int (natToInt
    /// (10 ^ k))` — the ∀-closed [`to_rat_at`]. **Proved**, hypothesis-free.
    pub fn to_rat_mk_dec() -> Result<Thm> {
        let (m, k) = (Term::free("m", Type::int()), Term::free("k", Type::nat()));
        to_rat_at(&m, &k)?
            .all_intro("k", Type::nat())?
            .all_intro("m", Type::int())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_eval::mk_int;

    /// `decimal` is `int × nat`.
    #[test]
    fn carrier_type() {
        assert_eq!(dec_ty(), prod::prod(Type::int(), Type::nat()));
    }

    /// `mkDec : int → nat → decimal` and `toRat : decimal → rat` are
    /// well-typed.
    #[test]
    fn builder_and_injection_types() {
        let (m, k) = (mk_int(15i128), mk_nat(1u32));
        assert_eq!(mk_dec(&m, &k).type_of().unwrap(), dec_ty());
        assert_eq!(
            to_rat().type_of().unwrap(),
            Type::fun(dec_ty(), rat::rat_ty())
        );
    }

    /// The injection lemma is **genuinely proved** — hypothesis-free — and
    /// concludes the expected `m / 10^k` equation.
    #[test]
    fn to_rat_lemma_is_genuine() {
        let (m, k) = (Term::free("m", Type::int()), Term::free("k", Type::nat()));
        let thm = to_rat_at(&m, &k).expect("to_rat_at");
        assert!(
            thm.hyps().is_empty(),
            "the decimal→rat injection lemma is proved, not postulated"
        );
        let (lhs, rhs) = thm.concl().as_eq().expect("an equation");
        assert_eq!(lhs, &Term::app(to_rat(), mk_dec(&m, &k)));
        // RHS is the canonical `of_int m / of_int (natToInt (10 ^ k))`.
        let expected = to_rat_body(m.clone(), k.clone());
        assert_eq!(rhs, &expected);
    }

    /// The ∀-closed cached form specialises back to [`to_rat_at`].
    #[test]
    fn cached_form_specialises() {
        let (m, k) = (mk_int(15i128), mk_nat(2u32));
        let inst = to_rat_mk_dec()
            .all_elim(m.clone())
            .and_then(|t| t.all_elim(k.clone()))
            .expect("specialise to_rat_mk_dec");
        let direct = to_rat_at(&m, &k).expect("to_rat_at");
        assert_eq!(inst.concl(), direct.concl());
        assert!(inst.hyps().is_empty());
    }

    /// `10 ^ k` computes on a literal exponent via the kernel `reduce`
    /// machinery — so `toRat (mkDec 15 1)` fully evaluates its denominator to
    /// `of_int 10`. This is the concrete `1.5 = 15/10` witness.
    #[test]
    fn denominator_computes_on_a_literal() {
        // 10 ^ 1 = 10 (nat), reduced by the kernel.
        let red = pow10(mk_nat(1u32)).reduce().expect("reduce 10^1");
        let (_, rhs) = red.concl().as_eq().expect("an equation");
        assert_eq!(rhs, &mk_nat(10u32));
    }
}
