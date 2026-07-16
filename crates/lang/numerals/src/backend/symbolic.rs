//! The [`Symbolic`] backend: build kernel `Term`s and prove relationships
//! *structurally*, with no new TCB.
//!
//! ## `prove_eq` — the headline
//!
//! Two surface numerals denote equal values iff they reduce to the same kernel
//! normal form. `prove_eq(a, b)` therefore:
//!
//! 1. reduces `a` to its normal form `nfa` with `⊢ a = nfa`;
//! 2. reduces `b` to `nfb` with `⊢ b = nfb`;
//! 3. checks `nfa` and `nfb` are the *same term* — if so `⊢ nfa = nfb` is
//!    reflexivity — and chains `⊢ a = nfa`, `⊢ nfa = nfb`, `(⊢ b = nfb).sym()`
//!    into `⊢ a = b`.
//!
//! For literals the reductions are the identity (`reduce` finds no redex), so
//! for `Symbolic.prove_eq(0xABC, 2748)` — where both surface forms already
//! folded, in [`covalence_types`], to the **same** `Nat` `2748` and hence to the
//! same literal `Term` — the chain collapses to a single `refl`. Every step is
//! an admitted kernel mint (`refl`/`trans`/`sym`/`reduce`); nothing here can
//! forge a theorem.

use covalence_hol_eval::defs::nat_lt;
use covalence_hol_eval::{EvalThm, mk_int, mk_nat, mk_u32, prove_true, reduce};
use covalence_init::Term;
use covalence_init::init::decimal::{mk_dec, to_rat_at};
use covalence_init::init::rat::{of_int, rat_div};
use covalence_types::{Decimal, Int, Nat, Rat};

use crate::lit::{FloatCert32, NumeralBackend};

/// Which rung of the ladder a [`NumeralTerm`] was built at — selects the
/// relation used to prove `<` and `toRat`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rung {
    Nat,
    Int,
    Decimal,
    Rat,
    F32Bits,
}

/// A built numeral: a kernel `Term` tagged with the rung it came from.
#[derive(Clone, Debug)]
pub struct NumeralTerm {
    /// The kernel term.
    pub term: Term,
    /// The ladder rung.
    pub rung: Rung,
}

impl NumeralTerm {
    fn new(term: Term, rung: Rung) -> Self {
        Self { term, rung }
    }
}

/// The structural kernel backend. See the module docs.
#[derive(Clone, Copy, Debug, Default)]
pub struct Symbolic;

impl Symbolic {
    /// The canonical rational term a built decimal denotes: the RHS of the
    /// proved injection lemma `⊢ toRat (mkDec m k) = of_int m / of_int
    /// (natToInt (10^k))`. Handy for callers that want the `r` to pass to
    /// [`NumeralBackend::prove_to_rat`]. Returns `None` if the lemma cannot be
    /// built (never, for a well-formed decimal).
    pub fn canonical_rat_of_decimal(&self, d: &Decimal) -> Option<NumeralTerm> {
        let (m, k) = (mk_int(d.mantissa().clone()), mk_nat(d.scale()));
        let lemma = to_rat_at(&m, &k).ok()?;
        let (_, rhs) = lemma.concl().as_eq()?;
        Some(NumeralTerm::new(rhs.clone(), Rung::Rat))
    }
}

/// `mkDec (mk_int m) (mk_nat k)` — a built finite decimal term for `m / 10^k`.
fn decimal_term(d: &Decimal) -> Term {
    mk_dec(&mk_int(d.mantissa().clone()), &mk_nat(d.scale()))
}

/// `ratDiv (of_int (mk_int n)) (of_int (mk_int d))` — a built rational term.
fn rat_term(r: &Rat) -> Term {
    let num = Term::app(of_int(), mk_int(r.numer()));
    let den = Term::app(of_int(), mk_int(r.denom()));
    Term::app(Term::app(rat_div(), num), den)
}

/// Reduce `t` to a normal form, returning `(nf, ⊢ t = nf)`. A single kernel
/// `reduce` step suffices for the literal leaves this backend produces (a bare
/// literal has no redex, so `nf = t` via `refl`).
fn normal_form(t: &Term) -> Option<(Term, EvalThm)> {
    match reduce(t) {
        Some(thm) => {
            let (_, rhs) = thm.concl().as_eq()?;
            Some((rhs.clone(), thm))
        }
        None => Some((t.clone(), EvalThm::refl(t.clone()).ok()?)),
    }
}

impl NumeralBackend for Symbolic {
    type Repr = NumeralTerm;
    type Thm = EvalThm;

    fn nat(&self, value: &Nat) -> NumeralTerm {
        NumeralTerm::new(mk_nat(value.clone()), Rung::Nat)
    }
    fn int(&self, value: &Int) -> NumeralTerm {
        NumeralTerm::new(mk_int(value.clone()), Rung::Int)
    }
    fn decimal(&self, value: &Decimal) -> NumeralTerm {
        NumeralTerm::new(decimal_term(value), Rung::Decimal)
    }
    fn rat(&self, value: &Rat) -> NumeralTerm {
        NumeralTerm::new(rat_term(value), Rung::Rat)
    }
    fn f32_bits(&self, bits: u32) -> NumeralTerm {
        // The raw single-precision bit pattern as a `u32` literal leaf.
        NumeralTerm::new(mk_u32(bits), Rung::F32Bits)
    }

    fn prove_eq(&self, a: &NumeralTerm, b: &NumeralTerm) -> Option<EvalThm> {
        // Reduce both to a common normal form and chain the equations.
        let (nfa, a_eq) = normal_form(&a.term)?; // ⊢ a = nfa
        let (nfb, b_eq) = normal_form(&b.term)?; // ⊢ b = nfb
        if nfa != nfb {
            return None; // distinct normal forms ⇒ not (provably) equal here
        }
        // ⊢ a = nfa , ⊢ nfa = nfb (=refl) , ⊢ nfb = b
        let a_to_nfb = a_eq; // nfa == nfb, so this is already ⊢ a = nfb
        let thm = a_to_nfb.trans(b_eq.sym().ok()?).ok()?; // ⊢ a = b
        Some(thm)
    }

    fn prove_lt(&self, a: &NumeralTerm, b: &NumeralTerm) -> Option<EvalThm> {
        // Decide `<` on the natural rung by evaluating `nat.lt a b` to `T`.
        if a.rung == Rung::Nat && b.rung == Rung::Nat {
            let lt = Term::app(Term::app(nat_lt(), a.term.clone()), b.term.clone());
            return prove_true(&lt).ok();
        }
        None
    }

    fn prove_to_rat(&self, a: &NumeralTerm, r: &NumeralTerm) -> Option<EvalThm> {
        // For a built decimal `mkDec m k`, the proved injection lemma gives
        // `⊢ toRat (mkDec m k) = of_int m / of_int (natToInt (10^k))`. We accept
        // `r` when it matches that canonical RHS (structurally, after reducing).
        if a.rung != Rung::Decimal {
            return None;
        }
        // Recover m, k from the built term `pair m k` = `((pair) m) k`.
        let (m, k) = split_mk_dec(&a.term)?;
        let lemma = to_rat_at(&m, &k).ok()?; // ⊢ toRat (mkDec m k) = <rhs>
        let (_, rhs) = lemma.concl().as_eq()?;
        // Only vouch for `r` if it is (structurally) that canonical rational.
        (rhs == &r.term).then_some(lemma)
    }

    fn ground_f32(&self, _value: &Decimal) -> FloatCert32<EvalThm> {
        // The rounding-enclosure certificate is not proved yet — see
        // `crates/lang/numerals/SKELETONS.md`. We do not fabricate one.
        FloatCert32::Unproven
    }
}

/// Split a built `mkDec m k` term (`((pair) m) k`) back into `(m, k)`.
fn split_mk_dec(t: &Term) -> Option<(Term, Term)> {
    // t = app(app(pair, m), k)
    let (inner, k) = t.as_app()?;
    let (_pair, m) = inner.as_app()?;
    Some((m.clone(), k.clone()))
}
