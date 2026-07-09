//! EG3a: the `zero` ↔ `Nat(0)`-literal bridge (`ZeroLitCert`) and the
//! derived `zero`-form freeness fact — see
//! `notes/vibes/literal-endgame-design.md` § 6 (EG3) and
//! `covalence_hol_eval::zero`.

use std::any::TypeId;

use covalence_core::hol;
use covalence_core::{Term, Type};
use covalence_hol_eval::{lit, rules, zero_eq_lit, zero_ne_succ_zero};

/// The bridge equation is genuine: `⊢ zero = ⌜0⌝` with NO hypotheses —
/// lhs the primitive `TermKind::Zero` singleton, rhs the transitional
/// `Nat(0)` literal, and the two sides DISTINCT as `Term`s (the bridge is
/// an object-level theorem, not a structural identity).
#[test]
fn bridge_equation_genuine() {
    let thm = zero_eq_lit().expect("EG3a bridge mints");
    assert_eq!(thm.hyps().iter().count(), 0, "no hypotheses");
    let (lhs, rhs) = thm.concl().as_eq().expect("an equation");
    assert_eq!(lhs, &Term::zero());
    assert_eq!(rhs, &lit::mk_nat(0u32));
    assert_ne!(lhs, rhs, "two distinct terms, provably equal");
    // Both sides type at `nat` (the sequent floor already enforced bool
    // at the equation; this pins the element sort).
    assert_eq!(lhs.type_of().unwrap(), Type::nat());
    assert_eq!(rhs.type_of().unwrap(), Type::nat());
}

/// A `zero`-form nat fact derived THROUGH the bridge (zero TCB beyond the
/// one admitted bridge rule): `⊢ ¬(zero = succ n)` for free and closed `n`.
#[test]
fn zero_form_freeness_derives() {
    // Free `n : nat`.
    let n = Term::free("n", Type::nat());
    let thm = zero_ne_succ_zero(&n).expect("derives for free n");
    assert_eq!(thm.hyps().iter().count(), 0);
    let want = hol::hol_not(hol::hol_eq(
        Term::zero(),
        Term::app(Term::succ(), n.clone()),
    ));
    assert_eq!(thm.concl(), &want);

    // Closed instance: `⊢ ¬(zero = succ zero)`.
    let thm = zero_ne_succ_zero(&Term::zero()).expect("derives for zero");
    let want = hol::hol_not(hol::hol_eq(
        Term::zero(),
        Term::app(Term::succ(), Term::zero()),
    ));
    assert_eq!(thm.concl(), &want);
}

/// The bridge is eval-tier ONLY: `CoreLang` does not admit `ZeroLitCert`
/// (its manifest is unchanged), and applying it at the pure-HOL tier is
/// refused by the mint gate.
#[test]
fn core_lang_does_not_admit_bridge() {
    assert!(!covalence_core::seam::core_admits(TypeId::of::<
        rules::ZeroLitCert,
    >()));
    assert!(
        covalence_pure::apply(covalence_core::seam::CoreLang, rules::ZeroLitCert, ()).is_err(),
        "pure-HOL tier refuses the transitional bridge mint"
    );
}
