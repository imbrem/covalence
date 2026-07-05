//! The toHOL first-slice acceptance tests (purge stage S4).
//!
//! Proves the design end-to-end: a computation-backed `IsThm` certificate,
//! reified through the admitted toHOL rules and transported with the base
//! `eq_mp`, lands as a `core::Thm` **bit-for-bit equal** to the legacy
//! literal-reduction fact — plus the seam's gating negative tests.

use covalence_core::proofs::nat_add_thm;
use covalence_core::seam::{CoreLang, HolApp, NatAddCert};
use covalence_core::{Term, Thm, defs};
use covalence_pure::{Error as PureError, Thm as PThm, apply, canon};
use covalence_pure_eval::{Builtins, NatAdd};
use covalence_types::Nat;

fn n(v: u32) -> Nat {
    Nat::from(v)
}

/// THE slice test: the toHOL-minted fact is indistinguishable from the
/// legacy literal-reduction fact — same (empty) hyps, same conclusion term.
#[test]
fn tohol_nat_add_matches_legacy_reduction() {
    let lit_app = Term::app(
        Term::app(defs::nat_add(), Term::nat_lit(n(2))),
        Term::nat_lit(n(3)),
    );
    let legacy = Thm::reduce_prim(lit_app).expect("legacy reduction of 2 + 3");

    let via_tohol = nat_add_thm(n(2), n(3)).expect("toHOL slice derivation of 2 + 3");

    assert!(via_tohol.hyps().is_empty(), "no hypotheses");
    assert_eq!(via_tohol.concl(), legacy.concl(), "identical conclusions");
}

/// A couple more values, including 0 edge cases (the driver must reify the
/// same numeral the certificate denoted).
#[test]
fn tohol_nat_add_more_values() {
    for (a, b) in [(0u32, 0u32), (0, 7), (255, 1)] {
        let thm = nat_add_thm(n(a), n(b)).expect("toHOL derivation");
        let lit_app = Term::app(
            Term::app(defs::nat_add(), Term::nat_lit(n(a))),
            Term::nat_lit(n(b)),
        );
        let legacy = Thm::reduce_prim(lit_app).expect("legacy reduction");
        assert_eq!(thm.concl(), legacy.concl());
    }
}

/// NEGATIVE: the certificate rule is inert in a language that does not admit
/// it — `apply` gates on the rule's own `TypeId` before `decide` ever runs.
#[test]
fn nat_add_cert_not_admitted_elsewhere() {
    assert!(matches!(
        apply((), NatAddCert, (n(2), n(3))),
        Err(PureError::NotAdmitted(_))
    ));
    assert!(matches!(
        apply(Builtins, NatAddCert, (n(2), n(3))),
        Err(PureError::NotAdmitted(_))
    ));
}

/// NEGATIVE: `HolApp` evaluation is admitted in `CoreLang` only.
#[test]
fn hol_app_canon_gated_on_core_lang() {
    let f = defs::nat_add();
    let x = defs::nat_succ();
    assert!(canon(HolApp, (f.clone(), x.clone()), CoreLang).is_ok());
    assert!(matches!(
        canon(HolApp, (f, x), ()),
        Err(PureError::NotAdmitted(_))
    ));
}

/// The seam's other half: a canon-minted `Thm<Builtins, _>` fact lifts into
/// `CoreLang` (`CoreLang.extends(Builtins)`), but not into `()`.
#[test]
fn builtins_facts_lift_into_core_lang() {
    let fact = canon(NatAdd, (n(2), n(2)), Builtins).expect("Builtins admits NatAdd");
    let lifted: PThm<CoreLang, _> = fact
        .clone()
        .lift(CoreLang)
        .expect("CoreLang extends Builtins");
    let _ = lifted;
    assert!(matches!(fact.lift(()), Err(PureError::NotExtended(_))));
}
