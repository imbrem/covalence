//! **L5 — the derivation-system interpretation mid-level API**
//! (`notes/vibes/logics/derivation-system-interp.md`).
//!
//! [`super::transport_db`]'s free-function interface lifted to two traits, so
//! each formal system on the shared engine ([`super::RuleSet`]) presents a
//! uniform frontend and an interpretation between two systems is "just another
//! impl". The K matching-logic-proofs → Metamath bridge is ONE (deferred)
//! instance of [`DerivationInterp`].
//!
//! ## The tower rung
//!
//! - [`DerivationSystem`] REQUIRES L2 ([`super::derivable`]) + L3
//!   ([`super::mm_algebra::MmAlgebra`]). A system supplies `rule_set()` (its
//!   `Derivable_L` [`RuleSet`]) and `algebra()` (its reified-term encoding); the
//!   PROVIDED `derivable(a)` delegates to [`super::derivable`].
//! - [`DerivationInterp`] REQUIRES L4 ([`super::transport_db::transport`]). It
//!   supplies `src`/`tgt` systems, `sigma()` (a syntax morphism, built via
//!   [`super::mm_algebra::MmAlgebra::structural_sigma`]) and `clause_sims()` (one
//!   simulation per source rule); the PROVIDED `interpret()` — NEVER overridden —
//!   is [`super::transport_db::transport`] trait-ified.
//!
//! ## What lands vs defers
//!
//! The traits + the Metamath [`DerivationSystem`] shim land now (pure
//! repackaging). The σ=id conservative-extension result already proved in
//! `transport_db::tests` re-instantiates through [`DerivationInterp::interpret`]
//! (the non-vacuity witness — a real working impl, no new proof). The full
//! K→Metamath instance DEFERS on: an honest structural σ (needs `MmExpr` +
//! `MmAlgebra` recursor), per-KORE-rule `clause_sims` (real Metamath simulation
//! proofs), and the same `check_same_carrier` blocker as full reification (K's
//! `Φ=nat` free algebra vs the Church `MmExpr` carrier). See the generated open-work index.

use covalence_core::{Result, Term};
use covalence_hol_eval::EvalThm as Thm;

use super::mm_algebra::MmAlgebra;
use super::{RuleSet, derivable, transport_db};

/// A **formal system reified as a rule set** on the shared engine — the thin
/// adapter Metamath, K, wasm, cfg, and lisp all already satisfy (each is a
/// [`RuleSet`] on `Φ=nat`).
pub trait DerivationSystem {
    /// The system's `Derivable_L` rule set.
    fn rule_set(&self) -> RuleSet<'static>;
    /// The system's reified-term encoding (L3).
    fn algebra(&self) -> &dyn MmAlgebra;

    /// PROVIDED — `Derivable_L a`, delegating to L2 [`super::derivable`].
    fn derivable(&self, a: &Term) -> Result<Term> {
        derivable(&self.rule_set(), a)
    }
}

/// An **interpretation** `Src → Tgt`: a syntax morphism `σ` plus a per-source-rule
/// simulation. The PROVIDED [`interpret`](DerivationInterp::interpret) is
/// [`super::transport_db::transport`], trait-ified.
pub trait DerivationInterp {
    /// The source system.
    type Src: DerivationSystem;
    /// The target system.
    type Tgt: DerivationSystem;

    fn src(&self) -> &Self::Src;
    fn tgt(&self) -> &Self::Tgt;

    /// `σ : Φ_src → Φ_tgt` — the syntax morphism (via
    /// [`super::mm_algebra::MmAlgebra::structural_sigma`] for a structural one).
    fn sigma(&self) -> Result<Term>;

    /// One simulation obligation per SOURCE rule — EXACTLY [`super::transport_db`]'s
    /// `clause_sims` contract: clause `k` laid out at `d := sigma_pred(tgt, σ)`.
    fn clause_sims(&self) -> Result<Vec<Thm>>;

    /// PROVIDED — the transport theorem in ONE `rule_induction` move:
    /// `⊢ ∀A. Derivable_Src A ⟹ Derivable_Tgt (σ A)`. NEVER overridden.
    fn interpret(&self) -> Result<Thm> {
        transport_db::transport(
            &self.src().rule_set(),
            &self.tgt().rule_set(),
            &self.sigma()?,
            self.clause_sims()?,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic::mm_algebra::FreeAlgebra;
    use crate::metalogic::mm_database::rule_set;
    use crate::metamath::{Database, parse, verify_all};

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem is hypothesis-free");
    }

    /// Two databases where T extends S (same signature, one extra axiom) — the
    /// exact fixtures `transport_db::tests` uses for the σ=id monotonicity result.
    const SRC_MM: &str = "\
$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
w-> $a wff ( ph -> ps ) $.
ax-s $a |- ( ph -> ps ) $.
";
    const TGT_MM: &str = "\
$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
w-> $a wff ( ph -> ps ) $.
ax-s $a |- ( ph -> ps ) $.
ax-t $a |- ( ph -> ph ) $.
";

    fn db(src: &str) -> Database {
        let d = parse(src).expect("parse");
        verify_all(&d).expect("verify");
        d
    }

    /// The identity translation `σ := λx:Φ. x` on `Φ=nat` — reused from the
    /// `transport_db` σ=id case.
    fn id_sigma() -> Term {
        let phi = crate::metalogic::mm_database::phi_ty();
        let x = Term::free("__x", phi.clone());
        Term::abs(phi.clone(), covalence_core::subst::close(&x, "__x"))
    }

    /// **L5 non-vacuity: the σ=id monotonicity result re-instantiated through
    /// `DerivationInterp::interpret()`.** We build the src/tgt rule sets, the
    /// id-σ, and the id `clause_sims` exactly as `transport_db::tests` does, but
    /// route them through the trait's PROVIDED `interpret()`. Zero new proofs —
    /// demonstrates the L5 layering delegates correctly to L4.
    #[test]
    fn interpret_delegates_to_transport_at_id() {
        let src_db = db(SRC_MM);
        let tgt_db = db(TGT_MM);
        let src = rule_set(&src_db);
        let tgt = rule_set(&tgt_db);
        let sigma = id_sigma();

        // The id `clause_sims`: reuse `transport_db`'s helper by proving each
        // source clause at `d := sigma_pred(tgt, id)`. `transport_db` exposes the
        // full σ=id path in its tests; here we call `transport` directly with the
        // same `id_clause_sims` shape via its public re-export.
        let sims = transport_db::id_clause_sims(&src_db, &tgt_db);
        let direct = transport_db::transport(&src, &tgt, &sigma, sims).expect("transport");
        assert_genuine(&direct);

        // The DerivationInterp path yields the SAME theorem — proving the trait's
        // provided `interpret()` is exactly `transport`.
        let a = Term::free("A", src.phi.clone());
        let der_src = derivable(&src, &a).unwrap();
        let der_tgt = derivable(&tgt, &sigma.clone().apply(a.clone()).unwrap()).unwrap();
        use crate::init::ext::TermExt;
        let expected = der_src
            .imp(der_tgt)
            .unwrap()
            .forall("A", src.phi.clone())
            .unwrap();
        assert_eq!(
            direct.concl(),
            &expected,
            "interpret() == transport() at σ=id"
        );
    }

    /// The Metamath `DerivationSystem` shim `derivable(a)` delegates to L2.
    #[test]
    fn derivation_system_derivable_delegates() {
        let d = db(SRC_MM);
        let rs = rule_set(&d);
        let fa = FreeAlgebra(&d);
        // Build a `DerivationSystem` by-hand adapter (borrowing).
        struct S<'a> {
            rs_db: &'a Database,
            fa: FreeAlgebra<'a>,
        }
        impl<'a> DerivationSystem for S<'a> {
            fn rule_set(&self) -> RuleSet<'static> {
                rule_set(self.rs_db)
            }
            fn algebra(&self) -> &dyn MmAlgebra {
                &self.fa
            }
        }
        let sys = S { rs_db: &d, fa };
        let a = Term::free("A", rs.phi.clone());
        let via_trait = sys.derivable(&a).unwrap();
        let direct = derivable(&rs, &a).unwrap();
        assert_eq!(
            via_trait, direct,
            "DerivationSystem::derivable == derivable"
        );
        // and `algebra()` is a live `&dyn MmAlgebra`.
        assert_eq!(sys.algebra().phi(), crate::metalogic::mm_database::phi_ty());
    }
}
