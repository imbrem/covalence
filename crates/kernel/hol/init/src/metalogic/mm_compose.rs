//! **Composing Metamath-style derivability theorems from outside Metamath.**
//!
//! [`super::database`] reifies a Metamath database as a HOL value `db :
//! Database` and gives `Derivable_DB db A := ∀d. Closed_DB db d ⟹ d A`, a
//! genuine HOL predicate, together with two composition theorems:
//! [`derive_axiom_from_membership`] (an axiom of `db` is derivable) and
//! [`derivable_db_mp`] (`Derivable_DB db` is modus-ponens-closed). This module
//! packages them into a small **session API** so a user can *assemble* new
//! derivability theorems by applying the database's rules in the HOL kernel —
//! without any Metamath proof of the composite existing.
//!
//! Every theorem the session returns is a genuine, kernel-checked
//! `⊢ Derivable_DB db ⌜S⌝`; nothing here adds an axiom or bypasses a check
//! (the constructions are exactly those proven sound in [`super::database`]).
//! The point of interest is the **composite**: from `⊢ Derivable_DB db ⌜A⌝` and
//! `⊢ Derivable_DB db ⌜A ⟹ B⌝` the session mints `⊢ Derivable_DB db ⌜B⌝` even
//! when `B` is *not* an axiom nor a stored theorem of `db` — the Metamath proof
//! of `B` is never written down, yet its existence is certified in HOL.
//!
//! ## Scope (and the bridge to real `.mm` import)
//!
//! Formulas live in the reified **propositional** carrier `Φ⟨bool⟩` of
//! [`crate::init::prop`] — [`DbSession::var`] / [`DbSession::imp`] build them —
//! so this is Metamath *propositional-calculus* derivability, the same
//! `Derivable_DB` notion the monotonicity and interpretation theorems
//! ([`super::database`], [`super::relations`]) are stated over. The `.mm`
//! **importer** ([`super::mm_database::replay_db`]) produces the *other*
//! derivability encoding (carrier `Φ = nat`, `mm$concat` leaves, rule set from
//! the database's `|-` assertions); composing *those* results the same way
//! needs a modus-ponens theorem at the generic [`super::RuleSet`] level (the
//! `derivable_db_mp` construction is database-value-specific). Wiring the two
//! encodings together is tracked in the generated open-work index.

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::mk_nat;

use super::database::{derivable_db, derive_axiom_from_membership, enc_imp};
use super::relations::derivable_db_mp;
use crate::init::ext::TermExt;
use crate::init::prop::p_var_at;

/// A composition session over a fixed reified Metamath database. Holds the HOL
/// database value `db : Database` (a finite axiom set `λf. f = a₀ ∨ … ∨ f =
/// aₙ₋₁`) and lets you build `⊢ Derivable_DB db ⌜S⌝` theorems by applying the
/// database's rules — see the [module docs](self).
#[derive(Debug, Clone)]
pub struct DbSession {
    db: Term,
    axioms: Vec<Term>,
}

impl DbSession {
    /// `Φ⟨bool⟩` — the reified propositional-formula carrier.
    fn phi() -> Type {
        super::database::phi()
    }

    /// The encoded propositional variable `var k : Φ⟨bool⟩` — a formula atom.
    pub fn var(k: u32) -> Term {
        p_var_at(
            &Type::bool(),
            mk_nat(covalence_types::Nat::from_inner(k.into())),
        )
    }

    /// The encoded implication `⌜a ⟹ b⌝ : Φ⟨bool⟩`.
    pub fn imp(a: &Term, b: &Term) -> Term {
        enc_imp(a, b)
    }

    /// Build a session for the database whose axioms are exactly `axioms`
    /// (encoded formulas; use [`var`](Self::var) / [`imp`](Self::imp)). The
    /// database value is `λf. f = a₀ ∨ … ∨ f = aₙ₋₁`. Requires at least one
    /// axiom.
    pub fn new(axioms: Vec<Term>) -> Result<Self> {
        if axioms.is_empty() {
            return Err(covalence_core::Error::ConnectiveRule(
                "DbSession::new: need at least one axiom".into(),
            ));
        }
        let f = Term::free("__f", Self::phi());
        let n = axioms.len();
        let mut body = f.clone().equals(axioms[n - 1].clone())?;
        for k in (0..n - 1).rev() {
            body = f.clone().equals(axioms[k].clone())?.or(body)?;
        }
        let db = Term::abs(Self::phi(), covalence_core::subst::close(&body, "__f"));
        Ok(Self { db, axioms })
    }

    /// The database value `db : Database`.
    pub fn database(&self) -> &Term {
        &self.db
    }

    /// The axiom formulas, in order.
    pub fn axioms(&self) -> &[Term] {
        &self.axioms
    }

    /// The statement term `Derivable_DB db ⌜formula⌝`.
    pub fn derivable(&self, formula: &Term) -> Result<Term> {
        derivable_db(&self.db, formula)
    }

    /// `⊢ Derivable_DB db ⌜formula⌝` for an **axiom** `formula` of this database
    /// (must be `==` one of [`axioms`](Self::axioms)). Proves the membership
    /// `⊢ db ⌜formula⌝` and lifts it through [`derive_axiom_from_membership`].
    pub fn axiom(&self, formula: &Term) -> Result<Thm> {
        let index = self
            .axioms
            .iter()
            .position(|a| a == formula)
            .ok_or_else(|| {
                covalence_core::Error::ConnectiveRule(
                    "DbSession::axiom: formula is not an axiom of this database".into(),
                )
            })?;
        let membership = self.prove_membership(index)?;
        derive_axiom_from_membership(membership)
    }

    /// **Modus ponens at the derivability level.** From `der_a : ⊢
    /// Derivable_DB db ⌜A⌝` and `der_ab : ⊢ Derivable_DB db ⌜A ⟹ B⌝`, produce
    /// `⊢ Derivable_DB db ⌜B⌝`. `a`, `b` are the formulas `A`, `B`; the premise
    /// theorems are checked to state exactly the expected derivabilities (a
    /// mismatch — e.g. `der_ab` not being about `⌜A ⟹ B⌝` — is a clear error,
    /// not a silently wrong result). Instantiates [`derivable_db_mp`] and
    /// discharges the two premises. `B` need not be an axiom or stored theorem
    /// of the database.
    pub fn mp(&self, a: &Term, b: &Term, der_a: &Thm, der_ab: &Thm) -> Result<Thm> {
        let want_a = self.derivable(a)?;
        if der_a.concl() != &want_a {
            return Err(covalence_core::Error::ConnectiveRule(format!(
                "DbSession::mp: first premise is not `Derivable_DB db A`; got {}",
                der_a.concl()
            )));
        }
        let imp_ab = Self::imp(a, b);
        let want_ab = self.derivable(&imp_ab)?;
        if der_ab.concl() != &want_ab {
            return Err(covalence_core::Error::ConnectiveRule(format!(
                "DbSession::mp: second premise is not `Derivable_DB db (A ⟹ B)`; got {}",
                der_ab.concl()
            )));
        }
        // derivable_db_mp: ⊢ Der db A ⟹ Der db ⌜A⟹B⌝ ⟹ Der db B (free db, A, B).
        let mp = derivable_db_mp()?
            .inst("db", self.db.clone())?
            .inst("A", a.clone())?
            .inst("B", b.clone())?;
        mp.imp_elim(der_a.clone())?.imp_elim(der_ab.clone())
    }

    // --- internal: membership proof ------------------------------------------

    /// `⊢ db ⌜aₖ⌝` for the `index`-th axiom, by β-reducing `db aₖ` to its
    /// disjunction and proving the `index`-th disjunct (reflexivity), injecting
    /// it into the right-nested `∨` structure.
    fn prove_membership(&self, index: usize) -> Result<Thm> {
        let ax_i = &self.axioms[index];
        let db_ax = self.db.clone().apply(ax_i.clone())?; // db aᵢ
        let beta = Thm::beta_conv(db_ax)?; // ⊢ db aᵢ = mem
        let n = self.axioms.len();

        // Proof of the index-th disjunct `aᵢ = aᵢ`, then fold outward.
        let mut proof = Thm::refl(ax_i.clone())?; // ⊢ aᵢ = aᵢ
        if index + 1 < n {
            proof = proof.or_intro_l(self.tail_term(index + 1, ax_i)?)?;
        }
        for k in (0..index).rev() {
            let left = ax_i.clone().equals(self.axioms[k].clone())?; // term aᵢ = aₖ
            proof = proof.or_intro_r(left)?;
        }
        beta.sym()?.eq_mp(proof) // ⊢ db aᵢ
    }

    /// The right-nested disjunction `(aᵢ = aⱼ) ∨ … ∨ (aᵢ = aₙ₋₁)` — the tail of
    /// the β-reduced membership prop from position `j` (with `f := aᵢ`).
    fn tail_term(&self, j: usize, ax_i: &Term) -> Result<Term> {
        let n = self.axioms.len();
        let mut t = ax_i.clone().equals(self.axioms[n - 1].clone())?;
        for k in (j..n - 1).rev() {
            t = ax_i.clone().equals(self.axioms[k].clone())?.or(t)?;
        }
        Ok(t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem should be hypothesis-free");
    }

    /// The database `{ p0, p0 ⟹ p1 }`: derive `p1` by modus ponens even though
    /// `p1` is not an axiom nor a stored theorem — the composite existence
    /// certified in HOL, no Metamath proof of `p1` written down.
    #[test]
    fn mp_derives_a_non_axiom() {
        let p0 = DbSession::var(0);
        let p1 = DbSession::var(1);
        let imp01 = DbSession::imp(&p0, &p1);
        let sess = DbSession::new(vec![p0.clone(), imp01.clone()]).unwrap();

        let der_p0 = sess.axiom(&p0).unwrap();
        assert_genuine(&der_p0);
        assert_eq!(der_p0.concl(), &sess.derivable(&p0).unwrap());

        let der_imp = sess.axiom(&imp01).unwrap();
        assert_genuine(&der_imp);

        // p1 is NOT an axiom (asking for it as an axiom fails)…
        assert!(sess.axiom(&p1).is_err());
        // …but it IS derivable, by MP.
        let der_p1 = sess.mp(&p0, &p1, &der_p0, &der_imp).unwrap();
        assert_genuine(&der_p1);
        assert_eq!(der_p1.concl(), &sess.derivable(&p1).unwrap());
    }

    /// A two-step composition: `{p0, p0⟹p1, p1⟹p2}` derives `p2`.
    #[test]
    fn mp_chains() {
        let p0 = DbSession::var(0);
        let p1 = DbSession::var(1);
        let p2 = DbSession::var(2);
        let imp01 = DbSession::imp(&p0, &p1);
        let imp12 = DbSession::imp(&p1, &p2);
        let sess = DbSession::new(vec![p0.clone(), imp01.clone(), imp12.clone()]).unwrap();

        let d0 = sess.axiom(&p0).unwrap();
        let d01 = sess.axiom(&imp01).unwrap();
        let d12 = sess.axiom(&imp12).unwrap();
        let d1 = sess.mp(&p0, &p1, &d0, &d01).unwrap();
        let d2 = sess.mp(&p1, &p2, &d1, &d12).unwrap();
        assert_genuine(&d2);
        assert_eq!(d2.concl(), &sess.derivable(&p2).unwrap());
    }

    /// A mismatched premise is a clear error, not a wrong theorem.
    #[test]
    fn mp_rejects_mismatched_premise() {
        let p0 = DbSession::var(0);
        let p1 = DbSession::var(1);
        let imp01 = DbSession::imp(&p0, &p1);
        let sess = DbSession::new(vec![p0.clone(), imp01.clone()]).unwrap();
        let der_p0 = sess.axiom(&p0).unwrap();
        // der_p0 proves `Derivable_DB db p0`, not `Derivable_DB db (p0 ⟹ p1)`.
        assert!(sess.mp(&p0, &p1, &der_p0, &der_p0).is_err());
    }

    /// A single-axiom database still proves its axiom (n = 1 membership path).
    #[test]
    fn singleton_axiom() {
        let p0 = DbSession::var(0);
        let sess = DbSession::new(vec![p0.clone()]).unwrap();
        let der = sess.axiom(&p0).unwrap();
        assert_genuine(&der);
        assert_eq!(der.concl(), &sess.derivable(&p0).unwrap());
    }
}
