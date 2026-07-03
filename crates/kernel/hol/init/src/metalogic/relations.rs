//! **Interpretation** between databases under a formula translation `σ`, and
//! the **transport** theorem — the `S`-rewrite of
//! `notes/vibes/theories-models-and-logics.md` §5.6 realised as a relation on the
//! [`Database`](super::database::database_ty) type.
//!
//! A translation is a HOL function `σ : Φ → Φ` on encoded formulas. Two
//! databases stand in the **interpretation** relation `A ⟹_σ B` when `σ` maps
//! every `A`-axiom to a `B`-derivable formula:
//!
//! ```text
//!   Interp A B σ  :=  ∀ax. A ax ⟹ Derivable_DB B (σ ax)
//! ```
//!
//! The **transport** theorem says derivability follows the translation:
//!
//! ```text
//!   σ_hom : (∀X Y. σ ⌜X ⟹ Y⌝ = ⌜σ X ⟹ σ Y⌝)        -- σ is a ⟹-homomorphism
//!   ⊢ σ_hom ⟹ Interp A B σ ⟹ Derivable_DB A S ⟹ Derivable_DB B (σ S)
//! ```
//!
//! **Proof.** Rule induction on the `A`-derivation: instantiate its
//! impredicative predicate `d := λx. Derivable_DB B (σ x)` and discharge
//! `Closed_DB A (λx. Derivable_DB B (σ x))`:
//!
//! - the **axiom clause** `∀ax. A ax ⟹ Derivable_DB B (σ ax)` is *exactly*
//!   `Interp A B σ`;
//! - the **modus-ponens clause** `∀X Y. Der_B(σ X) ∧ Der_B(σ⌜X⟹Y⌝) ⟹ Der_B(σ Y)`
//!   becomes, after rewriting `σ⌜X⟹Y⌝ = ⌜σX ⟹ σY⌝` (the `σ_hom` hypothesis),
//!   `Der_B(σ X) ∧ Der_B⌜σX ⟹ σY⌝ ⟹ Der_B(σ Y)` — which is `Derivable_DB B`'s
//!   own modus-ponens closure ([`derivable_db_mp`]).
//!
//! ## The `σ_hom` hypothesis and the identity demonstration
//!
//! `σ_hom` (σ commutes with `⟹`) is carried as an explicit hypothesis rather
//! than baked into the encoding, so [`transport`] is fully general over any
//! `⟹`-homomorphic translation. The concrete demonstration ([`tests`]) is the
//! **identity translation** `σ := λx. x`, for which `σ_hom` holds by
//! reflexivity (β); transport then specialises to
//! `Interp A B id ⟹ Derivable_DB A S ⟹ Derivable_DB B S`, and since `A ⊑ B`
//! entails `Interp A B id` (every `A`-axiom is a `B`-axiom, hence `B`-derivable),
//! this exhibits **monotonicity as interpretation under the identity renaming**
//! — the `⊑` of [`super::database`] sitting inside the `⟹_σ` lattice. A
//! non-trivial variable-renaming `σ` (with a genuinely structural `σ_hom`
//! proof) is the next step; see [`SKELETONS.md`](./SKELETONS.md).

use covalence_core::{Result, Term, Thm, Type};

use super::database::{app, closed, d_var, derivable_db, enc_imp, fvar, phi, pred_ty};
use crate::init::ext::{TermExt, ThmExt};

/// `Φ → Φ` — the type of a formula translation `σ`.
fn sigma_ty() -> Type {
    Type::fun(phi(), phi())
}

/// `σ X` — apply the translation `σ : Φ → Φ` to an encoded formula `X`.
fn sigma_at(sigma: &Term, x: &Term) -> Result<Term> {
    sigma.clone().apply(x.clone())
}

// ============================================================================
// `derivable_db_mp` — `Derivable_DB db` is modus-ponens-closed.
//
//   ⊢ Derivable_DB db A ⟹ Derivable_DB db ⌜A ⟹ B⌝ ⟹ Derivable_DB db B
//
// The same impredicative MP construction as `init::prop::derive_mp` /
// `peano::pa::derive_mp`, now reading the database off the value `db`.
// ============================================================================

/// **`Derivable_DB db` is closed under modus ponens.**
///
/// ```text
///   ⊢ Derivable_DB db A ⟹ Derivable_DB db ⌜A ⟹ B⌝ ⟹ Derivable_DB db B
/// ```
///
/// `db : Database`, `A`, `B : Φ` are free. A genuine HOL theorem — the reified
/// MP rule of the impredicative engine, lifted to the database-parameterized
/// derivability.
pub fn derivable_db_mp() -> Result<Thm> {
    let db = Term::free("db", super::database::database_ty());
    let a = fvar("A");
    let b = fvar("B");
    let imp_ab = enc_imp(&a, &b);
    let d = d_var();

    let closed_d = closed(&db, &d)?; // Closed_DB db d
    let assumed = Thm::assume(closed_d.clone())?; // {Closed} ⊢ Closed_DB db d

    // d ⌜A⌝ and d ⌜A⟹B⌝ from the two derivability hypotheses.
    let der_a = Thm::assume(derivable_db(&db, &a)?)?; // {Der A} ⊢ Derivable_DB db A
    let da = der_a.all_elim(d.clone())?.imp_elim(assumed.clone())?; // ⊢ d ⌜A⌝
    let der_ab = Thm::assume(derivable_db(&db, &imp_ab)?)?;
    let dab = der_ab.all_elim(d.clone())?.imp_elim(assumed.clone())?; // ⊢ d ⌜A⟹B⌝

    // The MP conjunct is the FIRST clause of `Closed_DB` (`and_elim_l`).
    let mp_clause = assumed.and_elim_l()?; // ⊢ ∀A B. (d A ∧ d⌜A⟹B⌝) ⟹ d B
    let mp_inst = mp_clause.all_elim(b.clone())?.all_elim(a.clone())?;
    let db_thm = mp_inst.imp_elim(da.and_intro(dab)?)?; // ⊢ d ⌜B⌝

    let der_b = db_thm.imp_intro(&closed_d)?.all_intro("d", pred_ty())?; // {Der A, Der (A⟹B)} ⊢ Derivable_DB db B
    der_b
        .imp_intro(&derivable_db(&db, &imp_ab)?)?
        .imp_intro(&derivable_db(&db, &a)?)
}

// ============================================================================
// `interp` — the interpretation relation `A ⟹_σ B`.
// ============================================================================

/// `Interp A B σ := ∀ax. A ax ⟹ Derivable_DB B (σ ax)` — the **interpretation**
/// relation: `σ` maps every axiom of `A` to a `B`-derivable formula. A HOL
/// `bool` term over the databases `a`, `b` and translation `sigma`.
pub fn interp(a: &Term, b: &Term, sigma: &Term) -> Result<Term> {
    let ax = fvar("ax");
    let sax = sigma_at(sigma, &ax)?;
    app(a, &ax)?
        .imp(derivable_db(b, &sax)?)?
        .forall("ax", phi())
}

/// `σ_hom σ := ∀X Y. σ ⌜X ⟹ Y⌝ = ⌜σ X ⟹ σ Y⌝` — `σ` commutes with the
/// implication constructor (is a `⟹`-homomorphism on encoded formulas). A HOL
/// `bool` term over the translation `sigma`.
pub fn sigma_hom(sigma: &Term) -> Result<Term> {
    let x = fvar("X");
    let y = fvar("Y");
    let lhs = sigma_at(sigma, &enc_imp(&x, &y))?; // σ ⌜X ⟹ Y⌝
    let rhs = enc_imp(&sigma_at(sigma, &x)?, &sigma_at(sigma, &y)?); // ⌜σX ⟹ σY⌝
    lhs.equals(rhs)?.forall("Y", phi())?.forall("X", phi())
}

// ============================================================================
// `transport` — the theorem for the interpretation relation.
//
//   ⊢ σ_hom σ ⟹ Interp A B σ ⟹ Derivable_DB A S ⟹ Derivable_DB B (σ S)
//
// PROOF: instantiate `Derivable_DB A S`'s predicate `d := λx. Der_B (σ x)` and
// discharge `Closed_DB A d`:
//   axiom clause = Interp A B σ                                   [the hypothesis]
//   MP clause: ∀X Y. d X ∧ d⌜X⟹Y⌝ ⟹ d Y, i.e.
//              Der_B(σX) ∧ Der_B(σ⌜X⟹Y⌝) ⟹ Der_B(σY);
//              rewrite σ⌜X⟹Y⌝ = ⌜σX⟹σY⌝ (σ_hom) ⟹ derivable_db_mp.
// ============================================================================

/// **Transport of derivability under interpretation.**
///
/// ```text
///   ⊢ σ_hom σ ⟹ Interp A B σ ⟹ Derivable_DB A S ⟹ Derivable_DB B (σ S)
/// ```
///
/// A genuine HOL theorem (no postulates): a formula derivable in `A` translates
/// to a `B`-derivable formula under any `⟹`-homomorphic interpretation `σ`.
/// `A`, `B : Database`, `σ : Φ → Φ`, `S : Φ` are free.
pub fn transport() -> Result<Thm> {
    // The database vars are named `DbA`/`DbB` to avoid clashing with the
    // *formula* vars `A`/`B : Φ` that `derivable_db_mp` (and `enc_imp`) carry —
    // the kernel rejects reusing one name at two types.
    let a = Term::free("DbA", super::database::database_ty());
    let b = Term::free("DbB", super::database::database_ty());
    let sigma = Term::free("sigma", sigma_ty());
    let s = fvar("S");

    // The instantiation predicate `d := λx. Derivable_DB B (σ x)`.
    let x = fvar("x");
    let d_body = derivable_db(&b, &sigma_at(&sigma, &x)?)?; // Derivable_DB B (σ x)
    let d_pred = Term::abs(phi(), covalence_core::subst::close(&d_body, "x"));

    let hom = sigma_hom(&sigma)?;
    let interp_ab = interp(&a, &b, &sigma)?;
    let der_a_s = derivable_db(&a, &s)?;

    let h_hom = Thm::assume(hom.clone())?; // {hom} ⊢ σ_hom σ
    let h_interp = Thm::assume(interp_ab.clone())?; // {interp} ⊢ Interp A B σ
    let h_der = Thm::assume(der_a_s.clone())?; // {der} ⊢ Derivable_DB A S

    // --- discharge Closed_DB A d, clause by clause ---
    let d = &d_pred;

    // Axiom clause `∀ax. A ax ⟹ d ax`. Since `d ax` β-reduces to
    // `Derivable_DB B (σ ax)`, this is `Interp A B σ` up to β under the binder.
    let axiom_clause = {
        let ax = fvar("ax");
        // h_interp @ ax : A ax ⟹ Derivable_DB B (σ ax)
        let interp_at = h_interp.clone().all_elim(ax.clone())?; // {interp} ⊢ A ax ⟹ Der_B(σ ax)
        // β-fold `Der_B(σ ax)` to `d ax`.
        let d_ax = d.clone().apply(ax.clone())?; // (λx. Der_B(σ x)) ax
        let beta = Thm::beta_conv(d_ax.clone())?; // ⊢ d ax = Der_B(σ ax)
        // rewrite the consequent of `interp_at` back to `d ax`.
        let a_ax = app(&a, &ax)?;
        let assume_a = Thm::assume(a_ax.clone())?; // {A ax} ⊢ A ax
        let der_b_sax = interp_at.imp_elim(assume_a)?; // {interp, A ax} ⊢ Der_B(σ ax)
        let d_ax_thm = beta.sym()?.eq_mp(der_b_sax)?; // {interp, A ax} ⊢ d ax
        d_ax_thm.imp_intro(&a_ax)?.all_intro("ax", phi())? // {interp} ⊢ ∀ax. A ax ⟹ d ax
    };

    // MP clause `∀X Y. d X ∧ d ⌜X⟹Y⌝ ⟹ d Y`.
    let mp_clause = {
        let big_x = fvar("X");
        let big_y = fvar("Y");
        let imp_xy = enc_imp(&big_x, &big_y);

        // Unfold `d X`, `d ⌜X⟹Y⌝`, `d Y` to their β-forms.
        let dx = d.clone().apply(big_x.clone())?;
        let beta_x = Thm::beta_conv(dx.clone())?; // ⊢ d X = Der_B(σ X)
        let dxy = d.clone().apply(imp_xy.clone())?;
        let beta_xy = Thm::beta_conv(dxy.clone())?; // ⊢ d ⌜X⟹Y⌝ = Der_B(σ ⌜X⟹Y⌝)
        let dy = d.clone().apply(big_y.clone())?;
        let beta_y = Thm::beta_conv(dy.clone())?; // ⊢ d Y = Der_B(σ Y)

        // σ_hom @ X Y : σ ⌜X⟹Y⌝ = ⌜σX ⟹ σY⌝
        let hom_xy = h_hom
            .clone()
            .all_elim(big_x.clone())?
            .all_elim(big_y.clone())?; // {hom} ⊢ σ⌜X⟹Y⌝ = ⌜σX⟹σY⌝
        // Der_B(σ⌜X⟹Y⌝) = Der_B⌜σX⟹σY⌝  (congruence under `Derivable_DB B ·`).
        // Build the equality `Der_B(σ⌜X⟹Y⌝) = Der_B⌜σX⟹σY⌝` by rewriting inside.

        // derivable_db_mp @ db:=B, A:=σX, B:=σY :
        //   Der_B(σX) ⟹ Der_B⌜σX⟹σY⌝ ⟹ Der_B(σY)
        let sx = sigma_at(&sigma, &big_x)?;
        let sy = sigma_at(&sigma, &big_y)?;
        let mp_b = derivable_db_mp()?
            .inst("db", b.clone())?
            .inst("A", sx.clone())?
            .inst("B", sy.clone())?; // ⊢ Der_B(σX) ⟹ Der_B⌜σX⟹σY⌝ ⟹ Der_B(σY)

        // Goal at the β/σ_hom-normal level:
        //   (Der_B(σX) ∧ Der_B(σ⌜X⟹Y⌝)) ⟹ Der_B(σY)
        let der_b_sx = derivable_db(&b, &sx)?; // Der_B(σ X)
        let der_b_sxy = derivable_db(&b, &sigma_at(&sigma, &imp_xy)?)?; // Der_B(σ⌜X⟹Y⌝)
        let conj = der_b_sx.clone().and(der_b_sxy.clone())?;
        let assume_conj = Thm::assume(conj.clone())?; // {conj} ⊢ Der_B(σX) ∧ Der_B(σ⌜X⟹Y⌝)
        let h_sx = assume_conj.clone().and_elim_l()?; // {conj} ⊢ Der_B(σ X)
        let h_sxy = assume_conj.and_elim_r()?; // {conj} ⊢ Der_B(σ⌜X⟹Y⌝)
        // rewrite Der_B(σ⌜X⟹Y⌝) → Der_B⌜σX⟹σY⌝ using `hom_xy` (congruence).
        let h_sxy_hom = h_sxy.rewrite(&hom_xy)?; // {conj, hom} ⊢ Der_B⌜σX⟹σY⌝
        let der_b_sy = mp_b.imp_elim(h_sx)?.imp_elim(h_sxy_hom)?; // {conj, hom} ⊢ Der_B(σ Y)
        let mp_den = der_b_sy.imp_intro(&conj)?; // {hom} ⊢ (Der_B(σX) ∧ Der_B(σ⌜X⟹Y⌝)) ⟹ Der_B(σY)

        // β-expand the three `Der_B(σ·)` back to `d ·`.
        mp_den
            .rewrite(&beta_x.clone().sym()?)?
            .rewrite(&beta_xy.clone().sym()?)?
            .rewrite(&beta_y.clone().sym()?)?
            .all_intro("X", phi())?
            .all_intro("Y", phi())?
    };

    // Assemble `Closed_DB A d = MP(d) ∧ axioms(d)`.
    let closed_a_d_thm = mp_clause.and_intro(axiom_clause)?; // {hom, interp} ⊢ Closed_DB A d
    debug_assert_eq!(closed_a_d_thm.concl(), &closed(&a, d)?);

    // Instantiate `Derivable_DB A S` at `d`, discharge `Closed_DB A d`.
    let der_at_d = h_der.all_elim(d.clone())?; // {der} ⊢ Closed_DB A d ⟹ d S
    let d_s = der_at_d.imp_elim(closed_a_d_thm)?; // {hom, interp, der} ⊢ d S
    // β-reduce `d S` to `Derivable_DB B (σ S)`.
    let d_s_app = d.clone().apply(s.clone())?;
    let beta_s = Thm::beta_conv(d_s_app)?; // ⊢ d S = Der_B(σ S)
    let der_b_ss = beta_s.eq_mp(d_s)?; // {hom, interp, der} ⊢ Derivable_DB B (σ S)
    debug_assert_eq!(der_b_ss.concl(), &derivable_db(&b, &sigma_at(&sigma, &s)?)?);

    // Discharge the three hypotheses.
    der_b_ss
        .imp_intro(&der_a_s)?
        .imp_intro(&interp_ab)?
        .imp_intro(&hom)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem is hypothesis-free");
        assert!(thm.has_no_obs(), "theorem is oracle-free");
    }

    fn database_ty() -> Type {
        super::super::database::database_ty()
    }

    /// The identity translation `σ := λx. x` on encoded formulas.
    fn id_sigma() -> Term {
        let x = fvar("__x");
        Term::abs(phi(), covalence_core::subst::close(&x, "__x"))
    }

    #[test]
    fn derivable_db_mp_is_genuine() {
        let thm = derivable_db_mp().unwrap();
        assert_genuine(&thm);
        // Shape: Der db A ⟹ Der db ⌜A⟹B⌝ ⟹ Der db B.
        let db = Term::free("db", database_ty());
        let a = fvar("A");
        let b = fvar("B");
        let expected = derivable_db(&db, &a)
            .unwrap()
            .imp(
                derivable_db(&db, &enc_imp(&a, &b))
                    .unwrap()
                    .imp(derivable_db(&db, &b).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    #[test]
    fn interp_and_sigma_hom_are_well_typed() {
        let a = Term::free("A", database_ty());
        let b = Term::free("B", database_ty());
        let sigma = Term::free("sigma", sigma_ty());
        assert_eq!(
            interp(&a, &b, &sigma).unwrap().type_of().unwrap(),
            Type::bool()
        );
        assert_eq!(sigma_hom(&sigma).unwrap().type_of().unwrap(), Type::bool());
    }

    /// **Transport** is a single genuine HOL theorem of the right shape.
    #[test]
    fn transport_is_genuine() {
        let thm = transport().unwrap();
        assert_genuine(&thm);
        // Shape: σ_hom σ ⟹ Interp DbA DbB σ ⟹ Der_DbA S ⟹ Der_DbB (σ S).
        let a = Term::free("DbA", database_ty());
        let b = Term::free("DbB", database_ty());
        let sigma = Term::free("sigma", sigma_ty());
        let s = fvar("S");
        let expected = sigma_hom(&sigma)
            .unwrap()
            .imp(
                interp(&a, &b, &sigma)
                    .unwrap()
                    .imp(
                        derivable_db(&a, &s)
                            .unwrap()
                            .imp(derivable_db(&b, &sigma_at(&sigma, &s).unwrap()).unwrap())
                            .unwrap(),
                    )
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// **Concrete σ = identity.** Prove `⊢ σ_hom (λx.x)` (reflexivity through β),
    /// then specialise [`transport`] to `σ := id` and discharge it, yielding the
    /// genuine theorem `⊢ Interp A B id ⟹ Derivable_DB A S ⟹ Derivable_DB B (id S)`
    /// — the identity-renaming instance of transport. Since `A ⊑ B` entails
    /// `Interp A B id` (every `A`-axiom is a `B`-axiom, hence `B`-derivable) and
    /// `id S = S`, this exhibits **monotonicity as interpretation under the
    /// identity renaming** — `⊑` sitting inside the `⟹_σ` lattice.
    #[test]
    fn identity_transport_is_the_identity_instance() {
        let id = id_sigma();

        // ⊢ σ_hom (λx.x): both sides of σ⌜X⟹Y⌝ = ⌜σX ⟹ σY⌝ β-reduce to ⌜X⟹Y⌝.
        let hom_thm = prove_by_beta_refl(&sigma_hom(&id).unwrap());
        assert_genuine(&hom_thm);

        // Specialise transport to σ := id and discharge σ_hom: a genuine HOL
        // theorem `⊢ Interp A B id ⟹ Derivable_DB A S ⟹ Derivable_DB B (id S)`
        // over free databases A, B and formula S — the identity-renaming instance
        // of transport (the seed of "monotonicity as interpretation under id").
        let trans_id = transport().unwrap().inst("sigma", id.clone()).unwrap();
        let after_hom = trans_id.imp_elim(hom_thm).unwrap();
        assert_genuine(&after_hom);

        // The conclusion is `Interp A B id ⟹ Der_A S ⟹ Der_B (id S)`.
        let a = Term::free("DbA", database_ty());
        let b = Term::free("DbB", database_ty());
        let s = fvar("S");
        let expected = interp(&a, &b, &id)
            .unwrap()
            .imp(
                derivable_db(&a, &s)
                    .unwrap()
                    .imp(derivable_db(&b, &sigma_at(&id, &s).unwrap()).unwrap())
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(after_hom.concl(), &expected);

        // `id S` is genuinely the identity: it β-reduces to `S`.
        let id_s = id.apply(s.clone()).unwrap();
        let id_beta = Thm::beta_conv(id_s).unwrap();
        assert_eq!(id_beta.concl().as_eq().unwrap().1, &s, "id S = S");
    }

    /// Prove a `∀…. lhs = rhs` goal whose `lhs`/`rhs` β-normalise to the same
    /// term: peel the `∀`s, prove the equation by reflexivity through β, re-`∀`.
    fn prove_by_beta_refl(goal: &Term) -> Thm {
        // Peel the two outer ∀X ∀Y to reach the equation body.
        // `goal = ∀X. ∀Y. (lhs = rhs)`; instantiate at fresh frees, prove, regen.
        let x = fvar("X");
        let y = fvar("Y");
        // Reconstruct the equation `(λx.x)⌜X⟹Y⌝ = ⌜(λx.x)X ⟹ (λx.x)Y⌝`.
        let id = id_sigma();
        let lhs = sigma_at(&id, &enc_imp(&x, &y)).unwrap();
        let rhs = enc_imp(&sigma_at(&id, &x).unwrap(), &sigma_at(&id, &y).unwrap());
        // ⊢ lhs = lhs_nf, ⊢ rhs = rhs_nf, with lhs_nf == rhs_nf.
        let lhs_nf = crate::init::eq::beta_nf(lhs.clone());
        let rhs_nf = crate::init::eq::beta_nf(rhs.clone());
        let eq = lhs_nf.trans(rhs_nf.sym().unwrap()).unwrap(); // ⊢ lhs = rhs
        let gen_thm = eq
            .all_intro("Y", phi())
            .unwrap()
            .all_intro("X", phi())
            .unwrap();
        debug_assert_eq!(gen_thm.concl(), goal);
        gen_thm
    }
}
