//! **Peano arithmetic as a deep object theory, with the soundness /
//! transport map to HOL** (Phase B of `docs/peano-arithmetic-plan.md`).
//!
//! [`fol`](super::fol) reified PA's locally-nameless syntax + substitution;
//! [`deep`](super::deep) gave the standard interpretation `⟦·⟧` into HOL
//! `nat`/`bool`. Here we build PA's **derivability** and prove **soundness**:
//! every PA derivation denotes a valid HOL theorem, i.e. the transport
//! `PA(A) ⟹ HOL(A)` (`docs/VISION.md` §2 — PA as an object logic, HOL the
//! metalogic).
//!
//! ## The shape of the soundness map
//!
//! A [`Derivation`] is *both* a reified PA formula ([`Fol`]) **and** a genuine
//! hypothesis-free HOL [`Thm`] of that formula's denotation `⟦A⟧` — the two
//! are built in lock-step, so *constructing a derivation and establishing
//! `⊢ ⟦A⟧` are the same act* (the LCF discipline, one level up, exactly as
//! [`crate::init::prop`]'s `derive_axiom`/`derive_mp` pair a reified formula
//! with its `Thm`). The PA **axioms** are the proven `nat` theorems in
//! [`crate::init::nat`]; the **inference rules** forward to the kernel; and
//! the **induction schema** — the one ingredient beyond first-order logic
//! that makes the theory *Peano* — discharges to [`Thm::nat_induct`].
//!
//! Because every step is kernel-checked and every leaf is a genuine theorem,
//! a [`Derivation`]'s `thm` is an outright HOL theorem with no PA postulate
//! assumed: **PA is sound in HOL with nothing assumed.** This is the
//! constructive form of `⊢ Derivable_PA ⌜A⌝ ⟹ ⟦A⟧` — the per-derivation
//! transport; the single ∀-closed impredicative statement (the Church-fold
//! `inst d := ⟦·⟧`) is recorded as the remaining step in the module
//! `SKELETONS.md`.

use covalence_core::{Result, Term, Thm};

use super::deep::denote_closed;
use super::fol::Fol;
use crate::init::ext::ThmExt;
#[cfg(test)]
use crate::init::ext::TermExt;
use crate::init::nat;

/// A **PA derivation**: a reified PA formula together with a genuine,
/// hypothesis-free HOL theorem of its denotation `⟦formula⟧`. The two move
/// together — see the [module docs](self).
#[derive(Clone, Debug)]
pub struct Derivation {
    /// The reified PA formula this derivation establishes.
    pub formula: Fol,
    /// `⊢ ⟦formula⟧` — the HOL theorem the formula denotes to (the soundness
    /// witness / transport of this derivation).
    pub thm: Thm,
}

impl Derivation {
    fn new(formula: Fol, thm: Thm) -> Self {
        Self { formula, thm }
    }

    /// The transported HOL theorem (`⊢ ⟦formula⟧`) — the soundness map applied
    /// to this derivation.
    pub fn into_thm(self) -> Thm {
        self.thm
    }
}

// ============================================================================
// PA axioms (each: reified formula + its proven `nat` denotation)
// ============================================================================

/// The PA term `0`.
pub fn zero() -> Fol {
    Fol::Zero
}
/// The PA term `S t`.
pub fn succ(t: Fol) -> Fol {
    Fol::Succ(Box::new(t))
}
/// The PA term `a + b`.
pub fn add(a: Fol, b: Fol) -> Fol {
    Fol::Add(Box::new(a), Box::new(b))
}
/// The PA term `a · b`.
pub fn mul(a: Fol, b: Fol) -> Fol {
    Fol::Mul(Box::new(a), Box::new(b))
}
/// A PA free variable `fvar k`.
pub fn var(k: u64) -> Fol {
    Fol::FVar(k)
}

/// **PA1.** `∀x. ¬(0 = S x)` — zero is not a successor.
///
/// Reified `∀. ¬(0 = S(bvar 0))`; denotation `⊢ ∀x. ¬(0 = S x)` is
/// [`nat::zero_ne_succ`].
pub fn zero_ne_succ() -> Result<Derivation> {
    let formula = Fol::All(Box::new(Fol::Neg(Box::new(Fol::Eq(
        Box::new(Fol::Zero),
        Box::new(Fol::Succ(Box::new(Fol::BVar(0)))),
    )))));
    let thm = denote_matches(&formula, nat::zero_ne_succ())?;
    Ok(Derivation::new(formula, thm))
}

/// **PA2.** `∀x y. S x = S y ⟹ x = y` — successor is injective.
/// Denotation is [`nat::succ_inj`].
pub fn succ_inj() -> Result<Derivation> {
    // ∀.∀. (S(bvar1) = S(bvar0)) ⟹ (bvar1 = bvar0)
    let formula = Fol::All(Box::new(Fol::All(Box::new(Fol::Imp(
        Box::new(Fol::Eq(
            Box::new(Fol::Succ(Box::new(Fol::BVar(1)))),
            Box::new(Fol::Succ(Box::new(Fol::BVar(0)))),
        )),
        Box::new(Fol::Eq(Box::new(Fol::BVar(1)), Box::new(Fol::BVar(0)))),
    )))));
    let thm = denote_matches(&formula, nat::succ_inj())?;
    Ok(Derivation::new(formula, thm))
}

/// **PA3.** `∀x. 0 + x = x` — addition's base equation.
/// Denotation is [`nat::add_base`].
pub fn add_base() -> Result<Derivation> {
    let formula = Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Add(Box::new(Fol::Zero), Box::new(Fol::BVar(0)))),
        Box::new(Fol::BVar(0)),
    )));
    let thm = denote_matches(&formula, nat::add_base())?;
    Ok(Derivation::new(formula, thm))
}

/// **PA4.** `∀x y. S x + y = S (x + y)` — addition's step equation.
/// Denotation is [`nat::add_step`].
pub fn add_step() -> Result<Derivation> {
    let formula = Fol::All(Box::new(Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Add(
            Box::new(Fol::Succ(Box::new(Fol::BVar(1)))),
            Box::new(Fol::BVar(0)),
        )),
        Box::new(Fol::Succ(Box::new(Fol::Add(
            Box::new(Fol::BVar(1)),
            Box::new(Fol::BVar(0)),
        )))),
    )))));
    let thm = denote_matches(&formula, nat::add_step())?;
    Ok(Derivation::new(formula, thm))
}

/// **PA5.** `∀x. 0 · x = 0` — multiplication's base equation.
/// Denotation is [`nat::mul_base`].
pub fn mul_base() -> Result<Derivation> {
    let formula = Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Mul(Box::new(Fol::Zero), Box::new(Fol::BVar(0)))),
        Box::new(Fol::Zero),
    )));
    let thm = denote_matches(&formula, nat::mul_base())?;
    Ok(Derivation::new(formula, thm))
}

/// **PA6.** `∀x y. S x · y = y + x · y` — multiplication's step equation.
/// Denotation is [`nat::mul_step`].
pub fn mul_step() -> Result<Derivation> {
    let formula = Fol::All(Box::new(Fol::All(Box::new(Fol::Eq(
        Box::new(Fol::Mul(
            Box::new(Fol::Succ(Box::new(Fol::BVar(1)))),
            Box::new(Fol::BVar(0)),
        )),
        Box::new(Fol::Add(
            Box::new(Fol::BVar(0)),
            Box::new(Fol::Mul(Box::new(Fol::BVar(1)), Box::new(Fol::BVar(0)))),
        )),
    )))));
    let thm = denote_matches(&formula, nat::mul_step())?;
    Ok(Derivation::new(formula, thm))
}

/// Check that `thm`'s conclusion is *exactly* the denotation `⟦formula⟧`, so
/// pairing them in a [`Derivation`] is honest. Returns the (unchanged) `thm`
/// on success; an error if the axiom's stated formula and its `nat`-theorem
/// witness disagree. This is the soundness invariant for the axiom leaves.
fn denote_matches(formula: &Fol, thm: Thm) -> Result<Thm> {
    let want = denote_closed(formula);
    if thm.concl() != &want {
        return Err(covalence_core::Error::ConnectiveRule(format!(
            "pa: axiom denotation mismatch:\n  want ⟦A⟧ = {want}\n  got  thm  = {}",
            thm.concl()
        )));
    }
    Ok(thm)
}

// ============================================================================
// Inference rules (forward to the kernel on the denotations)
// ============================================================================

/// **∀-elimination (specialize).** From `⊢ ∀x. P` and a *closed* PA term `t`,
/// derive `P[t/x]`. The reified result instantiates the bound variable; the
/// denotation forwards to [`Thm::all_elim`].
pub fn specialize(univ: &Derivation, witness: &Fol) -> Result<Derivation> {
    let Fol::All(body) = &univ.formula else {
        return Err(covalence_core::Error::ConnectiveRule(
            "pa::specialize: derivation is not a ∀".into(),
        ));
    };
    let formula = body.open(witness);
    // The HOL denotation of the witness term (closed → empty context).
    let w = super::deep::denote_term(witness, &[]);
    let thm = univ.thm.clone().all_elim(w)?;
    // Cross-check the kernel result equals the reified result's denotation.
    let thm = denote_matches(&formula, thm)?;
    Ok(Derivation::new(formula, thm))
}

/// **⟹-elimination (modus ponens).** From `⊢ A ⟹ B` and `⊢ A`, derive `B`.
pub fn mp(imp: &Derivation, ante: &Derivation) -> Result<Derivation> {
    let Fol::Imp(_a, b) = &imp.formula else {
        return Err(covalence_core::Error::ConnectiveRule(
            "pa::mp: first derivation is not an implication".into(),
        ));
    };
    let formula = (**b).clone();
    let thm = imp.thm.clone().imp_elim(ante.thm.clone())?;
    let thm = denote_matches(&formula, thm)?;
    Ok(Derivation::new(formula, thm))
}

// ============================================================================
// The induction schema — what makes the theory *Peano*
// ============================================================================

/// **PA induction schema.** Given a derivation of the base `P(0)` and a
/// derivation of the step `P(x) ⟹ P(S x)` (with `x` the free atom `k`),
/// derive `∀x. P(x)`.
///
/// `base.formula` must be `P` opened at `0`; `step.formula` must be
/// `P(fvar k) ⟹ P(S(fvar k))`. The reified conclusion re-closes `P` over the
/// atom `k`; the denotation discharges to [`Thm::nat_induct`] (the schema case
/// uses HOL `nat` induction — the "the schema case uses HOL `nat` induction"
/// of the plan §B3).
pub fn induct(p_body: &Fol, k: u64, base: &Derivation, step: &Derivation) -> Result<Derivation> {
    use covalence_core::subst::close;
    // Reified conclusion: ∀. P  where P is `p_body` with atom k closed to bvar0.
    let formula = Fol::All(Box::new(p_body.close(k)));

    // The HOL **motive** `p_hol := λn:nat. ⟦p_body⟧[pa.v{k} ↦ n]`. We denote
    // `p_body` (which mentions the free atom k as the HOL free var pa.v{k}),
    // then HOL-close that name into the binder. `nat_induct` requires base /
    // step to be `p_hol 0` / `p_hol n ⟹ p_hol (S n)`, so we β-bridge the
    // axiom-shaped denotations into that motive-applied form.
    let p_den = denote_closed(p_body); // ⟦P⟧ with pa.v{k} free
    let p_hol = Term::abs(
        covalence_core::Type::nat(),
        close(&p_den, &super::deep::fvar_hol_name(k)),
    );

    // base.thm : ⊢ ⟦P(0)⟧ = ⟦P[k:=0]⟧.  Want ⊢ p_hol 0.
    let zero_hol = Term::nat_lit(0u32);
    let base_app = Thm::beta_conv(Term::app(p_hol.clone(), zero_hol))?; // ⊢ p_hol 0 = ⟦P(0)⟧
    let base_motive = base_app.sym()?.eq_mp(base.thm.clone())?; // ⊢ p_hol 0

    // step.thm : ⊢ ⟦P(v) ⟹ P(S v)⟧ = (⟦P(v)⟧ ⟹ ⟦P(Sv)⟧).  Want
    // ⊢ p_hol n ⟹ p_hol (S n).  Re-express both sides via β.
    let n = super::deep::fvar_hol(k); // the induction variable pa.v{k} : nat
    let step_app_n = Thm::beta_conv(Term::app(p_hol.clone(), n.clone()))?; // p_hol n = ⟦P(v)⟧
    let succ_n = Term::app(covalence_core::defs::nat_succ(), n);
    let step_app_sn = Thm::beta_conv(Term::app(p_hol.clone(), succ_n))?; // p_hol (Sn) = ⟦P(Sv)⟧
    // Rewrite the implication's antecedent & consequent back to p_hol form.
    let step_motive = step
        .thm
        .clone()
        .rewrite(&step_app_n.sym()?)?
        .rewrite(&step_app_sn.sym()?)?; // ⊢ p_hol n ⟹ p_hol (Sn)

    // nat_induct: ⊢ ∀n. p_hol n. Its body `(λx.P) n` is still a β-redex
    // under the `∀n` binder; β-normalise so it equals the wanted denotation
    // `∀n. ⟦P⟧[n]`.
    let thm = Thm::nat_induct(base_motive, step_motive)?;
    let to_nf = crate::init::eq::beta_nf(thm.concl().clone()); // ⊢ concl = reduced
    let thm = to_nf.eq_mp(thm)?;
    let thm = denote_matches(&formula, thm)?;
    Ok(Derivation::new(formula, thm))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(d: &Derivation) {
        assert!(d.thm.hyps().is_empty(), "derivation is hypothesis-free");
        assert!(d.thm.has_no_obs(), "derivation is oracle-free");
    }

    /// Every PA axiom is a genuine derivation: its `thm` is exactly the
    /// denotation of its reified formula, hypothesis- and oracle-free.
    #[test]
    fn all_axioms_are_genuine() {
        for d in [
            zero_ne_succ().unwrap(),
            succ_inj().unwrap(),
            add_base().unwrap(),
            add_step().unwrap(),
            mul_base().unwrap(),
            mul_step().unwrap(),
        ] {
            assert_genuine(&d);
            // The pairing invariant: thm.concl() == ⟦formula⟧.
            assert_eq!(d.thm.concl(), &denote_closed(&d.formula));
        }
    }

    /// `specialize` instantiates a ∀ axiom at a closed term and transports.
    /// `add_base : ∀x. 0 + x = x`  specialised at `S 0`  ⟹  `0 + S0 = S0`.
    #[test]
    fn specialize_add_base() {
        let ab = add_base().unwrap();
        let d = specialize(&ab, &succ(zero())).unwrap();
        assert_genuine(&d);
        // Reified formula is `0 + S0 = S0`.
        assert_eq!(
            d.formula,
            Fol::Eq(
                Box::new(Fol::Add(
                    Box::new(Fol::Zero),
                    Box::new(Fol::Succ(Box::new(Fol::Zero)))
                )),
                Box::new(Fol::Succ(Box::new(Fol::Zero))),
            )
        );
    }

    /// The headline worked theorem: **`∀x. x + 0 = x`** proved *by PA
    /// induction-on-derivations* and transported to a native HOL `nat` fact.
    ///
    /// `P(x) := x + 0 = x` (atom k=0). Base `0 + 0 = 0`; step
    /// `x + 0 = x ⟹ S x + 0 = S x`. Both are derived from the PA add
    /// equations, then `induct` discharges to `nat_induct`. The resulting
    /// `thm` is exactly the HOL `nat` theorem `⊢ ∀x. x + 0 = x` — and it must
    /// match `init::nat`'s independently-proved `add_zero`.
    #[test]
    fn worked_add_zero_by_induction() {
        // P(x) := (fvar0 + 0 = fvar0)
        let p_body = Fol::Eq(
            Box::new(Fol::Add(Box::new(Fol::FVar(0)), Box::new(Fol::Zero))),
            Box::new(Fol::FVar(0)),
        );

        // Base: P(0) = (0 + 0 = 0). Derive via specialize(add_base, 0).
        let base_formula = p_body.subst_fvar(0, &Fol::Zero); // 0 + 0 = 0
        let base_thm = {
            // add_base ∀x. 0+x=x  at  x:=0  gives  0+0=0.
            specialize(&add_base().unwrap(), &Fol::Zero).unwrap()
        };
        assert_eq!(base_thm.formula, base_formula);

        // Step: P(x) ⟹ P(Sx) = (x+0=x) ⟹ (Sx+0=Sx).
        let step_formula = Fol::Imp(
            Box::new(p_body.clone()),                       // x + 0 = x
            Box::new(p_body.subst_fvar(0, &succ(var(0)))),  // Sx + 0 = Sx
        );
        // HOL proof of the step's denotation, then pair into a Derivation.
        let want = denote_closed(&step_formula);
        let step_thm = prove_step(&want).expect("step proof");
        let step = Derivation::new(step_formula.clone(), step_thm);
        assert_eq!(step.formula, step_formula);

        // Induct: ∀x. x + 0 = x.
        let concl = induct(&p_body, 0, &base_thm, &step).unwrap();
        assert_genuine(&concl);
        assert_eq!(concl.formula, Fol::All(Box::new(p_body.close(0))));

        // Transport check: the HOL theorem equals init::nat's add_zero.
        assert_eq!(concl.thm.concl(), nat::add_zero().concl());
    }

    /// Helper: prove `⊢ ⟦step⟧` for the `add_zero` induction step, used by the
    /// worked theorem. Kept in the test module since it is proof-plumbing for
    /// the demonstration, not part of the PA surface.
    fn prove_step(want: &Term) -> Result<Thm> {
        use covalence_core::Term;
        let env0 = super::super::deep::fvar_hol(0);
        // add_step at a:=env0, b:=0: S(env0) + 0 = S(env0 + 0).
        let s_env0_plus_0 = nat::add_step()
            .all_elim(env0.clone())?
            .all_elim(Term::nat_lit(0u32))?; // ⊢ S env0 + 0 = S(env0 + 0)
        // Assume the IH: env0 + 0 = env0.
        let ih_concl = nat::add(env0.clone(), Term::nat_lit(0u32))
            .equals(env0.clone())?; // env0 + 0 = env0
        let ih = Thm::assume(ih_concl.clone())?;
        // S(env0 + 0) = S(env0)  by congruence under succ.
        let succ_cong = ih.cong_arg(covalence_core::defs::nat_succ())?; // ⊢ S(env0+0) = S env0
        // Chain: S env0 + 0 = S(env0+0) = S env0.
        let step_eq = s_env0_plus_0.trans(succ_cong)?; // {IH} ⊢ S env0 + 0 = S env0
        // Discharge the IH: (env0 + 0 = env0) ⟹ (S env0 + 0 = S env0).
        let thm = step_eq.imp_intro(&ih_concl)?;
        // Sanity: it is the wanted denotation (up to the kernel's term eq).
        assert_eq!(thm.concl(), want, "step denotation matches");
        Ok(thm)
    }
}
