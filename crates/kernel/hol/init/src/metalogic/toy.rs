//! **A toy logic** — a minimal, from-scratch second instance of the generic
//! [`Derivable_L`](super) engine, proving the engine is genuinely reusable (not
//! a PA-shaped mould). It is deliberately tiny: one nullary constructor, one
//! unary constructor, one axiom, one inference rule, a one-line denotation, and
//! soundness + projection driven entirely through [`super`].
//!
//! ## The syntax `Φ⟨'r⟩`
//!
//! Two constructors, encoded impredicatively exactly as
//! [`crate::init::prop`]:
//!
//! ```text
//!   Φ⟨'r⟩  :=  'r            -- tt   (a base truth)
//!            → ('r → 'r)     -- box  (a unary modality)
//!            → 'r
//! ```
//!
//! - `tt`   — the formula `⊤`;
//! - `box A` — a unary modality.
//!
//! ## The rule set `L`
//!
//! - **axiom**: `tt` is derivable;
//! - **rule** (necessitation-like): `∀A. d A ⟹ d ⌜box A⌝`.
//!
//! ## Denotation and soundness
//!
//! `⟦·⟧` instantiates `'r := bool`, `tt ↦ T`, `box ↦ λp. p` (the identity
//! modality). So `⟦tt⟧ = T` and `⟦box A⟧ = ⟦A⟧`. Soundness `⊢ Derivable_L A ⟹
//! ⟦A⟧` is discharged through [`super::rule_induction`]: the axiom clause is
//! `⟦tt⟧ = T` (true), the rule clause is `⟦A⟧ ⟹ ⟦box A⟧` = `⟦A⟧ ⟹ ⟦A⟧` (trivial).
//! The acceptance test derives `box (box tt)` purely, then projects in one move.

use covalence_core::subst::close;
use covalence_core::{Result, Term, Thm, Type};

use super::RuleSet;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::truth;

fn rty() -> Type {
    Type::tfree("r")
}
fn bool_ty() -> Type {
    Type::bool()
}

/// Handler names + slot-type builders, in fold order: `tt`, `box`.
const HANDLERS: [(&str, crate::UnaryTypeHandler); 2] = [
    ("tt", |r| r.clone()),
    ("box", |r| Type::fun(r.clone(), r.clone())),
];

fn handler_ty(name: &str, r: &Type) -> Type {
    HANDLERS
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, f)| f(r))
        .expect("toy: unknown handler")
}

fn handler(r: &Type, name: &str) -> Term {
    Term::free(name, handler_ty(name, r))
}

/// `Φ⟨r⟩ = (tt)→(box)→r`.
fn phi_at(r: &Type) -> Type {
    let mut acc = r.clone();
    for (name, _) in HANDLERS.iter().rev() {
        acc = Type::fun(handler_ty(name, r), acc);
    }
    acc
}

fn phi() -> Type {
    phi_at(&rty())
}
fn phi_at_bool() -> Type {
    phi_at(&bool_ty())
}

fn close_handlers(r: &Type, body: Term) -> Term {
    let mut acc = body;
    for (name, _) in HANDLERS.iter().rev() {
        acc = Term::abs(handler_ty(name, r), close(&acc, name));
    }
    acc
}

fn apply_handlers(r: &Type, enc: Term) -> Term {
    let mut acc = enc;
    for (name, _) in HANDLERS {
        acc = Term::app(acc, handler(r, name));
    }
    acc
}

// ---- constructors ----------------------------------------------------------

/// `enc(tt) : Φ⟨r⟩`.
pub fn tt_at(r: &Type) -> Term {
    close_handlers(r, handler(r, "tt"))
}

/// `enc(box A) : Φ⟨r⟩`.
pub fn box_at(r: &Type, a: Term) -> Term {
    close_handlers(r, Term::app(handler(r, "box"), apply_handlers(r, a)))
}

/// `enc(tt) : Φ⟨'r⟩`.
pub fn tt() -> Term {
    tt_at(&rty())
}
/// `enc(box A) : Φ⟨'r⟩`.
pub fn boxed(a: Term) -> Term {
    box_at(&rty(), a)
}

// ---- denotation ------------------------------------------------------------

/// The two `bool` handlers, in fold order: `(T, λp. p)`.
fn bool_handlers() -> [Term; 2] {
    let p = Term::free("p", bool_ty());
    let id = Term::abs(bool_ty(), close(&p, "p")); // λp. p
    [truth().concl().clone(), id]
}

/// `⟦A⟧ : bool` — the standard denotation. `tt ↦ T`, `box ↦ identity`.
pub fn denote(a: Term) -> Term {
    let mut t = covalence_core::subst::subst_tfree_in_term(&a, "r", &bool_ty());
    for h in bool_handlers() {
        t = Term::app(t, h);
    }
    t
}

/// `λA:Φ⟨bool⟩. ⟦A⟧` — the denotation predicate (`d := ⟦·⟧`).
pub fn denote_pred() -> Term {
    let big_a = Term::free("A", phi_at_bool());
    let body = {
        let mut t = big_a.clone();
        for h in bool_handlers() {
            t = Term::app(t, h);
        }
        t
    };
    Term::abs(phi_at_bool(), close(&body, "A"))
}

// ---- the rule set ----------------------------------------------------------

/// The toy logic's rule set: clause 0 = axiom `d ⌜tt⌝`; clause 1 = the rule
/// `∀A. d A ⟹ d ⌜box A⌝` (necessitation).
pub fn rule_set() -> RuleSet<'static> {
    RuleSet::new(phi(), |d_apply| {
        let r = rty();
        // axiom: d ⌜tt⌝
        let ax = d_apply(&tt_at(&r))?;
        // rule: ∀A. d A ⟹ d ⌜box A⌝
        let a = Term::free("A", phi());
        let rule = d_apply(&a)?
            .imp(d_apply(&box_at(&r, a.clone()))?)?
            .forall("A", phi())?;
        Ok(vec![ax, rule])
    })
}

/// `Derivable_L A := ∀d. Closed_L d ⟹ d A`.
pub fn derivable(a: &Term) -> Result<Term> {
    super::derivable(&rule_set(), a)
}

// ---- derivation constructors ----------------------------------------------

/// `⊢ Derivable_L ⌜tt⌝` — the axiom, as a pure derivability witness.
pub fn derive_tt() -> Result<Thm> {
    let rs = rule_set();
    let n = rs.n_clauses()?;
    super::derive_via_closed(&rs, |assumed, _d_apply| {
        super::nth_conjunct(assumed.clone(), 0, n)
    })
}

/// `⊢ Derivable_L ⌜A⌝ ⟹ Derivable_L ⌜box A⌝` — the necessitation rule, lifted
/// to derivability witnesses.
pub fn derive_box(a: &Term) -> Result<Thm> {
    let rs = rule_set();
    let n = rs.n_clauses()?;
    let der_a = derivable(a)?;
    let der_box = super::derive_via_closed(&rs, |assumed, d_apply| {
        // d ⌜A⌝ from the hypothesis Derivable_L ⌜A⌝.
        let da = Thm::assume(der_a.clone())?
            .all_elim(rs.d_var())?
            .imp_elim(assumed.clone())?; // {Der A, Closed d} ⊢ d ⌜A⌝
        // rule clause (index 1): ∀A. d A ⟹ d ⌜box A⌝
        let rule = super::nth_conjunct(assumed.clone(), 1, n)?.all_elim(a.clone())?;
        let _ = d_apply;
        rule.imp_elim(da) // ⊢ d ⌜box A⌝
    })?;
    der_box.imp_intro(&der_a)
}

// ---- soundness + projection ------------------------------------------------

/// Substitute `'r := bool` in a `bool`-typed term.
fn inst_bool(t: &Term) -> Term {
    covalence_core::subst::subst_tfree_in_term(t, "r", &bool_ty())
}

/// `⊢ Derivable_L ⌜A⌝ ⟹ ⟦A⟧` for a specific encoded formula `a` — soundness,
/// via [`super::rule_induction`] specialised to `a`.
pub fn soundness_at(a: &Term) -> Result<Thm> {
    let d_pred = denote_pred();

    let deriv_bool = inst_bool(&derivable(a)?);
    let assumed = Thm::assume(deriv_bool.clone())?;
    let specialized = assumed.all_elim(d_pred.clone())?; // Closed ⟦·⟧ ⟹ ⟦·⟧ a

    let closed_d = discharge_closed(&d_pred)?;
    let d_a = specialized.imp_elim(closed_d)?; // {Der a} ⊢ ⟦·⟧ a

    let a_bool = inst_bool(a);
    let beta = Thm::beta_conv(d_pred.apply(a_bool)?)?; // ⊢ ⟦·⟧ a = ⟦a⟧
    let den_a = beta.eq_mp(d_a)?;
    den_a.imp_intro(&deriv_bool)
}

/// `⊢ ∀A. Derivable_L A ⟹ ⟦·⟧ A` — soundness as a single rule-induction, via
/// the generic [`super::rule_induction`] (exercising that engine path, the
/// way [`crate::init::prop::soundness_general`] does for prop). The per-clause
/// proofs are the two conjuncts of `discharge_closed`.
pub fn soundness_general() -> Result<Thm> {
    let d_pred = denote_pred();
    let closed = discharge_closed(&d_pred)?;
    // Split the right-nested `Closed ⟦·⟧` back into its two clause proofs.
    let ax_clause = closed.clone().and_elim_l()?;
    let rule_clause = closed.and_elim_r()?;
    let deriv_bool = inst_bool(&derivable(&Term::free("A", phi()))?);
    super::rule_induction(
        &d_pred,
        vec![ax_clause, rule_clause],
        &deriv_bool,
        "A",
        phi_at_bool(),
    )
}

/// `⊢ Closed_L ⟦·⟧` — discharge both clauses for `d := ⟦·⟧`.
fn discharge_closed(d_pred: &Term) -> Result<Thm> {
    let r = bool_ty();

    // β-bridge `⊢ ⟦·⟧⌜enc⌝ = nf` + the nf, for a closed `enc`.
    let br = |enc: Term| -> Result<(Thm, Term)> {
        let beta = Thm::beta_conv(d_pred.clone().apply(enc)?)?;
        let denoted = beta.concl().as_eq().expect("eq").1.clone();
        let to_nf = crate::init::eq::beta_nf(denoted);
        let nf = to_nf.concl().as_eq().expect("eq").1.clone();
        Ok((beta.trans(to_nf)?, nf))
    };

    // axiom: ⟦·⟧⌜tt⌝, nf = T.
    let (br_tt, _) = br(tt_at(&r))?;
    let ax_clause = br_tt.sym()?.eq_mp(truth())?; // ⊢ ⟦·⟧⌜tt⌝

    // rule: ∀A. ⟦·⟧ A ⟹ ⟦·⟧⌜box A⌝.  ⟦box A⟧ = ⟦A⟧ so this is A ⟹ A.
    let a = Term::free("A", phi_at_bool());
    let (br_a, a_nf) = br(a.clone())?; // ⟦·⟧ A, nf = ⟦A⟧ (= A folded)
    let (br_box, box_nf) = br(box_at(&r, a.clone()))?; // ⟦·⟧⌜box A⌝, nf = ⟦A⟧
    debug_assert_eq!(a_nf, box_nf, "toy: box is the identity modality");
    // A_nf ⊢ A_nf, then imp_intro; rewrite both back to the ⟦·⟧ forms.
    let pred_a = br_a.concl().as_eq().expect("eq").0.clone(); // ⟦·⟧ A
    let assumed = Thm::assume(pred_a.clone())?;
    let a_den = br_a.clone().eq_mp(assumed)?; // ⊢ ⟦A⟧
    let imp = a_den.imp_intro(&pred_a)?; // ⊢ ⟦·⟧ A ⟹ ⟦A⟧
    // rewrite the consequent ⟦A⟧ → ⟦·⟧⌜box A⌝.
    let rule_clause = imp.rewrite(&br_box.sym()?)?.all_intro("A", phi_at_bool())?;

    super::conj_thms(vec![ax_clause, rule_clause])
}

/// **Project** a finished derivation `der : ⊢ Derivable_L ⌜A⌝` to `⊢ ⟦A⟧` in
/// one step (soundness `imp_elim` + a final β-normalisation).
pub fn project(a: &Term, der: Thm) -> Result<Thm> {
    let snd = soundness_at(a)?;
    let der_bool = der.inst_tfree("r", bool_ty())?;
    super::project_normalized(snd, der_bool)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
        assert!(thm.has_no_obs(), "oracle-free");
    }

    /// The axiom is a genuine derivability witness, NOT a denotation.
    #[test]
    fn tt_is_derivable() {
        let der = derive_tt().unwrap();
        assert_genuine(&der);
        assert_eq!(der.concl(), &derivable(&tt()).unwrap());
    }

    /// Necessitation lifts a derivability witness.
    #[test]
    fn box_rule_is_genuine() {
        let mp = derive_box(&tt()).unwrap();
        assert_genuine(&mp);
        let expected = derivable(&tt())
            .unwrap()
            .imp(derivable(&boxed(tt())).unwrap())
            .unwrap();
        assert_eq!(mp.concl(), &expected);
    }

    /// **Acceptance**: derive `box (box tt)` purely (by axiom + two rule
    /// applications), then project in one step to `⊢ ⟦box (box tt)⟧ = T`.
    #[test]
    fn derive_box_box_tt_and_project() {
        // ⊢ Derivable_L ⌜tt⌝
        let d_tt = derive_tt().unwrap();
        // ⊢ Derivable_L ⌜box tt⌝   (necessitation applied to tt)
        let box_rule = derive_box(&tt()).unwrap();
        let d_box_tt = box_rule.imp_elim(d_tt).unwrap();
        // ⊢ Derivable_L ⌜box (box tt)⌝
        let box_rule2 = derive_box(&boxed(tt())).unwrap();
        let d_box_box_tt = box_rule2.imp_elim(d_box_tt).unwrap();
        assert_genuine(&d_box_box_tt);
        // The derivation is pure data: Derivable_L ⌜…⌝, not ⟦…⟧.
        assert_eq!(
            d_box_box_tt.concl(),
            &derivable(&boxed(boxed(tt()))).unwrap()
        );

        // Project in one step: ⟦box (box tt)⟧ = T.
        let projected = project(&boxed(boxed(tt())), d_box_box_tt).unwrap();
        assert_genuine(&projected);
        assert_eq!(projected.concl(), truth().concl());
    }

    /// The generic `rule_induction` path yields a genuine soundness theorem
    /// `⊢ ∀A. Derivable_L A ⟹ ⟦·⟧ A`.
    #[test]
    fn soundness_general_is_genuine() {
        let thm = soundness_general().unwrap();
        assert_genuine(&thm);
    }
}
