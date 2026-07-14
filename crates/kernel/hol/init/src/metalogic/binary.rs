//! **The binary `Derivable_L` engine** — a two-argument twin of
//! [`crate::metalogic`], for judgements `d n w` over a *pair* of carrier types
//! `(nt_ty, word_ty)` rather than a single reified formula.
//!
//! [`crate::init::regex`]'s `Matches r w` is exactly this shape hand-rolled;
//! the CFG stratum ([`crate::grammar::cfg`]) is data-driven from a grammar env
//! the way [`crate::wasm::relation`] is data-driven from a spec, so it wants the
//! generic packaged form. We pay ~one screenful once here instead of a pair
//! carrier `prod nt word` that would pollute every clause, soundness predicate,
//! and consumer statement with `fst`/`snd` projections (and needs prod's private
//! pair constructors — see the recorded prod `delta_all` over-unfolding gotcha).
//!
//! The judgement is
//!
//! ```text
//!   Derives_L n w  :=  ∀d : nt_ty → word_ty → bool. Closed_L d ⟹ d n w
//! ```
//!
//! with `Closed_L d` the right-nested conjunction of the rule set's clauses.
//! Nothing here is added to `covalence-core`: every move is an existing kernel
//! primitive, and `conj`/`nth_conjunct`/`conj_thms` are reused verbatim from the
//! unary engine.

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::TermExt;
use crate::metalogic::{conj, nth_conjunct};

/// A **binary rule set** over carrier types `(nt_ty, word_ty)`.
///
/// `clauses(d_apply)` lays out the closure clauses (in a fixed order), each a
/// `bool`-typed term, using `d_apply(n, w)` for every `d n w` occurrence — the
/// same closure builds the clauses for the bound `d` (to *state* `Derives_L`)
/// and for `d := pred` (to *discharge* it in [`rule_induction2`]).
pub struct RuleSet2<'a> {
    /// The first carrier type (non-terminal tags — `nat` for the CFG stratum).
    pub nt_ty: Type,
    /// The second carrier type (words — `list u8` for the CFG stratum).
    pub word_ty: Type,
    /// Build the closure clauses for a given `d n w` application builder.
    #[allow(clippy::type_complexity)]
    pub clauses: Box<dyn Fn(&dyn Fn(&Term, &Term) -> Result<Term>) -> Result<Vec<Term>> + 'a>,
}

impl<'a> RuleSet2<'a> {
    /// Construct a binary rule set from its carrier types and a clause builder.
    pub fn new(
        nt_ty: Type,
        word_ty: Type,
        clauses: impl Fn(&dyn Fn(&Term, &Term) -> Result<Term>) -> Result<Vec<Term>> + 'a,
    ) -> Self {
        RuleSet2 {
            nt_ty,
            word_ty,
            clauses: Box::new(clauses),
        }
    }

    /// `nt_ty → word_ty → bool` — the type of the impredicative predicate `d`.
    pub fn pred_ty(&self) -> Type {
        Type::fun(
            self.nt_ty.clone(),
            Type::fun(self.word_ty.clone(), Type::bool()),
        )
    }

    /// The predicate variable `d : nt_ty → word_ty → bool`.
    pub fn d_var(&self) -> Term {
        Term::free("d", self.pred_ty())
    }

    /// The number of closure clauses (computed by laying them out for `d`).
    pub fn n_clauses(&self) -> Result<usize> {
        Ok((self.clauses)(&|n, w| self.d_var().apply(n.clone())?.apply(w.clone()))?.len())
    }
}

/// `Closed_L d` — the right-nested conjunction of the rule set's clauses, with
/// `d n w` filled by `d_apply`.
pub fn closed_conj2(rs: &RuleSet2, d_apply: &dyn Fn(&Term, &Term) -> Result<Term>) -> Result<Term> {
    conj((rs.clauses)(d_apply)?)
}

/// `Closed_L d` for the bound predicate variable `d`.
pub fn closed_for_var2(rs: &RuleSet2) -> Result<Term> {
    let d = rs.d_var();
    closed_conj2(rs, &|n, w| d.clone().apply(n.clone())?.apply(w.clone()))
}

/// `Derives_L n w := ∀d. Closed_L d ⟹ d n w`.
pub fn derivable2(rs: &RuleSet2, n: &Term, w: &Term) -> Result<Term> {
    let d = rs.d_var();
    let closed_d = closed_for_var2(rs)?;
    let d_nw = d.apply(n.clone())?.apply(w.clone())?;
    let body = closed_d.imp(d_nw)?;
    body.forall("d", rs.pred_ty())
}

/// Build a derivation `⊢ Derives_L n w` from a function that, under the assumed
/// `Closed_L d`, derives `⊢ d n w`. The shared spine of every binary derivation
/// constructor (mirrors [`crate::metalogic::derive_via_closed`]).
pub fn derive_via_closed2(
    rs: &RuleSet2,
    build_d_nw: impl FnOnce(&Thm, &dyn Fn(&Term, &Term) -> Result<Term>) -> Result<Thm>,
) -> Result<Thm> {
    let d = rs.d_var();
    let closed_t = closed_for_var2(rs)?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d
    let d_apply = |n: &Term, w: &Term| d.clone().apply(n.clone())?.apply(w.clone());
    let d_nw = build_d_nw(&assumed, &d_apply)?; // {Closed d, …} ⊢ d n w
    d_nw.imp_intro(&closed_t)?.all_intro("d", rs.pred_ty())
}

/// A premise fed to [`derive_mixed`]: either a *side* condition already proved
/// outright (`Matches ⌜c⌝ w` for a terminal segment — discharged by direct
/// `imp_elim`), or a *sub-derivation* `⊢ Derives_L nⱼ wⱼ` for a non-terminal
/// segment (opened under the assumed `Closed d` first).
pub enum Premise {
    /// A side antecedent proved outside the derivability predicate.
    Side(Thm),
    /// A sub-derivation `⊢ Derives_L nⱼ wⱼ`.
    Derivation(Thm),
}

/// **Apply clause `clause_idx`** of a binary rule set: peel its word `∀`s with
/// `word_args` (in the clause's quantifier order), then discharge its
/// antecedents with `premises` in order, yielding `⊢ Derives_L n w`.
///
/// The mixed-premise generalisation of [`crate::wasm::relation::derive`]: a
/// [`Premise::Side`] is a plain `imp_elim`; a [`Premise::Derivation`] is opened
/// to `d nⱼ wⱼ` under the assumed `Closed d` (via `all_elim(d) . imp_elim`)
/// first, exactly the relation-engine move. The kernel re-checks every step.
pub fn derive_mixed(
    rs: &RuleSet2,
    clause_idx: usize,
    n_clauses: usize,
    word_args: &[Term],
    premises: Vec<Premise>,
) -> Result<Thm> {
    derive_via_closed2(rs, |assumed, _d_apply| {
        let mut clause = nth_conjunct(assumed.clone(), clause_idx, n_clauses)?;
        for w in word_args {
            clause = clause.all_elim(w.clone())?;
        }
        for prem in premises {
            let ant = match prem {
                Premise::Side(thm) => thm,
                Premise::Derivation(der) => der.all_elim(rs.d_var())?.imp_elim(assumed.clone())?,
            };
            clause = clause.imp_elim(ant)?;
        }
        Ok(clause)
    })
}

/// **Generic rule induction over `Derives_L`.** Given a predicate
/// `pred : nt_ty → word_ty → bool` and a proof of each closure clause *for
/// `d := pred`* (in clause order), conclude
///
/// ```text
///   ⊢ ∀n w. Derives_L n w ⟹ pred n w
/// ```
///
/// `deriv_nw` is `Derives_L n w` with `n`/`w` the free variables named by
/// `(n_name, n_ty)` / `(w_name, w_ty)` that the conclusion generalises.
pub fn rule_induction2(
    pred: &Term,
    clause_proofs: Vec<Thm>,
    deriv_nw: &Term,
    n_name: &str,
    n_ty: Type,
    w_name: &str,
    w_ty: Type,
) -> Result<Thm> {
    let closed_pred_thm = crate::metalogic::conj_thms(clause_proofs)?;

    // Derives_L n w ⊢ Derives_L n w
    //               ⊢ ∀d. Closed d ⟹ d n w
    //     (inst d := pred)  Closed pred ⟹ pred n w
    //     (imp_elim Closed pred)         pred n w
    let assumed = Thm::assume(deriv_nw.clone())?;
    let pred_nw = assumed.all_elim(pred.clone())?.imp_elim(closed_pred_thm)?;

    pred_nw
        .imp_intro(deriv_nw)?
        .all_intro(w_name, w_ty)?
        .all_intro(n_name, n_ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_hol_eval::mk_nat;

    // A tiny binary logic to exercise the engine end to end, over
    // `(nt_ty, word_ty) = (nat, nat)`:
    //   rule z:            d 0 0
    //   rule s:  d n w ⟹  d 0 (succ w)          (one recursive premise)
    // (Meaningless as a "grammar"; it just drills every path.)
    fn toy_rule_set() -> RuleSet2<'static> {
        RuleSet2::new(Type::nat(), Type::nat(), |d_apply| {
            let zero = mk_nat(0u32);
            // clause 0: d 0 0
            let c0 = d_apply(&zero, &zero)?;
            // clause 1: ∀n w. d n w ⟹ d 0 (succ w)
            let n = Term::free("n", Type::nat());
            let w = Term::free("w", Type::nat());
            let succ_w = crate::init::nat::succ(w.clone());
            let body = d_apply(&n, &w)?.imp(d_apply(&zero, &succ_w)?)?;
            let c1 = body.forall("w", Type::nat())?.forall("n", Type::nat())?;
            Ok(vec![c0, c1])
        })
    }

    #[test]
    fn derivable_shape_and_clause_count() {
        let rs = toy_rule_set();
        assert_eq!(rs.n_clauses().unwrap(), 2);
        let zero = mk_nat(0u32);
        let prop = derivable2(&rs, &zero, &zero).unwrap();
        // `∀d. Closed d ⟹ d 0 0` is a closed bool proposition.
        assert_eq!(prop.type_of().unwrap(), Type::bool());
    }

    #[test]
    fn derive_axiom_and_step() {
        let rs = toy_rule_set();
        let n = rs.n_clauses().unwrap();
        let zero = mk_nat(0u32);

        // ⊢ Derives 0 0  (axiom clause: no word `∀`s, no premises)
        let base = derive_mixed(&rs, 0, n, &[], vec![]).unwrap();
        assert!(base.hyps().is_empty());
        assert_eq!(base.concl(), &derivable2(&rs, &zero, &zero).unwrap());

        // ⊢ Derives 0 (succ 0)  (recursive clause, discharging the base)
        let succ0 = crate::init::nat::succ(zero.clone());
        let step = derive_mixed(
            &rs,
            1,
            n,
            &[zero.clone(), zero.clone()],
            vec![Premise::Derivation(base)],
        )
        .unwrap();
        assert!(step.hyps().is_empty());
        assert_eq!(step.concl(), &derivable2(&rs, &zero, &succ0).unwrap());
    }
}
