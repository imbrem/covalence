//! **Generic rule application over any [`RuleSet`].** The forward, composition
//! direction of the impredicative engine: given a rule set `L`, a clause index
//! `k`, witnesses for the clause's `∀`-bound metavariables, and derivability
//! premises for its essential antecedents, mint
//!
//! ```text
//!   ⊢ Derivable_L (σ concl)
//! ```
//!
//! where `σ` substitutes the clause's `float_vars` by `float_witnesses`. This is
//! the [`crate::metalogic`] engine's *general* rule-instance constructor — the
//! move that [`crate::metalogic::mm_database`]'s `derive_clause` performs inside a
//! per-theorem `ClauseCtx` during replay, and that
//! [`crate::metalogic::relations::derivable_db_mp`] performs for the fixed
//! modus-ponens clause of the database-value world — lifted to *any* `RuleSet`
//! and *any* clause. `mm_session` builds the high-level Metamath-database API on
//! top of it.
//!
//! # The construction (mirrors `derive_clause`)
//!
//! Everything runs under [`super::derive_via_closed`]: assume `Closed_L d`,
//! derive `{Closed_L d, …} ⊢ d (σ concl)`, then `imp_intro` the `Closed_L d`
//! assumption and `all_intro d` — yielding a genuine, oracle-free
//! `⊢ Derivable_L (σ concl)` (essential-premise hypotheses surface as the
//! result's hypotheses, exactly as they do on the premises). Inside:
//!
//! 1. [`super::nth_conjunct`] extracts clause `k` from the assumed `Closed_L d`
//!    (an `n`-clause right-nested conjunction);
//! 2. the clause is `∀float_vars. (⋀ d essᵢ ⟹)? d concl` with `float_vars[0]`
//!    bound *outermost* (see `mm_database`'s `Clause::build`'s `.rev()`), so
//!    `all_elim`-ing the witnesses **in order** strips `float_vars[0]` first —
//!    `float_witnesses[i]` substitutes `float_vars[i]`;
//! 3. for each essential premise `⊢ Derivable_L (σ essᵢ)`, `all_elim d` +
//!    `imp_elim`-against-`Closed_L d` turns it into `d (σ essᵢ)`;
//! 4. those are `and_intro`-ed **right-nested** (matching [`super::conj`]'s
//!    association), and `imp_elim`-ed into the instantiated clause to reach
//!    `d (σ concl)`.
//!
//! A 0-essential clause is `∀float_vars. d concl`: no `imp`, so premises must be
//! empty and step 2 already lands `d (σ concl)`.
//!
//! # Soundness / no new trusted code
//!
//! Every step is an existing kernel rule (`all_elim`, `imp_elim`, `and_intro`,
//! `imp_intro`, `all_intro`). Nothing is postulated; a wrong witness count or a
//! premise that is not the expected `Derivable_L (σ essᵢ)` fails a kernel check
//! (or the explicit arity guard below) rather than fabricating a theorem. This is
//! the *construct* direction: it only ever builds a witness for the specific
//! instance the caller names.

use covalence_core::term::TermKind;
use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use super::{RuleSet, conj_thms, nth_conjunct};

fn apply_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("metalogic::apply: {}", msg.into()))
}

/// Whether the instantiated clause conclusion `t` carries an essential
/// **antecedent** — i.e. is a binary connective application `App(App(head, _), _)`
/// (the `⟹` a rule clause builds via `conj(prems)?.imp(…)`), as opposed to a
/// bare predicate application `d concl` = `App(d_free, concl)` (a 0-essential
/// clause). Used only for a *clear arity error* (premise count vs the clause's
/// essential count); it never affects the theorem built — the kernel's own
/// `imp_elim` (or the direct return of the 0-essential clause) does that.
/// **Not soundness-load-bearing:** a misclassification could only produce a
/// worse error message or a well-typed theorem, never a false one — every
/// conclusion is still assembled by sound kernel rules.
///
/// The discriminator is precise for our clauses: a `⟹`/`∧`/`∨`-headed clause
/// nests as `App(App(spec_head, …), …)`, so `f = App(spec_head, …)` is itself an
/// `App`; a bare `d concl` has `f = d` (a `Free`), which is *not* an `App`. We do
/// not need to distinguish `⟹` from `∧`/`∨` — only "has an antecedent" from
/// "does not" — and a clause's outermost connective is always the antecedent `⟹`
/// (the premise conjunction lives strictly *inside* it).
fn is_implication(t: &Term) -> bool {
    let TermKind::App(f, _) = t.kind() else {
        return false;
    };
    matches!(f.kind(), TermKind::App(head, _) if matches!(head.kind(), TermKind::Spec(_, _) | TermKind::Const(..)))
}

/// **Apply clause `clause_index` of rule set `rs` (which has `n_clauses`
/// clauses).**
///
/// Substitutes the clause's `∀`-bound metavariables by `float_witnesses` (in
/// binder order — `float_witnesses[0]` is the outermost binder) and discharges
/// its essential antecedents with `premises`, producing
///
/// ```text
///   ⊢ Derivable_L (σ concl)
/// ```
///
/// `premises[i]` must be `⊢ Derivable_L (σ essᵢ)` for the clause's `i`-th
/// essential (their hypotheses carry through to the result). The number of
/// premises must equal the clause's essential count; a mismatch is a clear error.
/// See the [module docs](self) for the construction and its soundness.
pub fn apply_rule(
    rs: &RuleSet,
    clause_index: usize,
    n_clauses: usize,
    float_witnesses: &[Term],
    premises: &[&Thm],
) -> Result<Thm> {
    // The predicate variable `d` `derive_via_closed` will `all_intro`; it is the
    // *same* `d` its `d_apply` closes over (both are `rs.d_var()`), so we can use
    // it to `all_elim` the premises' `∀d`.
    let d = rs.d_var();
    super::derive_via_closed(rs, |assumed, _d_apply| {
        // Clause `k`, still `∀float_vars. (⋀ d essᵢ ⟹)? d concl`, under `Closed_L d`.
        let mut clause = nth_conjunct(assumed.clone(), clause_index, n_clauses)?;

        // Strip the ∀-binders in order: witness[0] hits `float_vars[0]`, the
        // outermost binder.
        for w in float_witnesses {
            clause = clause.all_elim(w.clone())?;
        }

        // Does the instantiated clause carry an essential antecedent (an `⟹`)?
        let has_antecedent = is_implication(clause.concl());

        if premises.is_empty() {
            if has_antecedent {
                return Err(apply_err(
                    "clause has essential premises but none were supplied",
                ));
            }
            // 0-essential clause: `clause` is already `d (σ concl)`.
            return Ok(clause);
        }

        if !has_antecedent {
            return Err(apply_err(
                "premises were supplied but the clause has no essential antecedent",
            ));
        }

        // Turn each `⊢ Derivable_L (σ essᵢ)` into `d (σ essᵢ)` under `Closed_L d`,
        // then conjoin (right-nested) and discharge the clause's antecedent.
        let d_prems: Vec<Thm> = premises
            .iter()
            .map(|p| (*p).clone().all_elim(d.clone())?.imp_elim(assumed.clone()))
            .collect::<Result<_>>()?;
        clause.imp_elim(conj_thms(d_prems)?)
    })
}

/// **A premise-free rule / axiom-schema instance.** [`apply_rule`] with no
/// premises: for a clause `∀float_vars. d concl`, mint
/// `⊢ Derivable_L (σ concl)`. Errors if the named clause actually has essential
/// antecedents.
pub fn derive_axiom_instance(
    rs: &RuleSet,
    clause_index: usize,
    n_clauses: usize,
    float_witnesses: &[Term],
) -> Result<Thm> {
    apply_rule(rs, clause_index, n_clauses, float_witnesses, &[])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use crate::metalogic::{RuleSet, conj, derivable};
    use covalence_core::Type;

    // ------------------------------------------------------------------------
    // A tiny embedded propositional-calculus rule set over an uninterpreted
    // free-term carrier `Φ = nat`, to exercise `apply_rule` end-to-end.
    //
    // Encoding: `p k` = a propositional atom = `Term::free("p<k>", nat)`;
    // `⌜a ⟹ b⌝` = `imp(a, b)` via an uninterpreted binary former `mmimp`.
    //
    // Rules (clauses, in order):
    //   0. ax-1 : ∀A B.            d ⌜A ⟹ (B ⟹ A)⌝
    //   1. ax-mp: ∀A B. d A ∧ d ⌜A ⟹ B⌝ ⟹ d B
    // ------------------------------------------------------------------------

    fn phi() -> Type {
        Type::nat()
    }

    fn imp_fn() -> Term {
        Term::free("mmimp", Type::fun(phi(), Type::fun(phi(), phi())))
    }

    fn enc_imp(a: &Term, b: &Term) -> Term {
        imp_fn().apply(a.clone()).unwrap().apply(b.clone()).unwrap()
    }

    fn atom(k: u32) -> Term {
        Term::free(format!("p{k}"), phi())
    }

    /// The rule set: clause 0 = ax-1, clause 1 = ax-mp.
    fn prop_rs() -> RuleSet<'static> {
        RuleSet::new(phi(), move |d_apply| {
            let a = Term::free("A", phi());
            let b = Term::free("B", phi());

            // ax-1: ∀A B. d ⌜A ⟹ (B ⟹ A)⌝
            let ax1_body = d_apply(&enc_imp(&a, &enc_imp(&b, &a)))?;
            let ax1 = ax1_body.forall("B", phi())?.forall("A", phi())?;

            // ax-mp: ∀A B. (d A ∧ d ⌜A ⟹ B⌝) ⟹ d B
            let da = d_apply(&a)?;
            let dab = d_apply(&enc_imp(&a, &b))?;
            let db = d_apply(&b)?;
            let mp_body = da.and(dab)?.imp(db)?;
            let mp = mp_body.forall("B", phi())?.forall("A", phi())?;

            Ok(vec![ax1, mp])
        })
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem must be hypothesis-free");
    }

    /// `derive_axiom_instance` on the ax-1 clause: a hypothesis-free
    /// `⊢ Derivable_L ⌜p0 ⟹ (p1 ⟹ p0)⌝`.
    #[test]
    fn axiom_instance_ax1() {
        let rs = prop_rs();
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 2);
        let p0 = atom(0);
        let p1 = atom(1);

        // float witnesses A := p0, B := p1 (binder order A outermost).
        let thm = derive_axiom_instance(&rs, 0, n, &[p0.clone(), p1.clone()]).unwrap();
        assert_genuine(&thm);
        let want = derivable(&rs, &enc_imp(&p0, &enc_imp(&p1, &p0))).unwrap();
        assert_eq!(thm.concl(), &want);
    }

    /// `apply_rule` on the ax-mp clause: from `⊢ Der ⌜p0⌝` and
    /// `⊢ Der ⌜p0 ⟹ p1⌝` derive `⊢ Der ⌜p1⌝` — hypothesis-free when the premises
    /// are (here the premises are *assumed*, so the result carries their hyps).
    #[test]
    fn apply_rule_mp() {
        let rs = prop_rs();
        let n = rs.n_clauses().unwrap();
        let p0 = atom(0);
        let p1 = atom(1);
        let imp01 = enc_imp(&p0, &p1);

        // Premises: assume Der ⌜p0⌝ and Der ⌜p0 ⟹ p1⌝.
        let der_p0 = Thm::assume(derivable(&rs, &p0).unwrap()).unwrap();
        let der_imp = Thm::assume(derivable(&rs, &imp01).unwrap()).unwrap();

        // ax-mp clause: floats A := p0, B := p1; premises [der_p0, der_imp].
        let thm = apply_rule(&rs, 1, n, &[p0.clone(), p1.clone()], &[&der_p0, &der_imp]).unwrap();
        let want = derivable(&rs, &p1).unwrap();
        assert_eq!(thm.concl(), &want);
        // The two premise hypotheses surface.
        assert_eq!(thm.hyps().len(), 2);
    }

    /// A hypothesis-free axiom-schema instance feeds a further MP: `ax-1 @ (p0, p1)`
    /// mints the hypothesis-free `⊢ Der ⌜p0 ⟹ (p1 ⟹ p0)⌝`, which is exactly a
    /// `Der ⌜A ⟹ B⌝` (minor) for `A := p0`, `B := ⌜p1 ⟹ p0⌝`. Composing it by MP
    /// with an *assumed* major `Der ⌜p0⌝` yields `⊢ Der ⌜p1 ⟹ p0⌝` carrying just
    /// that one assumed hypothesis — the composite existence certified without any
    /// Metamath proof of `⌜p1 ⟹ p0⌝` being written.
    #[test]
    fn apply_rule_mp_composite_from_axiom_instance() {
        let rs = prop_rs();
        let n = rs.n_clauses().unwrap();
        let p0 = atom(0);
        let p1 = atom(1);

        // ax-1 @ (p0, p1): hypothesis-free ⊢ Der ⌜p0 ⟹ (p1 ⟹ p0)⌝.
        let ax1 = derive_axiom_instance(&rs, 0, n, &[p0.clone(), p1.clone()]).unwrap();
        assert_genuine(&ax1);
        assert_eq!(
            ax1.concl(),
            &derivable(&rs, &enc_imp(&p0, &enc_imp(&p1, &p0))).unwrap()
        );

        // Compose by MP: minor = ax1 (Der ⌜p0 ⟹ (p1 ⟹ p0)⌝), major = assumed
        // Der ⌜p0⌝; ax-mp floats A := p0, B := ⌜p1 ⟹ p0⌝.
        let b = enc_imp(&p1, &p0);
        let major = Thm::assume(derivable(&rs, &p0).unwrap()).unwrap();
        let composed = apply_rule(&rs, 1, n, &[p0.clone(), b.clone()], &[&major, &ax1]).unwrap();
        assert_eq!(composed.concl(), &derivable(&rs, &b).unwrap());
        assert_eq!(composed.hyps().len(), 1, "only the assumed major survives");
    }

    /// Mismatched arity errors: supplying premises to a premise-free (ax-1) clause
    /// fails, and supplying none to ax-mp fails.
    #[test]
    fn mismatched_premise_count_errors() {
        let rs = prop_rs();
        let n = rs.n_clauses().unwrap();
        let p0 = atom(0);
        let p1 = atom(1);
        let der_p0 = Thm::assume(derivable(&rs, &p0).unwrap()).unwrap();

        // ax-1 is premise-free: supplying a premise must error.
        let err = apply_rule(&rs, 0, n, &[p0.clone(), p1.clone()], &[&der_p0]);
        assert!(err.is_err(), "premise supplied to premise-free clause");

        // ax-mp needs 2 premises: supplying none must error.
        let err2 = apply_rule(&rs, 1, n, &[p0.clone(), p1.clone()], &[]);
        assert!(err2.is_err(), "no premises supplied to ax-mp");
    }

    /// `apply_rule` reproduces the `derivable_db_mp`-shaped MP theorem: closing MP
    /// over free `A`, `B` gives exactly `Der A ⟹ Der ⌜A⟹B⌝ ⟹ Der B`. Here we
    /// witness the *instance* form and check it matches a hand-built one.
    #[test]
    fn apply_rule_matches_hand_built_mp_instance() {
        let rs = prop_rs();
        let n = rs.n_clauses().unwrap();
        let p0 = atom(0);
        let p1 = atom(1);
        let imp01 = enc_imp(&p0, &p1);

        let der_p0 = Thm::assume(derivable(&rs, &p0).unwrap()).unwrap();
        let der_imp = Thm::assume(derivable(&rs, &imp01).unwrap()).unwrap();
        let via_apply =
            apply_rule(&rs, 1, n, &[p0.clone(), p1.clone()], &[&der_p0, &der_imp]).unwrap();

        // Hand-built: nth_conjunct(assumed,1,n) all_elim p1, p0; discharge with
        // the two `d`-of-premises. We just check the conclusion equals `Der ⌜p1⌝`.
        assert_eq!(via_apply.concl(), &derivable(&rs, &p1).unwrap());

        // Sanity: `conj` of the two clause bodies is `Closed_L` (association match).
        let d = rs.d_var();
        let d_apply = |f: &Term| d.clone().apply(f.clone());
        let clauses = (rs.clauses)(&d_apply).unwrap();
        let closed = conj(clauses).unwrap();
        assert_eq!(closed.type_of().unwrap(), Type::bool());
    }
}
