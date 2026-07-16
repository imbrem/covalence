//! **S3 ladder plumbing — the reusable derivation layer for unary
//! `Derivable_L` rule sets** (design `notes/vibes/lisp/acl2-s0-s3-design.md`
//! §6.1).
//!
//! Nothing in this module is ACL2-specific: every helper is generic over a
//! [`crate::metalogic::RuleSet`]. It packages the two moves that
//! [`crate::metalogic`] lacks and that its instances (`peano/pa.rs`,
//! `metalogic/toy.rs`, `init/prop.rs`) currently hand-roll per clause:
//!
//! 1. [`derive_mixed`] — the **unary twin of
//!    [`crate::metalogic::binary::derive_mixed`]**: fire clause `k` of the
//!    impredicative least fixpoint, peeling its `∀`s with `args` and
//!    discharging its antecedents with mixed [`Premise`]s (side conditions
//!    proved outright vs. sub-derivations opened under the assumed
//!    `Closed_L d`).
//! 2. the **β-bridge discharge helpers** ([`br`] / [`bridge_eq`] /
//!    [`expand_to_pred`]) — generalized from the private per-instance copies
//!    in `peano/pa.rs` and `metalogic/toy.rs`: moving facts between the
//!    *applied* predicate form `pred ⌜e⌝` a clause states and the β-normal
//!    denotation form a proof lands on. These are what a per-clause
//!    soundness discharge (`d := pred` in `rule_induction`) is written with.
//!
//! **PROMOTION FLAG:** this module is metalogic-shaped but ACL2-homed —
//! `metalogic/` is outside the current edit area. When it is promoted to
//! `metalogic/`, `peano/pa.rs` and `metalogic/toy.rs` should migrate onto
//! it (tracked in this directory's `SKELETONS.md`).

use covalence_core::{Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::eq::beta_nf;
use crate::init::ext::TermExt;
use crate::metalogic::{RuleSet, derive_via_closed, nth_conjunct};

/// A premise fed to [`derive_mixed`]: either a *side* condition already
/// proved outright (discharged by direct `imp_elim`), or a
/// *sub-derivation* `⊢ Derivable_L ⌜A⌝` (opened to `d ⌜A⌝` under the
/// assumed `Closed_L d` first). The unary mirror of
/// [`crate::metalogic::binary::Premise`].
pub enum Premise {
    /// A side antecedent proved outside the derivability predicate.
    Side(Thm),
    /// A sub-derivation `⊢ Derivable_L ⌜A⌝`.
    Derivation(Thm),
}

/// **Apply clause `clause_idx`** of a unary rule set: peel its `∀`s with
/// `args` (in the clause's quantifier order, outermost first), then
/// discharge its antecedents with `premises` in order, yielding
/// `⊢ Derivable_L ⌜A⌝` for the clause's conclusion instance.
///
/// The unary twin of [`crate::metalogic::binary::derive_mixed`]: a
/// [`Premise::Side`] is a plain `imp_elim`; a [`Premise::Derivation`] is
/// opened to `d ⌜Aⱼ⌝` under the assumed `Closed_L d` (via
/// `all_elim(d) . imp_elim`) first. The kernel re-checks every step — a
/// wrong index / argument / premise fails, it never fabricates a
/// derivation.
pub fn derive_mixed(
    rs: &RuleSet,
    clause_idx: usize,
    n_clauses: usize,
    args: &[Term],
    premises: Vec<Premise>,
) -> Result<Thm> {
    derive_via_closed(rs, |assumed, _d_apply| {
        let mut clause = nth_conjunct(assumed.clone(), clause_idx, n_clauses)?;
        for x in args {
            clause = clause.all_elim(x.clone())?;
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

/// The full β-bridge for a predicate application: `⊢ d_pred ⌜enc⌝ = nf`
/// (one `beta_conv` for the head redex, then strong β-normalisation)
/// together with the normal form `nf`. The clause-discharge workhorse —
/// `pa.rs`'s per-clause `br` closure, packaged once.
pub fn br(d_pred: &Term, enc: Term) -> Result<(Thm, Term)> {
    let beta = Thm::beta_conv(d_pred.clone().apply(enc)?)?; // ⊢ d_pred ⌜enc⌝ = body
    let denoted = beta
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?
        .1
        .clone();
    let to_nf = beta_nf(denoted); // ⊢ body = nf
    let nf = to_nf
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?
        .1
        .clone();
    Ok((beta.trans(to_nf)?, nf))
}

/// Bridge `Γ ⊢ p` to `Γ ⊢ p'` when `p` and `p'` have the same β-normal
/// form (`pa.rs::bridge_eq`, verbatim but public).
pub fn bridge_eq(thm: Thm, target: &Term) -> Result<Thm> {
    if thm.concl() == target {
        return Ok(thm);
    }
    let from_nf = beta_nf(thm.concl().clone()); // ⊢ p  = nf
    let to_nf = beta_nf(target.clone()); // ⊢ p' = nf
    let eq = from_nf.trans(to_nf.sym()?)?; // ⊢ p = p'
    eq.eq_mp(thm)
}

/// Given a proved fact `⊢ φ` whose statement β-normalises to the
/// denotation of `d_pred` at `enc`, produce the *applied* form
/// `⊢ d_pred ⌜enc⌝` (the shape a closure clause wants at `d := d_pred`).
/// `pa.rs::expand_to_pred` generalized through [`br`]/[`bridge_eq`].
pub fn expand_to_pred(fact: Thm, enc: &Term, d_pred: &Term) -> Result<Thm> {
    let (bridge, nf) = br(d_pred, enc.clone())?; // ⊢ d_pred ⌜enc⌝ = nf
    let bridged = bridge_eq(fact, &nf)?; // ⊢ nf
    bridge.sym()?.eq_mp(bridged)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic::derivable;
    use covalence_core::Type;
    use covalence_hol_eval::mk_nat;

    /// A tiny unary logic over `nat` exercising every [`derive_mixed`]
    /// path (mirrors `metalogic::binary`'s toy):
    ///   clause 0 (axiom):           d 0
    ///   clause 1 (derivation prem): ∀n. d n ⟹ d (succ n)
    ///   clause 2 (side prem):       ∀n. (n = n) ⟹ d n
    fn toy_rule_set() -> RuleSet<'static> {
        RuleSet::new(Type::nat(), |d_apply| {
            let zero = mk_nat(0u32);
            let c0 = d_apply(&zero)?;
            let n = Term::free("n", Type::nat());
            let succ_n = crate::init::nat::succ(n.clone());
            let c1 = d_apply(&n)?
                .imp(d_apply(&succ_n)?)?
                .forall("n", Type::nat())?;
            let c2 = n
                .clone()
                .equals(n.clone())?
                .imp(d_apply(&n)?)?
                .forall("n", Type::nat())?;
            Ok(vec![c0, c1, c2])
        })
    }

    #[test]
    fn derive_mixed_axiom_derivation_and_side() {
        let rs = toy_rule_set();
        let n = rs.n_clauses().unwrap();
        assert_eq!(n, 3);
        let zero = mk_nat(0u32);
        let one = crate::init::nat::succ(zero.clone());

        // Axiom clause: ⊢ Derivable 0.
        let base = derive_mixed(&rs, 0, n, &[], vec![]).unwrap();
        assert!(base.hyps().is_empty());
        assert_eq!(base.concl(), &derivable(&rs, &zero).unwrap());

        // Derivation premise: ⊢ Derivable (succ 0).
        let step = derive_mixed(
            &rs,
            1,
            n,
            std::slice::from_ref(&zero),
            vec![Premise::Derivation(base)],
        )
        .unwrap();
        assert!(step.hyps().is_empty());
        assert_eq!(step.concl(), &derivable(&rs, &one).unwrap());

        // Side premise: ⊢ Derivable (succ 0) again, via ⊢ succ 0 = succ 0.
        let side = Thm::refl(one.clone()).unwrap();
        let via_side = derive_mixed(
            &rs,
            2,
            n,
            std::slice::from_ref(&one),
            vec![Premise::Side(side)],
        )
        .unwrap();
        assert!(via_side.hyps().is_empty());
        assert_eq!(via_side.concl(), &derivable(&rs, &one).unwrap());
    }

    /// β-bridge round trip: `⊢ 0 = 0` ↔ `⊢ (λn. n = n) 0`.
    #[test]
    fn beta_bridges_round_trip() {
        let zero = mk_nat(0u32);
        // pred := λn:nat. n = n.
        let pred = {
            let n = Term::free("__n", Type::nat());
            let body = n.clone().equals(n).unwrap();
            Term::abs(Type::nat(), covalence_core::subst::close(&body, "__n"))
        };
        let fact = Thm::refl(zero.clone()).unwrap(); // ⊢ 0 = 0

        let (bridge, nf) = br(&pred, zero.clone()).unwrap();
        assert!(bridge.hyps().is_empty());
        assert_eq!(&nf, fact.concl());

        let applied = expand_to_pred(fact, &zero, &pred).unwrap(); // ⊢ (λn. n=n) 0
        assert!(applied.hyps().is_empty());
        assert_eq!(applied.concl(), &pred.clone().apply(zero).unwrap());

        // bridge_eq lands the applied form back on the normal form.
        let back = bridge_eq(applied, &nf).unwrap();
        assert!(back.hyps().is_empty());
        assert_eq!(back.concl(), &nf);
    }
}
