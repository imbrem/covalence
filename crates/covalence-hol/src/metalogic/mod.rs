//! **The generic `Derivable_L` engine** — the reusable impredicative
//! rule-induction substrate that [`crate::init::prop`]'s `Derivable_Prop` and
//! [`crate::peano::pa`]'s `Derivable_PA` are two instances of
//! (`docs/theories-models-and-logics.md §5.5/§5.6`, the Phase-A3 boundary).
//!
//! ## What a "logic" is here
//!
//! A **logic `L`** is a *rule set* over a **reified syntax carrier** `Φ` — the
//! HOL type of an encoded formula (e.g. `init::prop`'s `Φ⟨'r⟩` or `peano`'s
//! two-sorted `Φ_sem⟨'t,'r⟩`). The rule set is, abstractly, a list of
//! **closure clauses** — each a `bool`-typed body over a predicate variable
//! `d : Φ → bool`:
//!
//! - an **axiom** is a premise-free clause `d ⌜A⌝` (possibly `∀`-closed over
//!   schematic formula variables);
//! - an **inference rule** is a clause `∀…. premises ⟹ d ⌜concl⌝` whose
//!   premises are themselves `d`-of-formulas.
//!
//! The engine never inspects *what* a clause says — only that the same closure
//! that builds the clauses for a bound `d` also builds them for `d := pred`.
//! That single contract is what makes rule induction one move.
//!
//! ## The impredicative predicate (the heart)
//!
//! Derivability of `A` is the impredicative "smallest predicate closed under
//! the rules":
//!
//! ```text
//!   Derivable_L A  :=  ∀d:Φ→bool. Closed_L d ⟹ d A
//! ```
//!
//! where `Closed_L d` is the right-nested conjunction of the clauses. A
//! **derivation is a value `⊢ Derivable_L ⌜A⌝`** — *pure syntactic data*, it
//! carries no target `Thm`. This module packages the three reusable pieces:
//!
//! 1. [`derivable`] / [`closed_conj`] — build `Derivable_L A` and `Closed_L d`
//!    from a [`RuleSet`];
//! 2. [`rule_induction`] — the generic `inst d := pred` + `Closed_L pred`
//!    discharge recipe (`init::prop::prop_induction` and PA's soundness used
//!    this by hand — now once, generically);
//! 3. [`project`] — one-step projection of a finished derivation given a
//!    soundness theorem `⊢ Derivable_L A ⟹ ⟦A⟧` (a transport instance).
//!
//! ## Genericity
//!
//! A `RuleSet` is just `{ phi, clauses }` — the carrier type plus a way to lay
//! out the clauses for any `d`. [`init::prop`](crate::init::prop) and
//! [`peano::pa`](crate::peano::pa) each present their rule set this way (PA's
//! two-sortedness is entirely inside its carrier, invisible here), and the
//! [`toy`] sub-module is a from-scratch minimal logic that exercises the engine
//! end-to-end (axiom + one rule + soundness + projection). Nothing here is
//! added to `covalence-core`: every move is an existing kernel primitive.

use covalence_core::{Result, Term, Thm, Type};

use crate::init::ext::TermExt;

pub mod toy;

// The **HOL database type + relation lattice** (`docs/theories-models-and-logics.md
// §5.6`): databases as first-class HOL *values* (an axiom-selecting predicate), with
// `⊑`/monotonicity and `⟹_σ`/transport proved over `Derivable_DB`. NOTE: `database`'s
// `Derivable_DB db A := ∀d. Closed_DB db d ⟹ d A` is a *second* impredicative
// derivability notion alongside this engine's `RuleSet`-parameterized `derivable` —
// the database is a HOL value (vs a Rust `RuleSet` closure). Unifying the two (drive
// the engine off a HOL `Database` value) is the reconciliation tracked in SKELETONS.md.
pub mod database;
pub mod relations;

// Re-exported WITHOUT `database::derivable` (a 0-ary schema builder) to avoid
// colliding with this engine's `derivable`; reach it as `metalogic::database::derivable`.
pub use database::{derivable_db, extends, monotone};
pub use relations::{derivable_db_mp, interp, sigma_hom, transport};

// ============================================================================
// The rule-set description
// ============================================================================

/// A **rule set** over a reified syntax carrier — the data defining a logic
/// `L`'s derivability. The engine is generic over it.
///
/// `clauses(d_apply)` must build the closure clauses (in a fixed order), each
/// a `bool`-typed term, using `d_apply` for every `d ⌜·⌝` occurrence. The same
/// closure is called with the bound predicate variable `d` (to *state*
/// `Derivable_L`) and with `d := pred` (to *discharge* it in [`rule_induction`]
/// / soundness), so the two are clause-for-clause identical by construction.
pub struct RuleSet<'a> {
    /// The reified-formula carrier type `Φ` (the domain of the predicate `d`).
    pub phi: Type,
    /// Build the closure clauses for a given `d ⌜·⌝` application builder.
    /// Returns them in fold order; the engine right-nests them into `Closed_L`.
    pub clauses: Box<dyn Fn(&dyn Fn(&Term) -> Result<Term>) -> Result<Vec<Term>> + 'a>,
}

impl<'a> RuleSet<'a> {
    /// Construct a rule set from a carrier type and a clause builder.
    pub fn new(
        phi: Type,
        clauses: impl Fn(&dyn Fn(&Term) -> Result<Term>) -> Result<Vec<Term>> + 'a,
    ) -> Self {
        RuleSet {
            phi,
            clauses: Box::new(clauses),
        }
    }

    /// `Φ → bool` — the type of the impredicative predicate variable `d`.
    pub fn pred_ty(&self) -> Type {
        Type::fun(self.phi.clone(), Type::bool())
    }

    /// The predicate variable `d : Φ → bool`.
    pub fn d_var(&self) -> Term {
        Term::free("d", self.pred_ty())
    }

    /// The number of closure clauses (computed by laying them out for `d`).
    pub fn n_clauses(&self) -> Result<usize> {
        let d = self.d_var();
        let d_apply = |f: &Term| d.clone().apply(f.clone());
        Ok((self.clauses)(&d_apply)?.len())
    }
}

// ============================================================================
// `Closed_L` and `Derivable_L`
// ============================================================================

/// Right-nest a non-empty list of clauses into a single conjunction
/// `c₀ ∧ (c₁ ∧ (… ∧ c_{n-1}))`.
pub fn conj(clauses: Vec<Term>) -> Result<Term> {
    let mut iter = clauses.into_iter().rev();
    let mut acc = iter
        .next()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("metalogic: empty rule set".into()))?;
    for cl in iter {
        acc = cl.and(acc)?;
    }
    Ok(acc)
}

/// `Closed_L d` — the right-nested conjunction of the rule set's clauses, with
/// `d ⌜·⌝` filled by `d_apply`. Supplied as a closure so the *same* layout
/// builds `Closed_L` for the bound `d` and for `d := pred`.
pub fn closed_conj(rs: &RuleSet, d_apply: &dyn Fn(&Term) -> Result<Term>) -> Result<Term> {
    conj((rs.clauses)(d_apply)?)
}

/// `Closed_L d` for the bound predicate variable `d`.
pub fn closed_for_var(rs: &RuleSet) -> Result<Term> {
    let d = rs.d_var();
    closed_conj(rs, &|f| d.clone().apply(f.clone()))
}

/// `Derivable_L A := ∀d. Closed_L d ⟹ d A` — the impredicative derivability
/// predicate over an encoded formula `A : Φ`.
pub fn derivable(rs: &RuleSet, a: &Term) -> Result<Term> {
    let d = rs.d_var();
    let closed_d = closed_conj(rs, &|f| d.clone().apply(f.clone()))?;
    let body = closed_d.imp(d.apply(a.clone())?)?;
    body.forall("d", rs.pred_ty())
}

// ============================================================================
// Conjunct extraction
// ============================================================================

/// From a right-nested conjunction of `n` clauses, extract conjunct `k`
/// (`0`-based): peel `k` right-projections, then a left-projection (or return
/// the whole thing for the last `k`).
pub fn nth_conjunct(mut thm: Thm, k: usize, n: usize) -> Result<Thm> {
    for _ in 0..k {
        thm = thm.and_elim_r()?;
    }
    if k + 1 < n {
        thm.and_elim_l()
    } else {
        Ok(thm)
    }
}

// ============================================================================
// Derivation-constructor helper: open the impredicative definition, extract a
// clause, and re-package as a `Derivable_L` witness.
// ============================================================================

/// Build a derivation `⊢ Derivable_L ⌜A⌝` from a function that, under the
/// assumption `Closed_L d`, derives `⊢ d ⌜A⌝`.
///
/// This is the shared spine of every derivation constructor (`derive_axiom`,
/// `derive_mp`, the quantifier/induction rules): assume `Closed_L d`, run
/// `build_d_a` to obtain `{Closed_L d, …} ⊢ d ⌜A⌝`, then `imp_intro` the
/// `Closed_L d` assumption and `all_intro` the predicate variable `d`. The
/// `build_d_a` closure receives the *assumed* `Closed_L d` theorem and the
/// applier `λf. d f`.
pub fn derive_via_closed(
    rs: &RuleSet,
    build_d_a: impl FnOnce(&Thm, &dyn Fn(&Term) -> Result<Term>) -> Result<Thm>,
) -> Result<Thm> {
    let d = rs.d_var();
    let closed_t = closed_for_var(rs)?;
    let assumed = Thm::assume(closed_t.clone())?; // {Closed d} ⊢ Closed d
    let d_apply = |f: &Term| d.clone().apply(f.clone());
    let d_a = build_d_a(&assumed, &d_apply)?; // {Closed d, …} ⊢ d ⌜A⌝
    d_a.imp_intro(&closed_t)?.all_intro("d", rs.pred_ty())
}

// ============================================================================
// Generic rule induction — the `inst d := pred` recipe, packaged once
// ============================================================================

/// **Generic rule induction over `Derivable_L`.** Given a predicate
/// `pred : Φ → bool` and a proof of each closure clause *for `d := pred`* (in
/// the rule set's clause order), conclude
///
/// ```text
///   ⊢ ∀A. Derivable_L A ⟹ pred A
/// ```
///
/// This is the impredicative `inst d := pred` discharged against `Closed_L
/// pred`. The caller supplies `clause_proofs` — one theorem per clause, each
/// proving exactly the clause the rule set lays out at `d := pred` (the engine
/// conjoins them in order). The kernel re-checks every step, so a bogus clause
/// proof fails the conjunction build rather than fabricating an induction.
///
/// `a_name`/`a_ty` name the bound formula variable of the conclusion (the
/// instance the carrier wants — typically `Φ` pinned at the denotation type).
/// `deriv_a` is `Derivable_L A` already pinned at that instance (the carrier
/// often instantiates type variables before calling).
pub fn rule_induction(
    pred: &Term,
    clause_proofs: Vec<Thm>,
    deriv_a: &Term,
    a_name: &str,
    a_ty: Type,
) -> Result<Thm> {
    let closed_pred = conj(clause_proofs.iter().map(|t| t.concl().clone()).collect())?;
    let closed_pred_thm = conj_thms(clause_proofs)?;
    debug_assert_eq!(closed_pred_thm.concl(), &closed_pred);

    // Derivable_L A ⊢ Derivable_L A
    //              ⊢ ∀d. Closed d ⟹ d A
    //    (inst d := pred) Closed pred ⟹ pred A
    //     (imp_elim Closed pred)       pred A
    let assumed = Thm::assume(deriv_a.clone())?;
    let pred_a = assumed
        .all_elim(pred.clone())?
        .imp_elim(closed_pred_thm)?; // {Der A} ⊢ pred A

    pred_a.imp_intro(deriv_a)?.all_intro(a_name, a_ty)
}

/// Conjoin a non-empty list of theorems right-nested: from `⊢ c₀ … ⊢ c_{n-1}`,
/// build `⊢ c₀ ∧ (c₁ ∧ (… ∧ c_{n-1}))`.
pub fn conj_thms(thms: Vec<Thm>) -> Result<Thm> {
    let mut iter = thms.into_iter().rev();
    let mut acc = iter
        .next()
        .ok_or_else(|| covalence_core::Error::ConnectiveRule("metalogic: no clause proofs".into()))?;
    for cl in iter {
        acc = cl.and_intro(acc)?;
    }
    Ok(acc)
}

// ============================================================================
// One-step projection
// ============================================================================

/// **Project** a finished derivation to its target fact in one step, given the
/// soundness theorem `soundness : ⊢ Derivable_L ⌜A⌝ ⟹ ⟦A⟧` (already pinned at
/// the target instance) and the derivation `der : ⊢ Derivable_L ⌜A⌝` (likewise
/// pinned). This is *just* `imp_elim` — no re-derivation. An optional
/// `normalize` step (e.g. β-normalising a denotation fold) lands the result in
/// the target's ordinary form.
pub fn project(soundness: Thm, der: Thm) -> Result<Thm> {
    soundness.imp_elim(der)
}

/// [`project`] followed by β-normalising the conclusion to its normal form —
/// the common case where `⟦A⟧` is a Church-fold redex that must reduce to the
/// standard-model term.
pub fn project_normalized(soundness: Thm, der: Thm) -> Result<Thm> {
    let denoted = project(soundness, der)?;
    let to_nf = crate::init::eq::beta_nf(denoted.concl().clone());
    to_nf.eq_mp(denoted)
}
