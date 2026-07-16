//! **The generic `Derivable_L` engine** — the reusable impredicative
//! rule-induction substrate that [`crate::init::prop`]'s `Derivable_Prop` and
//! [`crate::peano::pa`]'s `Derivable_PA` are two instances of
//! (`notes/vibes/theories-models-and-logics.md §5.5/§5.6`, the Phase-A3 boundary).
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

use std::cell::OnceCell;

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::TermExt;

pub mod toy;

// **The binary twin of this engine** (`d n w` over `(nt_ty, word_ty)` rather
// than a single reified formula `d ⌜A⌝`) — the substrate for the CFG stratum's
// `Derives_E n w` judgement (`crate::grammar::cfg`), reusing `conj` /
// `nth_conjunct` / `conj_thms` here. `init::regex`'s `Matches r w` is the same
// shape hand-rolled; this packages it once.
pub mod binary;

// **Generic rule application over any [`RuleSet`]** — the forward/composition
// direction of the impredicative engine: `apply_rule(rs, k, n, floats, premises)`
// mints `⊢ Derivable_L (σ concl)` by instantiating clause `k`'s metavariables and
// discharging its essential antecedents. `derive_clause` (mm_database replay) and
// `derivable_db_mp` (the database-value world) are the two hardcoded instances
// this generalises; `mm_session` builds the high-level Metamath-database API on it.
pub mod apply;

// **MID — a term-rewrite relation on the binary engine** (the reduction analogue
// of `interp::DerivationSystem`): base rewrite clauses + generic `app`-congruence
// + `Reduces = Step*`, plus a `Matcher` trait and a fuel driver. The reusable
// layer K (`crate::k`) and SpecTec reduction instantiate. `notes/vibes/k/reduction-demo-scope.md`.
pub mod rewrite;

// The **HOL database type + relation lattice** (`notes/vibes/theories-models-and-logics.md
// §5.6`): databases as first-class HOL *values* (an axiom-selecting predicate), with
// `⊑`/monotonicity and `⟹_σ`/transport proved over `Derivable_DB`. UNIFIED (Phase A):
// `database::Derivable_DB db A` is now literally `derivable(&db_rule_set(db), A)` — a
// single impredicative derivability notion, with the database value's axioms supplied
// as this engine's `RuleSet` (`db_rule_set`). The relation theorems
// (`monotone`/`transport`) are thus theorems about *this engine's* `derivable`.
pub mod database;
pub mod relations;

// **A genuinely structural (non-identity) `σ` for `relations::transport`**
// (`notes/vibes/logics/structural-sigma-transport.md`): a variable-index
// renaming `σ_f := λA. λ v ¬ ∧ ∨ ⟹. A (λn. v (f n)) ¬ ∧ ∨ ⟹` on the reified
// `Φ⟨bool⟩` carrier, with its `⟹`-homomorphism proved for `f := succ` — the
// first discharge of transport's `σ_hom` premise off `σ = id`.
pub mod relations_sigma;

// **L3 — the reified Metamath-expression algebra** (`notes/vibes/logics/
// derivation-system-interp.md`): the `MmAlgebra` insulation trait + two impls
// (`FreeAlgebra` recursor-free `Φ=nat`; `MmExprAlgebra` genuine inductive
// `MmExpr := sym(nat) | app(Rec, Rec)` realized via `ImpredicativeBackend`).
// `structural_sigma` catamorphism + `sigma_app_hom`-by-`comp` on `MmExpr`; the
// acid-test op runs UNCHANGED on both backends (encoding-swap insulation).
pub mod mm_algebra;

// **L5 — the derivation-system interpretation mid-level API**: `DerivationSystem`
// (each system supplies `rule_set` + `algebra`) + `DerivationInterp` (σ +
// per-rule `clause_sims`, `interpret()` delegating to `transport_db::transport`).
// The K matching-logic → Metamath cross-system bridge is one (deferred) instance.
pub mod interp;

// **Generic interpretation/transport between Metamath-database logics**
// (`notes/vibes/metatheory.md`, "relate formal systems"): `transport` proves
// `Derivable_L1 ⟹ Derivable_L2 ∘ σ` ONCE via `rule_induction` (predicate
// `d := λx. Derivable_L2 (σ x)`); the caller's `clause_sims` are the per-rule
// "σ simulates this rule in the target" obligations. Worked instance:
// conservative-extension / monotonicity (`σ = id`, `T ⊇ S`) over `mm_database`
// rule sets. The long-term target is `Derivable_HOL ⟹ Derivable_ZFC ∘ σ`.
pub mod transport_db;

// **Metamath-Prop → HOL replay** (`notes/vibes/metatheory.md`): replay a *verified*
// propositional-calculus Metamath proof into a kernel-constructed
// `⊢ Derivable_Prop ⌜S⌝` theorem — the "construct, don't trust" bridge landing in
// *pure derivability over the encoded syntax* (NO denotation, NO oracle).
pub mod mm_replay;

// **General schema-database Metamath replay** (`notes/vibes/metatheory.md`): generalise
// `mm_replay` from the fixed prop-calc rule set to an *arbitrary*
// `metamath::Database` — build a data-driven `RuleSet` from the database's
// assertions (an uninterpreted free term algebra over `nat`; substitution =
// `all_elim`) and replay a verified normal proof into `⊢ Derivable_L ⌜S⌝`. One
// function replays many logics. "A Metamath database IS a logic."
pub mod mm_database;

// **Import a whole Metamath database INTO covalence-hol** (`notes/vibes/metatheory.md`):
// the high-level API over `mm_database::replay_db` — `import_theorems(db)` /
// `read_and_import(source)` re-derive `⊢ Derivable_L ⌜S⌝` for *every* `$p`
// theorem from its (possibly compressed) proof. Tested on the real, vendored
// `hol.mm` (all-compressed) and (ignored, env-gated) a `set.mm` sample.
pub mod mm_import;

// **A HOL-backed `DatabaseSink`**: construct `⊢ Derivable_Prop ⌜S⌝` *while
// reading* a `.mm` source (the reader drives the builder trait; this backend
// replays each `$p` through the kernel as it is read). The in-memory `Database`
// is the HOL-free sanity-check backend; this is the HOL one.
pub mod mm_sink;

// **Composing derivability theorems from outside Metamath.** A session API over
// `Derivable_DB db` that applies the database's rules (axiom introduction,
// modus ponens) in the HOL kernel to assemble `⊢ Derivable_DB db ⌜S⌝` theorems
// — including for statements `S` with no Metamath proof in the database.
pub mod mm_compose;

// **A high-level session over a real imported Metamath database.** `MmSession`
// wraps a `metamath::Database`: `theorem(label)` re-derives `⊢ Derivable_L ⌜S⌝`
// for a stored `$p` (via `replay_db`); `apply(rule, floats, premises)` composes
// *new* `⊢ Derivable_L (σ concl)` theorems from ANY of the database's `|-` rules
// (via the generic `apply_rule`) — including statements the database has no `$p`
// proof for. All results share one full-database `Derivable_L` head, so they
// compose. Sound: every theorem is a `replay_db` result or an `apply_rule` build.
pub mod mm_session;

// Re-exported WITHOUT `database::derivable` (a 0-ary schema builder) to avoid
// colliding with this engine's `derivable`; reach it as `metalogic::database::derivable`.
pub use apply::{apply_rule, derive_axiom_instance};
pub use database::{derivable_db, extends, monotone};
pub use mm_compose::DbSession;
pub use mm_session::MmSession;
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
    // An alias would force a `'static` object-lifetime default on the inner
    // `&dyn Fn`; the higher-order shape is the point here.
    #[allow(clippy::type_complexity)]
    pub clauses: Box<dyn Fn(&dyn Fn(&Term) -> Result<Term>) -> Result<Vec<Term>> + 'a>,
    /// The memoized bound-`d` layout (see [`Layout`]). **Caching only** — the
    /// clause closure is pure and the bound `d` is fixed, so laying the clauses
    /// out once per rule set is observationally identical to laying them out
    /// per call (terms are `Arc`-shared). Assumes `phi`/`clauses` are not
    /// mutated after the first layout (nothing in-tree does).
    layout: OnceCell<Layout>,
}

/// The memoized bound-`d` artifacts every statement/derivation over a
/// [`RuleSet`] reuses: the laid-out clauses, their conjunction `Closed_L d`
/// (the `Derivable_L` statement prefix), and the assumed
/// `{Closed_L d} ⊢ Closed_L d` each derivation opens with. All three are
/// deterministic per rule set and were previously rebuilt (and re-type-checked)
/// on **every** operation — O(spec) per derive; with the cache, repeat derives
/// are O(clause).
struct Layout {
    /// The clauses at the bound `d`, in fold order.
    clauses: Vec<Term>,
    /// `Closed_L d` — their right-nested conjunction.
    closed: Term,
    /// `{Closed_L d} ⊢ Closed_L d` (`Thm::assume`, kernel-checked once).
    assumed: Thm,
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
            layout: OnceCell::new(),
        }
    }

    /// The memoized bound-`d` layout, computed on first use.
    fn layout(&self) -> Result<&Layout> {
        if self.layout.get().is_none() {
            let d = self.d_var();
            let clauses = (self.clauses)(&|f| d.clone().apply(f.clone()))?;
            let closed = conj(clauses.clone())?;
            let assumed = Thm::assume(closed.clone())?;
            // `OnceCell` is `!Sync`, so the only way `set` can fail is a
            // re-entrant `clauses` closure — which would have computed the
            // identical value; either copy is fine to keep.
            let _ = self.layout.set(Layout {
                clauses,
                closed,
                assumed,
            });
        }
        Ok(self.layout.get().expect("layout just initialised"))
    }

    /// `Φ → bool` — the type of the impredicative predicate variable `d`.
    pub fn pred_ty(&self) -> Type {
        Type::fun(self.phi.clone(), Type::bool())
    }

    /// The predicate variable `d : Φ → bool`.
    pub fn d_var(&self) -> Term {
        Term::free("d", self.pred_ty())
    }

    /// The number of closure clauses (memoized via the bound-`d` layout).
    pub fn n_clauses(&self) -> Result<usize> {
        Ok(self.layout()?.clauses.len())
    }
}

// ============================================================================
// `Closed_L` and `Derivable_L`
// ============================================================================

/// Right-nest a list of clauses into a single conjunction
/// `c₀ ∧ (c₁ ∧ (… ∧ c_{n-1}))`. The **empty** conjunction is `T` (the unit of
/// `∧`), so a *rule set with no clauses* is well-formed: its `Closed_L d` is `T`
/// and `Derivable_L A := ∀d. T ⟹ d A`. That is exactly what a proof-scoped rule
/// set needs when a theorem is derivable from its hypotheses alone (it references
/// no rule), e.g. `H ⊢ H`.
pub fn conj(clauses: Vec<Term>) -> Result<Term> {
    let mut iter = clauses.into_iter().rev();
    let Some(mut acc) = iter.next() else {
        return Ok(covalence_hol_eval::mk_bool(true));
    };
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

/// `Closed_L d` for the bound predicate variable `d` (memoized — the
/// `Arc`-shared cached term, not a fresh layout).
pub fn closed_for_var(rs: &RuleSet) -> Result<Term> {
    Ok(rs.layout()?.closed.clone())
}

/// `Derivable_L A := ∀d. Closed_L d ⟹ d A` — the impredicative derivability
/// predicate over an encoded formula `A : Φ`. The `Closed_L d` prefix is
/// memoized, so repeat statements share one `Arc`-shared prefix term.
pub fn derivable(rs: &RuleSet, a: &Term) -> Result<Term> {
    let d = rs.d_var();
    let closed_d = closed_for_var(rs)?;
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
    if k + 1 < n { thm.and_elim_l() } else { Ok(thm) }
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
    let layout = rs.layout()?; // memoized `Closed d` + `{Closed d} ⊢ Closed d`
    let d_apply = |f: &Term| d.clone().apply(f.clone());
    let d_a = build_d_a(&layout.assumed, &d_apply)?; // {Closed d, …} ⊢ d ⌜A⌝
    d_a.imp_intro(&layout.closed)?.all_intro("d", rs.pred_ty())
}

// ============================================================================
// Mixed-premise clause application — the unary twin of `binary::derive_mixed`
// ============================================================================

/// A premise fed to [`derive_mixed`]: either a **side** antecedent already
/// proved outright (an arbitrary `bool` proposition the clause carries — e.g. a
/// computable side condition discharged by
/// [`TermExt::prove_true`](crate::init::ext::TermExt::prove_true)), or a
/// **sub-derivation** `⊢ Derivable_L ⌜p⌝` (opened under the assumed
/// `Closed_L d` first). The unary twin of [`binary::Premise`].
pub enum Premise {
    /// A side antecedent proved outside the derivability predicate.
    Side(Thm),
    /// A sub-derivation `⊢ Derivable_L ⌜p⌝`.
    Derivation(Thm),
}

/// **Apply clause `clause_idx`** of a rule set: peel its metavariable `∀`s with
/// `args` (in the clause's quantifier order), then discharge its antecedents
/// with `premises` in clause-antecedent order (one `imp_elim` per premise — the
/// [`clause_of`](crate::wasm::relation) chained shape, *not* a conjunction),
/// yielding `⊢ Derivable_L ⌜concl[args]⌝`.
///
/// The mixed-premise generalisation of [`crate::wasm::relation::derive`] and
/// unary twin of [`binary::derive_mixed`]: a [`Premise::Side`] is a plain
/// `imp_elim` — the kernel enforces that the theorem's conclusion is
/// *syntactically* the instantiated antecedent, so nothing can be fabricated; a
/// [`Premise::Derivation`] is opened to `d ⌜p⌝` under the assumed `Closed_L d`
/// (via `all_elim(d) . imp_elim`) first, exactly the relation-engine move.
pub fn derive_mixed(
    rs: &RuleSet,
    clause_idx: usize,
    n_clauses: usize,
    args: &[Term],
    premises: Vec<Premise>,
) -> Result<Thm> {
    derive_via_closed(rs, |assumed, _d_apply| {
        let mut clause = nth_conjunct(assumed.clone(), clause_idx, n_clauses)?;
        for a in args {
            clause = clause.all_elim(a.clone())?;
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
    let pred_a = assumed.all_elim(pred.clone())?.imp_elim(closed_pred_thm)?; // {Der A} ⊢ pred A

    pred_a.imp_intro(deriv_a)?.all_intro(a_name, a_ty)
}

/// Conjoin a non-empty list of theorems right-nested: from `⊢ c₀ … ⊢ c_{n-1}`,
/// build `⊢ c₀ ∧ (c₁ ∧ (… ∧ c_{n-1}))`.
pub fn conj_thms(thms: Vec<Thm>) -> Result<Thm> {
    let mut iter = thms.into_iter().rev();
    let mut acc = iter.next().ok_or_else(|| {
        covalence_core::Error::ConnectiveRule("metalogic: no clause proofs".into())
    })?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::nat;
    use covalence_hol_eval::mk_nat;

    /// A toy **mixed** rule set over the real carrier `Φ = nat` (mirroring the
    /// binary engine's `derive_aabb_by_hand` precedent on the unary side):
    ///
    /// ```text
    ///   clause 0 (axiom):          d 0
    ///   clause 1 (mixed):  ∀n. n < 5  ⟹  d n  ⟹  d (n + 1)
    /// ```
    ///
    /// The `n < 5` antecedent is a *real HOL `bool` proposition* (not a
    /// `d`-application) — the side-condition shape SpecTec `if` premises lower
    /// to — discharged by kernel computation ([`TermExt::prove_true`]).
    fn mixed_rule_set() -> RuleSet<'static> {
        RuleSet::new(Type::nat(), |d_apply| {
            let c0 = d_apply(&mk_nat(0u32))?;
            let n = Term::free("n", Type::nat());
            let lt5 = Term::app(Term::app(nat::nat_lt(), n.clone()), mk_nat(5u32));
            let body = lt5.imp(d_apply(&n)?.imp(d_apply(&nat::add(n.clone(), mk_nat(1u32)))?)?)?;
            Ok(vec![c0, body.forall("n", Type::nat())?])
        })
    }

    /// End-to-end mixed derivation, hypothesis-free: axiom `d 0`, then the
    /// mixed clause at `n := 0` with its side condition `0 < 5` proved by
    /// computation and its recursive premise discharged by the axiom.
    #[test]
    fn derive_mixed_side_and_derivation() {
        let rs = mixed_rule_set();
        let n_cl = rs.n_clauses().unwrap();
        assert_eq!(n_cl, 2);
        let zero = mk_nat(0u32);

        // ⊢ Derivable ⌜0⌝  (the axiom clause).
        let base = derive_mixed(&rs, 0, n_cl, &[], vec![]).unwrap();
        assert!(base.hyps().is_empty());
        assert_eq!(base.concl(), &derivable(&rs, &zero).unwrap());

        // ⊢ 0 < 5 by computation — the side-condition discharge.
        let side = Term::app(Term::app(nat::nat_lt(), zero.clone()), mk_nat(5u32))
            .prove_true()
            .unwrap();

        // ⊢ Derivable ⌜0 + 1⌝ via the mixed clause.
        let step = derive_mixed(
            &rs,
            1,
            n_cl,
            &[zero.clone()],
            vec![Premise::Side(side), Premise::Derivation(base.clone())],
        )
        .unwrap();
        assert!(
            step.hyps().is_empty(),
            "mixed derivation is hypothesis-free"
        );
        let concl = derivable(&rs, &nat::add(zero.clone(), mk_nat(1u32))).unwrap();
        assert_eq!(step.concl(), &concl);

        // Gating, not fabricating: a side theorem that is NOT the instantiated
        // antecedent (⊢ 1 < 5 instead of ⊢ 0 < 5) fails to compose.
        let wrong = Term::app(Term::app(nat::nat_lt(), mk_nat(1u32)), mk_nat(5u32))
            .prove_true()
            .unwrap();
        assert!(
            derive_mixed(
                &rs,
                1,
                n_cl,
                &[zero],
                vec![Premise::Side(wrong), Premise::Derivation(base)],
            )
            .is_err()
        );
    }

    /// The memoized layout: repeat statements/derivations are consistent (the
    /// cached `Closed_L d` prefix produces the same terms/theorems as a fresh
    /// layout does — structural equality all the way down).
    #[test]
    fn layout_memoization_is_consistent() {
        let rs = mixed_rule_set();
        let n_cl = rs.n_clauses().unwrap();
        let zero = mk_nat(0u32);

        // A fresh (uncached) layout for cross-checking.
        let fresh = mixed_rule_set();
        assert_eq!(
            closed_for_var(&rs).unwrap(),
            closed_for_var(&fresh).unwrap()
        );
        assert_eq!(
            derivable(&rs, &zero).unwrap(),
            derivable(&fresh, &zero).unwrap()
        );

        // Deriving twice through the same (now cached) rule set agrees, and
        // agrees with a derivation over the fresh rule set.
        let d1 = derive_mixed(&rs, 0, n_cl, &[], vec![]).unwrap();
        let d2 = derive_mixed(&rs, 0, n_cl, &[], vec![]).unwrap();
        let d3 = derive_mixed(&fresh, 0, n_cl, &[], vec![]).unwrap();
        assert_eq!(d1.concl(), d2.concl());
        assert_eq!(d1.concl(), d3.concl());
        assert!(d1.hyps().is_empty() && d2.hyps().is_empty() && d3.hyps().is_empty());
    }
}
