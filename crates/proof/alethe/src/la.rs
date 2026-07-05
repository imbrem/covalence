//! Linear integer arithmetic (LIA) rule checkers — the `la_generic`
//! **Farkas** certificate, re-derived through the kernel's `int` ordered
//! ring (never trusted).
//!
//! ## What `la_generic` is
//!
//! In Alethe, `la_generic` emits a *tautology clause*
//! `(cl (not l₁) … (not lₙ))` annotated with nonnegative rational
//! coefficients `c₁ … cₙ` in `:args`. It certifies that the conjunction
//! `l₁ ∧ … ∧ lₙ` of the asserted arithmetic literals is contradictory:
//! the nonnegative linear combination `Σ cᵢ · lᵢ` (each `lᵢ` read as
//! `tᵢ ⋈ 0`) sums to a manifestly-false inequality (`0 < 0`, `0 ≤ -1`).
//! Resolution against the assumed `lᵢ` then closes the branch — exactly
//! like the propositional tautology rules already in [`crate::hol`].
//!
//! So checking `la_generic` = (1) re-derive the sequent
//! `{l₁, …, lₙ} ⊢ F` in the kernel from the `int` order theory, then
//! (2) clausify it with [`logic::clause_intro`] into `⊢ ¬l₁ ∨ … ∨ ¬lₙ`.
//! Step (2) is shared, generic plumbing; step (1) is the arithmetic core.
//!
//! ## What this checker covers
//!
//! The **unit-coefficient, all-strict transitivity-cycle** case: `n ≥ 2`
//! literals `t₁ < t₂, t₂ < t₃, …, tₙ < t₁` (in any order / rotation) that
//! chain — via [`int::lt_trans`] — into `x < x`, contradicted by
//! [`int::lt_irrefl`]. The two-literal case (`a < b ∧ b < a`) is the
//! `n = 2` instance. `>`/`>=` are normalised to `<`/`<=` upstream in
//! [`crate::hol`], so we only see `int.lt` / `int.le` here.
//!
//! Still **`NotImplemented`** (see `SKELETONS.md`): non-unit / rational
//! coefficients (needs [`int::lt_mul_pos`] to scale a strict literal and
//! `int::lt_add_mono` to add inequalities), non-strict (`≤`) literals and
//! le/lt mixing (needs [`int::le_def`] + `lt_trichotomy`), and the general
//! *scale-each-literal-by-its-coefficient-and-sum* combination that does
//! not reduce to a transitivity cycle.

use covalence_core::Term;
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_init::init::{int, logic};

use crate::error::BridgeError;

type R<T> = Result<T, BridgeError>;

/// `la_generic`: check a Farkas tautology clause `(cl (not l₁) … (not lₙ))`.
///
/// `lits` are the *stated clause literals* (the `(not lᵢ)`); `args` are
/// the coefficients (the cycle case fixes them at unit, so non-unit
/// coefficients are rejected). Returns `⊢ ¬l₁ ∨ … ∨ ¬lₙ`, derived by
/// refuting `{l₁, …, lₙ}` in the kernel and clausifying.
pub fn la_generic(lits: &[Term], args: &[covalence_sexp::SExpr]) -> R<Thm> {
    // Recover the asserted literals lᵢ by stripping the clause's `(not ·)`.
    let atoms: Vec<Term> = lits
        .iter()
        .map(|l| {
            dest_not(l).ok_or_else(|| BridgeError::BadStep {
                rule: "la_generic".into(),
                detail: format!("clause literal `{l}` is not a negation"),
            })
        })
        .collect::<R<_>>()?;

    if atoms.len() < 2 {
        return Err(BridgeError::NotImplemented(format!(
            "la_generic with {} literal(s) (need ≥ 2 for a refutation)",
            atoms.len()
        )));
    }

    // The cycle checker is sound only for unit coefficients. If `:args`
    // carries coefficients, require they are all `1` (the genuine
    // scale-and-sum for non-unit coefficients is not yet wired).
    if !args.is_empty() && !all_unit_coeffs(args) {
        return Err(BridgeError::NotImplemented(
            "la_generic with non-unit coefficients (only the unit-coefficient \
             strict transitivity-cycle case is wired)"
                .into(),
        ));
    }

    // Every literal must be a strict `int.lt`. (Non-strict `≤` mixing is
    // deferred — see SKELETONS.md.)
    let edges: Vec<(Term, Term)> = atoms
        .iter()
        .map(|a| {
            dest_lt(a).ok_or_else(|| {
                BridgeError::NotImplemented(format!(
                    "la_generic: literal `{a}` is not a strict `int.lt` \
                     (le/lt mixing not yet wired)"
                ))
            })
        })
        .collect::<R<_>>()?;

    let refutation = farkas_strict_cycle(&atoms, &edges)?; // {l₁, …, lₙ} ⊢ F
    clausify(refutation, &atoms)
}

/// Turn `{l₁, …, lₙ} ⊢ F` into `⊢ ¬l₁ ∨ … ∨ ¬lₙ` by discharging the last
/// literal as the clause tail then clausifying the rest. (Discharging the
/// final literal directly avoids the spurious trailing `∨ F` that
/// clausifying an `F`-conclusion would leave.)
fn clausify(refutation: Thm, atoms: &[Term]) -> R<Thm> {
    let (last, init) = atoms.split_last().expect("≥ 2 literals checked by caller");
    let seq = refutation.imp_intro(last)?.not_intro()?; // {l₁, …, lₙ₋₁} ⊢ ¬lₙ
    logic::clause_intro(seq, init).map_err(Into::into)
}

/// The unit-coefficient, all-strict Farkas core: from `n` strict
/// inequalities that form a cycle, derive `{l₁, …, lₙ} ⊢ F`.
///
/// `edges[i] = (aᵢ, bᵢ)` is `atoms[i] = (aᵢ < bᵢ)`. We walk the cycle
/// starting at edge 0 (`a₀ < b₀`), repeatedly finding the unique unused
/// edge whose source equals the current chain head's target, chaining via
/// [`int::lt_trans`]. A valid unit-coefficient strict refutation makes the
/// walk return to `a₀` after consuming **every** edge — yielding `a₀ < a₀`,
/// contradicted by [`int::lt_irrefl`].
fn farkas_strict_cycle(atoms: &[Term], edges: &[(Term, Term)]) -> R<Thm> {
    let n = edges.len();
    let mut used = vec![false; n];

    // Start the chain at edge 0.
    used[0] = true;
    let (start, mut tip) = (edges[0].0.clone(), edges[0].1.clone());
    // The running theorem: `{…} ⊢ start < tip`.
    let mut chain = Thm::assume(atoms[0].clone())?;

    for _ in 1..n {
        // Find the unused edge whose source == current tip.
        let next = (0..n).find(|&j| !used[j] && edges[j].0 == tip);
        let Some(j) = next else {
            return Err(BridgeError::NotImplemented(format!(
                "la_generic: literals do not form a single strict cycle \
                 (no edge continues from `{tip}`; general scale-and-sum \
                 Farkas not yet wired)"
            )));
        };
        used[j] = true;
        let tj = edges[j].1.clone();
        // `start < tip` and `tip(=edges[j].0) < tj`  ⟹  `start < tj`.
        let next_thm = Thm::assume(atoms[j].clone())?;
        chain = int::lt_trans()
            .all_elim(start.clone())?
            .all_elim(tip.clone())?
            .all_elim(tj.clone())?
            .imp_elim(chain)?
            .imp_elim(next_thm)?; // {…} ⊢ start < tj
        tip = tj;
    }

    // The cycle must close: the final tip is the start.
    if tip != start {
        return Err(BridgeError::NotImplemented(format!(
            "la_generic: strict chain `{start} < … < {tip}` does not close \
             the cycle (general scale-and-sum Farkas not yet wired)"
        )));
    }

    // `{…} ⊢ start < start`, contradicted by `⊢ ¬(start < start)`.
    let not_refl = int::lt_irrefl().all_elim(start.clone())?; // ⊢ ¬(start < start)
    not_refl.not_elim(chain).map_err(Into::into) // {l₁, …, lₙ} ⊢ F
}

/// Are all `:args` coefficients the literal `1`? (cvc5 emits Farkas
/// coefficients as bare numerals; a unit cycle has every coefficient `1`.)
fn all_unit_coeffs(args: &[covalence_sexp::SExpr]) -> bool {
    args.iter()
        .all(|a| a.as_symbol() == Some("1") || coeff_is_one(a))
}

/// Recognise `1`, `(/ 1 1)`, or `1.0` style unit coefficients.
fn coeff_is_one(a: &covalence_sexp::SExpr) -> bool {
    match a.as_symbol() {
        Some(s) => s == "1" || s == "1.0",
        None => false,
    }
}

/// `App(¬, p)` → `p`, if `t` is a HOL negation.
fn dest_not(t: &Term) -> Option<Term> {
    let (head, p) = t.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&covalence_hol_eval::defs::not_spec())
        .then(|| p.clone())
}

/// `int.lt a b` → `(a, b)`. `defs::int_lt()` is the bare curried spec
/// constant (the same head `crate::hol` applies to build a `<` term).
fn dest_lt(t: &Term) -> Option<(Term, Term)> {
    let (f, b) = t.as_app()?;
    let (head, a) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    let lt = covalence_hol_eval::defs::int_lt();
    let (lt_spec, _) = lt.as_spec()?;
    spec.ptr_eq(lt_spec).then(|| (a.clone(), b.clone()))
}
