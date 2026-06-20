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
//! ## What the prototype covers
//!
//! The **two-literal, coefficient-`(1,1)`, all-strict** Farkas case — the
//! canonical `x < 0 ∧ 0 < x ⟹ ⊥` shape (and any rotation of it). The two
//! literals must chain by transitivity: `P < Q` and `Q < P`, yielding
//! `P < P`, contradicted by [`int::lt_irrefl`]. `>`/`>=` are normalised to
//! `</<=` upstream in [`crate::hol`], so we only see `int.lt` / `int.le`
//! here.
//!
//! Everything else — `n > 2` literals, non-unit coefficients, mixed
//! strict/non-strict, the genuine *scale-and-sum* combination — is
//! reported `NotImplemented` with a precise message. See the module-level
//! roadmap in `SKELETONS.md` for the generalisation path (it needs
//! `int::lt_add_mono` / `le_add_mono` to scale-and-add, and
//! `int::lt_mul_pos` to scale a strict inequality by a positive constant —
//! both already **proved** in `init::int`).

use covalence_core::{Term, Thm};
use covalence_hol::init::{int, logic};

use crate::error::BridgeError;

type R<T> = Result<T, BridgeError>;

/// `la_generic`: check a Farkas tautology clause `(cl (not l₁) … (not lₙ))`.
///
/// `lits` are the *stated clause literals* (the `(not lᵢ)`); `_args` are
/// the rational coefficients (unused by the 2-literal strict prototype,
/// which fixes them at `1`). Returns `⊢ ¬l₁ ∨ … ∨ ¬lₙ`, derived by
/// refuting `{l₁, …, lₙ}` in the kernel and clausifying.
pub fn la_generic(lits: &[Term], _args: &[covalence_sexp::SExpr]) -> R<Thm> {
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

    let (l1, l2) = match atoms.as_slice() {
        [l1, l2] => (l1, l2),
        _ => {
            return Err(BridgeError::NotImplemented(format!(
                "la_generic with {} literals (prototype handles the 2-literal \
                 strict case)",
                atoms.len()
            )));
        }
    };

    let refutation = farkas_two_strict(l1, l2)?; // {l₁, l₂} ⊢ F
    // Turn `{l₁, l₂} ⊢ F` into `{l₁} ⊢ ¬l₂` (the last literal becomes the
    // clause tail), then clausify the remaining hypothesis: `⊢ ¬l₁ ∨ ¬l₂`.
    // (Discharging l₂ directly avoids the spurious trailing `∨ F` that
    // clausifying an `F`-conclusion would leave.)
    let seq = refutation.imp_intro(l2)?.not_intro()?; // {l₁} ⊢ ¬l₂
    logic::clause_intro(seq, std::slice::from_ref(l1)).map_err(Into::into)
}

/// The two-literal, coefficient-`(1,1)`, all-strict Farkas core: from two
/// strict inequalities that chain (`P < Q` and `Q < P`) derive
/// `{l₁, l₂} ⊢ F`.
fn farkas_two_strict(l1: &Term, l2: &Term) -> R<Thm> {
    let (a, b) = dest_lt(l1).ok_or_else(|| unsupported(l1, l2))?;
    let (c, d) = dest_lt(l2).ok_or_else(|| unsupported(l1, l2))?;

    // The combination is contradictory iff the two inequalities chain into
    // `P < P`. With coefficients (1,1) and strict literals that means
    // `b == c` and `d == a`: `a < b` and `b < a`.
    if b != c || d != a {
        return Err(BridgeError::NotImplemented(format!(
            "la_generic: literals `{l1}` and `{l2}` do not form a \
             (1,1) transitivity contradiction (need `a < b` and `b < a`; \
             general scale-and-sum Farkas not yet wired)"
        )));
    }

    // {a<b} and {b<a} ⊢ a < a, by int.lt_trans.
    let h1 = Thm::assume(l1.clone())?; // {a<b} ⊢ a < b
    let h2 = Thm::assume(l2.clone())?; // {b<a} ⊢ b < a
    let a_lt_a = int::lt_trans() // ∀a b c. a<b ⟹ b<c ⟹ a<c
        .all_elim(a.clone())?
        .all_elim(b.clone())?
        .all_elim(a.clone())?
        .imp_elim(h1)?
        .imp_elim(h2)?; // {a<b, b<a} ⊢ a < a

    // ⊢ ¬(a < a), contradict.
    let not_a_lt_a = int::lt_irrefl().all_elim(a.clone())?; // ⊢ ¬(a < a)
    not_a_lt_a.not_elim(a_lt_a).map_err(Into::into) // {a<b, b<a} ⊢ F
}

fn unsupported(l1: &Term, l2: &Term) -> BridgeError {
    BridgeError::NotImplemented(format!(
        "la_generic: literals `{l1}` / `{l2}` are not both strict `int.lt` \
         inequalities (prototype handles the strict 2-literal case)"
    ))
}

/// `App(¬, p)` → `p`, if `t` is a HOL negation.
fn dest_not(t: &Term) -> Option<Term> {
    let (head, p) = t.as_app()?;
    let (spec, _) = head.as_spec()?;
    spec.ptr_eq(&covalence_core::defs::not_spec())
        .then(|| p.clone())
}

/// `int.lt a b` → `(a, b)`. `defs::int_lt()` is the bare curried spec
/// constant (the same head `crate::hol` applies to build a `<` term).
fn dest_lt(t: &Term) -> Option<(Term, Term)> {
    let (f, b) = t.as_app()?;
    let (head, a) = f.as_app()?;
    let (spec, _) = head.as_spec()?;
    let lt = covalence_core::defs::int_lt();
    let (lt_spec, _) = lt.as_spec()?;
    spec.ptr_eq(lt_spec).then(|| (a.clone(), b.clone()))
}
