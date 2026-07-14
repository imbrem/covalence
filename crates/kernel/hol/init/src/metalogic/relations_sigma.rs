//! A **genuinely structural** (non-identity) formula translation `σ`, and its
//! `⟹`-homomorphism proof — the first instance that upgrades
//! [`super::relations::transport`] off the `σ = id` demonstration.
//!
//! ## What this closes (and what it does not)
//!
//! [`super::relations`] proves `transport` for any `⟹`-homomorphic `σ`, but
//! carried an explicit `σ_hom` hypothesis whose *only* concrete discharge was
//! the identity translation `σ := λx. x` (reflexivity through β). The
//! [`SKELETONS`](./SKELETONS.md) blocker asks for a **real structural `σ`** — a
//! constant/variable renaming that actually moves formulas — proved to satisfy
//! the same homomorphism law, so transport is demonstrated at a non-trivial
//! translation.
//!
//! This module builds exactly that on the **live transport carrier**
//! `Φ⟨bool⟩` — the reified propositional formula carrier of
//! [`crate::init::prop`] that [`super::database`]/[`super::relations`] already
//! range over. No new carrier, no parallel `MmExpr` datatype: `transport()` is
//! reused *verbatim*, only fed its first non-identity `σ_hom`.
//!
//! ## The translation `σ_f` — variable-index renaming
//!
//! A formula `A : Φ⟨bool⟩` is a Church fold
//! `λ var ¬ ∧ ∨ ⟹. body` — it consumes five handlers, one per constructor.
//! The `var` handler has type `nat → bool` and is applied to the propositional
//! variable index at every leaf. To **rename every variable index by a function
//! `f : nat → nat`**, we re-plumb *only* the `var` handler, pre-composing it
//! with `f`, and pass the other four handlers through untouched:
//!
//! ```text
//!   σ_f := λA:Φ⟨bool⟩. λ v ¬ ∧ ∨ ⟹.  A (λn. v (f n)) ¬ ∧ ∨ ⟹
//! ```
//!
//! `σ_f : Φ⟨bool⟩ → Φ⟨bool⟩` is exactly [`super::relations`]'s `sigma_ty`, so
//! it plugs into `transport()` with no re-parameterisation. Instantiated at
//! `f := succ` (a genuine non-identity `nat → nat` term), `σ_f` shifts every
//! variable index up by one — e.g. `σ_f ⌜var 0⌝ = ⌜var (succ 0)⌝` — so it is
//! **observably not the identity** (proved in the tests).
//!
//! ## The homomorphism `σ_f ⌜X ⟹ Y⌝ = ⌜σ_f X ⟹ σ_f Y⌝`
//!
//! Because `enc_imp X Y` folds by applying the `⟹` handler to the folds of
//! `X` and `Y`, and `σ_f` only rewrites the `var` handler slot, both
//! `σ_f ⌜X ⟹ Y⌝` and `⌜σ_f X ⟹ σ_f Y⌝` β-normalise to the *same* term. The
//! proof is therefore the identical spine
//! [`super::relations::tests`] used at `σ = id` (`beta_nf` both sides, `trans`,
//! two `all_intro`s) — now generalised off `id` to the structural `σ_f`.
//!
//! ## Scope / what remains
//!
//! This upgrades transport at the `Φ⟨bool⟩` propositional carrier. The
//! **MM-import** carrier `Φ = nat` (`super::mm_database`, `concat`/`mm$c$<tok>`
//! free vars) is genuinely a recursor-free free algebra; a structural `σ`
//! *there* still needs the encoding reified as an inductive `MmExpr` datatype
//! (`sym(nat) | app(Rec, Rec)`) with a catamorphic recursor. That harder path
//! remains open — see the design note
//! `notes/vibes/logics/structural-sigma-transport.md` and the metalogic
//! `SKELETONS.md`.

use covalence_core::{Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use super::database::{enc_imp, fvar, phi};
use crate::init::ext::TermExt;

fn nat() -> Type {
    Type::nat()
}

fn bool_ty() -> Type {
    Type::bool()
}

/// The five Church-fold handler slot types at `'r := bool`, in fold order
/// `var ¬ ∧ ∨ ⟹` (mirrors [`crate::init::prop`]'s `phi_at(bool)`). The `var`
/// slot is `nat → bool`; the others are `bool → bool` / `bool → bool → bool`.
fn handler_tys() -> [(&'static str, Type); 5] {
    let un = Type::fun(bool_ty(), bool_ty());
    let bin = Type::fun(bool_ty(), Type::fun(bool_ty(), bool_ty()));
    [
        ("__var", Type::fun(nat(), bool_ty())),
        ("__neg", un.clone()),
        ("__and", bin.clone()),
        ("__or", bin.clone()),
        ("__imp", bin),
    ]
}

/// **The variable-index renaming translation `σ_f`.**
///
/// ```text
///   σ_f := λA:Φ⟨bool⟩. λ v ¬ ∧ ∨ ⟹.  A (λn. v (f n)) ¬ ∧ ∨ ⟹
/// ```
///
/// where `f : nat → nat`. Re-plumbs *only* the `var` handler (pre-composed with
/// `f`); the other four handlers pass straight through. Result type
/// `Φ⟨bool⟩ → Φ⟨bool⟩` = [`super::relations`]'s `sigma_ty()`, so `σ_f` feeds
/// `transport()` directly. Non-identity whenever `f` is (e.g. `f := succ`).
///
/// Uses fresh `__`-prefixed binder names distinct from
/// [`crate::init::prop`]'s `var`/`neg`/`and`/`or`/`imp` to avoid any β-capture.
pub fn var_rename_sigma(f: &Term) -> Result<Term> {
    let tys = handler_tys();

    // The bound formula `A : Φ⟨bool⟩`.
    let a = Term::free("__A", phi());

    // The re-plumbed `var` handler `λn:nat. __var (f n)`.
    let var_handler = {
        let n = Term::free("__n", nat());
        let var = Term::free("__var", tys[0].1.clone()); // __var : nat → bool
        let fn_ = f.clone().apply(n.clone())?; // f n : nat
        let body = var.apply(fn_)?; // __var (f n) : bool
        Term::abs(nat(), covalence_core::subst::close(&body, "__n"))
    };

    // `A (λn. __var (f n)) __neg __and __or __imp` — apply the (possibly
    // renamed) handlers to the folded formula.
    let mut folded = a.clone().apply(var_handler)?;
    for (name, ty) in tys.iter().skip(1) {
        folded = folded.apply(Term::free(*name, ty.clone()))?;
    }

    // Wrap in the five handler binders (innermost `__imp`, outermost `__var`).
    let mut body = folded;
    for (name, ty) in tys.iter().rev() {
        body = Term::abs(ty.clone(), covalence_core::subst::close(&body, name));
    }

    // Abstract over the formula argument `A`.
    Ok(Term::abs(phi(), covalence_core::subst::close(&body, "__A")))
}

/// `succ : nat → nat` — the successor function, a genuine non-identity
/// `nat → nat` term used to instantiate [`var_rename_sigma`]. Re-exported from
/// [`crate::init::nat`] so `σ_succ := var_rename_sigma(&succ())` shifts every
/// variable index up by one.
pub fn succ() -> Term {
    crate::init::nat::nat_succ()
}

/// `σ_f X` — apply the translation `σ_f` to an encoded formula `X`.
fn sigma_at(sigma: &Term, x: &Term) -> Result<Term> {
    sigma.clone().apply(x.clone())
}

/// **The `⟹`-homomorphism of a `var`-renaming `σ_f`:**
///
/// ```text
///   ⊢ ∀X Y. σ_f ⌜X ⟹ Y⌝ = ⌜σ_f X ⟹ σ_f Y⌝
/// ```
///
/// A genuine hypothesis-free HOL theorem (no postulates). This is exactly
/// [`super::relations::sigma_hom`] `(σ_f)` — the premise `transport()` carries —
/// discharged for the structural `σ_f = var_rename_sigma(f)` (rather than the
/// identity). Both sides β-normalise to the same term, so the proof is the
/// `id`-case spine generalised off `id`: `beta_nf` both sides, `trans`, two
/// `all_intro`s.
///
/// `X`, `Y : Φ⟨bool⟩` are bound; `f` (hence `σ_f`) is a fixed concrete term.
pub fn sigma_hom_of_var_rename(f: &Term) -> Result<Thm> {
    let sigma = var_rename_sigma(f)?;
    let x = fvar("X");
    let y = fvar("Y");

    // lhs = σ_f ⌜X ⟹ Y⌝ ; rhs = ⌜σ_f X ⟹ σ_f Y⌝.
    let lhs = sigma_at(&sigma, &enc_imp(&x, &y))?;
    let rhs = enc_imp(&sigma_at(&sigma, &x)?, &sigma_at(&sigma, &y)?);

    // ⊢ lhs = lhs_nf and ⊢ rhs = rhs_nf; the two normal forms coincide.
    let lhs_nf = crate::init::eq::beta_nf(lhs);
    let rhs_nf = crate::init::eq::beta_nf(rhs);

    // The load-bearing fact: both sides normalise to the same term. If this
    // ever failed (β-capture etc.), `trans` below would error rather than
    // fabricate — but assert it explicitly so a mismatch is a loud test failure.
    debug_assert_eq!(
        lhs_nf.concl().as_eq().expect("lhs beta_nf eq").1,
        rhs_nf.concl().as_eq().expect("rhs beta_nf eq").1,
        "σ_f ⌜X⟹Y⌝ and ⌜σ_f X ⟹ σ_f Y⌝ must share a β-normal form"
    );

    // ⊢ lhs = rhs, then generalise over Y then X.
    let eq = lhs_nf.trans(rhs_nf.sym()?)?;
    eq.all_intro("Y", phi())?.all_intro("X", phi())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::prop::p_var_at;
    use covalence_hol_eval::mk_nat;

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "theorem is hypothesis-free");
    }

    /// `var k : Φ⟨bool⟩` — a literal propositional variable, encoded at bool.
    fn var(k: u32) -> Term {
        p_var_at(
            &bool_ty(),
            mk_nat(covalence_types::Nat::from_inner(k.into())),
        )
    }

    /// The `σ_f` type is `Φ⟨bool⟩ → Φ⟨bool⟩` = `relations::sigma_ty()`.
    #[test]
    fn sigma_is_well_typed() {
        let sigma = var_rename_sigma(&succ()).unwrap();
        assert_eq!(
            sigma.type_of().unwrap(),
            Type::fun(phi(), phi()),
            "σ_succ : Φ⟨bool⟩ → Φ⟨bool⟩"
        );
    }

    /// **(1) The homomorphism theorem** — a genuine hypothesis-free HOL theorem
    /// `⊢ ∀X Y. σ_succ ⌜X ⟹ Y⌝ = ⌜σ_succ X ⟹ σ_succ Y⌝`, of exactly the shape
    /// `relations::sigma_hom(σ_succ)`.
    #[test]
    fn sigma_hom_of_var_rename_is_genuine() {
        let thm = sigma_hom_of_var_rename(&succ()).unwrap();
        assert_genuine(&thm);
        // Shape check: it IS `relations::sigma_hom(σ_succ)` (the transport premise).
        let sigma = var_rename_sigma(&succ()).unwrap();
        assert_eq!(
            thm.concl(),
            &super::super::relations::sigma_hom(&sigma).unwrap(),
            "the proved theorem is exactly the transport σ_hom premise at σ_succ"
        );
    }

    /// **(2) Non-vacuity witness — `σ_succ` genuinely moves a formula.** At
    /// `f := succ`, `σ_succ ⌜var 0⌝` β-reduces to `⌜var (succ 0)⌝`, which is
    /// syntactically distinct from `⌜var 0⌝` (the `var` argument differs:
    /// `succ 0` vs `0`). So `σ_succ ≠ id` — this is not the identity in disguise.
    #[test]
    fn sigma_succ_moves_a_variable() {
        let sigma = var_rename_sigma(&succ()).unwrap();
        let var0 = var(0);

        // ⊢ σ_succ ⌜var 0⌝ = (its β-normal form).
        let applied = sigma_at(&sigma, &var0).unwrap();
        let nf_thm = crate::init::eq::beta_nf(applied);
        assert_genuine(&nf_thm);
        let nf = nf_thm.concl().as_eq().unwrap().1.clone();

        // The normal form equals `⌜var (succ 0)⌝` (index shifted 0 → succ 0).
        let var_succ0 = {
            let succ0 = succ().apply(mk_nat(0u32)).unwrap(); // succ 0
            p_var_at(&bool_ty(), succ0)
        };
        let var_succ0_nf = crate::init::eq::beta_nf(var_succ0)
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        assert_eq!(
            nf, var_succ0_nf,
            "σ_succ ⌜var 0⌝ β-reduces to ⌜var (succ 0)⌝"
        );

        // And it is NOT `⌜var 0⌝` — the translation observably moves the term,
        // so this genuinely is not σ = id.
        let var0_nf = crate::init::eq::beta_nf(var(0))
            .concl()
            .as_eq()
            .unwrap()
            .1
            .clone();
        assert_ne!(
            nf, var0_nf,
            "σ_succ ⌜var 0⌝ ≠ ⌜var 0⌝ — σ_succ is not the identity"
        );
    }

    /// **(3) Transport at a real structural σ.** Feed `transport()` the
    /// non-identity `σ_succ` and discharge its `σ_hom` premise with theorem (1).
    /// The result is a genuine hypothesis-free HOL theorem
    /// `⊢ Interp DbA DbB σ_succ ⟹ Der_DbA S ⟹ Der_DbB (σ_succ S)` — transport of
    /// derivability across a genuine variable-index renaming. This is the same
    /// `transport()` proof `relations::tests` fed only `σ = id`, now at its
    /// first non-identity structural translation.
    #[test]
    fn transport_at_var_rename_is_genuine() {
        let sigma = var_rename_sigma(&succ()).unwrap();
        let hom = sigma_hom_of_var_rename(&succ()).unwrap();

        let transported = super::super::relations::transport()
            .unwrap()
            .inst("sigma", sigma.clone())
            .unwrap()
            .imp_elim(hom)
            .unwrap();
        assert_genuine(&transported);

        // Conclusion: `Interp DbA DbB σ_succ ⟹ Der_DbA S ⟹ Der_DbB (σ_succ S)`.
        let a = Term::free("DbA", super::super::database::database_ty());
        let b = Term::free("DbB", super::super::database::database_ty());
        let s = fvar("S");
        let expected = super::super::relations::interp(&a, &b, &sigma)
            .unwrap()
            .imp(
                super::super::database::derivable_db(&a, &s)
                    .unwrap()
                    .imp(
                        super::super::database::derivable_db(&b, &sigma_at(&sigma, &s).unwrap())
                            .unwrap(),
                    )
                    .unwrap(),
            )
            .unwrap();
        assert_eq!(
            transported.concl(),
            &expected,
            "transport at σ_succ has the renaming-instance shape"
        );

        // And this is genuinely NOT the identity instance: the transported
        // formula `σ_succ S` is not `S` (σ_succ shifts variable indices).
        let id_transported = super::super::database::derivable_db(&b, &s).unwrap();
        assert_ne!(
            &super::super::database::derivable_db(&b, &sigma_at(&sigma, &s).unwrap()).unwrap(),
            &id_transported,
            "the conclusion transports σ_succ S, not S — a real renaming, not id"
        );
    }
}
