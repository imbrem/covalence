//! The **`Hol` interface** — the value-typed HOL Light surface the inductive
//! engine is being ported onto, so the *same* engine can drive any HOL
//! backend: our native kernel today, an internal / object-level HOL later
//! (the "prove induction *inside* HOL" goal).
//!
//! ## Why a new trait
//!
//! `covalence-hol` already has [`HolLightKernel`](crate::HolLightKernel), but
//! that is the **arena**-style primitive interface (`&mut self`, `NameId`
//! handles — for OpenTheory-shaped backends). The inductive engine works with
//! *value-typed* terms / theorems (`Clone`, immutable, structural equality),
//! and with the **derived** HOL Light rules (`all_intro`, `imp_elim`,
//! `and_intro`, …) rather than only the 10 primitives. `Hol` is that
//! higher-level, value-typed surface.
//!
//! ## What a backend supplies
//!
//! Associated `Type` / `Term` / `Thm`, the logical-constant builders, and the
//! HOL Light rule set the engine uses. Our [`NativeHol`] forwards each to the
//! fast `covalence-core` constructor / rule (or the `init::eq` / `init::logic`
//! derivation); an internal-HOL backend would build object-level proofs the
//! same shape. The engine itself adds no axioms — type-specific facts
//! (induction, freeness) stay behind [`Inductive`](super::Inductive).
//!
//! The trait carries the **primitives and the "hard" derived rules** (β-normal
//! form, `∃`-intro / `∃`-elim, rewriting — each backend's own); the **easy**
//! derived rules ([`cong_arg`], [`conjuncts`], [`beta_reduce`],
//! [`beta_expand`], …) are generic free functions built on the trait, so a
//! backend gets them for free.
//!
//! ## Porting status
//!
//! Ported: the conjunction-proof plumbing ([`conj`] / [`project`] / [`and_all`]
//! / [`discharge_conj`]). The trait now covers the full proof-layer surface;
//! the remaining work is threading it through the data model (`InductiveSig` →
//! generic over `Hol::Term`/`Type`) and the `existence` / `uniqueness` /
//! `determinacy` / `recursor` proofs (the `Inductive` trait → `Inductive<H>`).
//! See `SKELETONS.md`.

use covalence_core::{Error, Result, Term, TermKind, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;

use crate::init::ext::TermExt;

/// The value-typed HOL Light surface the inductive engine reasons through.
///
/// Methods are grouped: **types**, **term builders**, **term / theorem
/// queries**, the **rule set** (primitives + the derived rules the engine
/// calls), and the **hard derived rules** (β-nf, `∃`, rewriting). The easy
/// derived rules are generic helpers below, not methods.
pub trait Hol {
    /// HOL types.
    type Type: Clone + PartialEq + std::fmt::Debug;
    /// HOL terms.
    type Term: Clone + PartialEq + std::fmt::Debug;
    /// HOL theorems.
    type Thm: Clone + std::fmt::Debug;

    // -- Types --

    /// The boolean type.
    fn bool_ty(&self) -> Self::Type;
    /// The function type `a → b`.
    fn fun_ty(&self, a: Self::Type, b: Self::Type) -> Self::Type;
    /// A (free) type variable `'name` — standard HOL's polymorphic type
    /// variable, e.g. the single carrier a monad theory abstracts over.
    fn tvar(&self, name: &str) -> Self::Type;

    // -- Term builders --

    /// A free variable `name : ty`.
    fn var(&self, name: &str, ty: Self::Type) -> Self::Term;
    /// Application `f x` (type-checked).
    fn app(&self, f: Self::Term, x: Self::Term) -> Result<Self::Term>;
    /// Abstraction `λ(name:ty). body`, closing free `name` in `body`.
    fn lam(&self, name: &str, ty: Self::Type, body: Self::Term) -> Self::Term;
    /// `a = b`.
    fn eq(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a ⟹ b`.
    fn imp(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `a ∧ b`.
    fn and(&self, a: Self::Term, b: Self::Term) -> Result<Self::Term>;
    /// `∀(name:ty). body`, closing free `name`.
    fn forall(&self, name: &str, ty: Self::Type, body: Self::Term) -> Result<Self::Term>;
    /// `∃(name:ty). body`, closing free `name`.
    fn exists(&self, name: &str, ty: Self::Type, body: Self::Term) -> Result<Self::Term>;
    /// The Hilbert choice operator `ε : (ty → bool) → ty`.
    fn select_op(&self, ty: Self::Type) -> Self::Term;

    // -- Queries --

    /// The type of a term.
    fn type_of(&self, t: &Self::Term) -> Result<Self::Type>;
    /// Destruct an application `f x`.
    fn dest_app(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// Destruct an equation `a = b`.
    fn dest_eq(&self, t: &Self::Term) -> Option<(Self::Term, Self::Term)>;
    /// Destruct a free variable, returning `(name, type)`.
    fn dest_var(&self, t: &Self::Term) -> Option<(String, Self::Type)>;
    /// Substitute the free variable `name` by `replacement` throughout `t`.
    fn subst_free(&self, t: &Self::Term, name: &str, replacement: &Self::Term) -> Self::Term;
    /// A theorem's conclusion.
    fn concl(&self, th: &Self::Thm) -> Self::Term;
    /// A theorem's hypotheses.
    fn hyps(&self, th: &Self::Thm) -> Vec<Self::Term>;

    // -- Rules --

    /// `ASSUME t`: `{t} ⊢ t`.
    fn assume(&self, t: Self::Term) -> Result<Self::Thm>;
    /// `REFL t`: `⊢ t = t`.
    fn refl(&self, t: Self::Term) -> Result<Self::Thm>;
    /// `⊢ a = b` → `⊢ b = a`.
    fn sym(&self, th: Self::Thm) -> Result<Self::Thm>;
    /// `⊢ a = b` + `⊢ b = c` → `⊢ a = c`.
    fn trans(&self, a: Self::Thm, b: Self::Thm) -> Result<Self::Thm>;
    /// `⊢ a = b` + `⊢ a` → `⊢ b` (EQ_MP).
    fn eq_mp(&self, eq: Self::Thm, p: Self::Thm) -> Result<Self::Thm>;
    /// `BETA ((λx.t) u)`: `⊢ (λx.t) u = t[u/x]` (single top redex).
    fn beta_conv(&self, redex: Self::Term) -> Result<Self::Thm>;
    /// `⊢ f = g` + `⊢ x = y` → `⊢ f x = g y` (MK_COMB).
    fn cong_app(&self, f: Self::Thm, x: Self::Thm) -> Result<Self::Thm>;
    /// Instantiate the free variable `name` by `t` in a theorem.
    fn inst(&self, th: Self::Thm, name: &str, t: Self::Term) -> Result<Self::Thm>;
    /// `Γ ⊢ p` → `Γ ⊢ ∀(name:ty). p` (GEN).
    fn all_intro(&self, th: Self::Thm, name: &str, ty: Self::Type) -> Result<Self::Thm>;
    /// `⊢ ∀x. p` → `⊢ p[t/x]` (SPEC).
    fn all_elim(&self, th: Self::Thm, t: Self::Term) -> Result<Self::Thm>;
    /// `Γ ⊢ q` → `Γ\{p} ⊢ p ⟹ q` (DISCH).
    fn imp_intro(&self, th: Self::Thm, h: &Self::Term) -> Result<Self::Thm>;
    /// `⊢ p ⟹ q` + `⊢ p` → `⊢ q` (MP).
    fn imp_elim(&self, imp: Self::Thm, ante: Self::Thm) -> Result<Self::Thm>;
    /// `⊢ a` + `⊢ b` → `⊢ a ∧ b`.
    fn and_intro(&self, a: Self::Thm, b: Self::Thm) -> Result<Self::Thm>;
    /// `⊢ a ∧ b` → `⊢ a`.
    fn and_elim_l(&self, th: Self::Thm) -> Result<Self::Thm>;
    /// `⊢ a ∧ b` → `⊢ b`.
    fn and_elim_r(&self, th: Self::Thm) -> Result<Self::Thm>;
    /// `⊢ F` → `⊢ goal` (ex falso).
    fn false_elim(&self, false_th: Self::Thm, goal: Self::Term) -> Result<Self::Thm>;
    /// The Hilbert axiom: `⊢ pred witness ⟹ pred (ε pred)`.
    fn select_ax(&self, pred: Self::Term, witness: Self::Term) -> Result<Self::Thm>;

    // -- Hard derived rules (each backend's own) --

    /// `⊢ t = nf` — the **β-normal form** of `t` (all redexes, under binders).
    fn beta_nf(&self, t: Self::Term) -> Result<Self::Thm>;
    /// From `⊢ pred witness` conclude `⊢ ∃x. pred x`.
    fn exists_intro(
        &self,
        pred: Self::Term,
        witness: Self::Term,
        proof: Self::Thm,
    ) -> Result<Self::Thm>;
    /// From `⊢ ∃x. pred x` and `⊢ ∀x. pred x ⟹ c` (with `c` free of `x`),
    /// conclude `⊢ c`.
    fn exists_elim(
        &self,
        exists_thm: Self::Thm,
        c: Self::Term,
        step: Self::Thm,
    ) -> Result<Self::Thm>;
    /// `⊢ t = t'` rewriting every occurrence of `eq`'s LHS by its RHS in `t`.
    fn rw_all(&self, t: &Self::Term, eq: &Self::Thm) -> Result<Self::Thm>;
}

/// The **native** backend: `Hol` over `covalence-core`'s value-typed kernel,
/// each method forwarding to the corresponding fast constructor / rule (or
/// the `init::eq` / `init::logic` derivation).
#[derive(Clone, Copy, Default, Debug)]
pub struct NativeHol;

impl Hol for NativeHol {
    type Type = Type;
    type Term = Term;
    type Thm = Thm;

    fn bool_ty(&self) -> Type {
        Type::bool()
    }
    fn fun_ty(&self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }
    fn tvar(&self, name: &str) -> Type {
        Type::tfree(name)
    }

    fn var(&self, name: &str, ty: Type) -> Term {
        Term::free(name, ty)
    }
    fn app(&self, f: Term, x: Term) -> Result<Term> {
        f.apply(x)
    }
    fn lam(&self, name: &str, ty: Type, body: Term) -> Term {
        Term::abs(ty, subst::close(&body, name))
    }
    fn eq(&self, a: Term, b: Term) -> Result<Term> {
        a.equals(b)
    }
    fn imp(&self, a: Term, b: Term) -> Result<Term> {
        a.imp(b)
    }
    fn and(&self, a: Term, b: Term) -> Result<Term> {
        a.and(b)
    }
    fn forall(&self, name: &str, ty: Type, body: Term) -> Result<Term> {
        body.forall(name, ty)
    }
    fn exists(&self, name: &str, ty: Type, body: Term) -> Result<Term> {
        body.exists(name, ty)
    }
    fn select_op(&self, ty: Type) -> Term {
        Term::select_op(ty)
    }

    fn type_of(&self, t: &Term) -> Result<Type> {
        t.type_of()
    }
    fn dest_app(&self, t: &Term) -> Option<(Term, Term)> {
        t.as_app().map(|(f, x)| (f.clone(), x.clone()))
    }
    fn dest_eq(&self, t: &Term) -> Option<(Term, Term)> {
        t.as_eq().map(|(a, b)| (a.clone(), b.clone()))
    }
    fn dest_var(&self, t: &Term) -> Option<(String, Type)> {
        match t.kind() {
            TermKind::Free(v) => Some((v.name().to_string(), v.ty().clone())),
            _ => None,
        }
    }
    fn subst_free(&self, t: &Term, name: &str, replacement: &Term) -> Term {
        subst::open(&subst::close(t, name), replacement)
    }
    fn concl(&self, th: &Thm) -> Term {
        th.concl().clone()
    }
    fn hyps(&self, th: &Thm) -> Vec<Term> {
        th.hyps().iter().cloned().collect()
    }

    fn assume(&self, t: Term) -> Result<Thm> {
        Thm::assume(t)
    }
    fn refl(&self, t: Term) -> Result<Thm> {
        Thm::refl(t)
    }
    fn sym(&self, th: Thm) -> Result<Thm> {
        th.sym()
    }
    fn trans(&self, a: Thm, b: Thm) -> Result<Thm> {
        a.trans(b)
    }
    fn eq_mp(&self, eq: Thm, p: Thm) -> Result<Thm> {
        eq.eq_mp(p)
    }
    fn beta_conv(&self, redex: Term) -> Result<Thm> {
        Thm::beta_conv(redex)
    }
    fn cong_app(&self, f: Thm, x: Thm) -> Result<Thm> {
        f.cong_app(x)
    }
    fn inst(&self, th: Thm, name: &str, t: Term) -> Result<Thm> {
        th.inst(name, t)
    }
    fn all_intro(&self, th: Thm, name: &str, ty: Type) -> Result<Thm> {
        th.all_intro(name, ty)
    }
    fn all_elim(&self, th: Thm, t: Term) -> Result<Thm> {
        th.all_elim(t)
    }
    fn imp_intro(&self, th: Thm, h: &Term) -> Result<Thm> {
        th.imp_intro(h)
    }
    fn imp_elim(&self, imp: Thm, ante: Thm) -> Result<Thm> {
        imp.imp_elim(ante)
    }
    fn and_intro(&self, a: Thm, b: Thm) -> Result<Thm> {
        a.and_intro(b)
    }
    fn and_elim_l(&self, th: Thm) -> Result<Thm> {
        th.and_elim_l()
    }
    fn and_elim_r(&self, th: Thm) -> Result<Thm> {
        th.and_elim_r()
    }
    fn false_elim(&self, false_th: Thm, goal: Term) -> Result<Thm> {
        false_th.false_elim(goal)
    }
    fn select_ax(&self, pred: Term, witness: Term) -> Result<Thm> {
        Thm::select_ax(pred, witness)
    }

    fn beta_nf(&self, t: Term) -> Result<Thm> {
        Ok(crate::init::eq::beta_nf(t))
    }
    fn exists_intro(&self, pred: Term, witness: Term, proof: Thm) -> Result<Thm> {
        crate::init::logic::exists_intro(pred, witness, proof)
    }
    fn exists_elim(&self, exists_thm: Thm, c: Term, step: Thm) -> Result<Thm> {
        crate::init::logic::exists_elim(exists_thm, c, step)
    }
    fn rw_all(&self, t: &Term, eq: &Thm) -> Result<Thm> {
        t.rw_all(eq)
    }
}

// ============================================================================
// Easy derived rules — generic free functions over any `Hol`
// ============================================================================

/// `⊢ x = y` → `⊢ f x = f y`, for a fixed `f`.
pub fn cong_arg<H: Hol>(hol: &H, th: H::Thm, f: H::Term) -> Result<H::Thm> {
    hol.cong_app(hol.refl(f)?, th)
}

/// `⊢ f = g` → `⊢ f a = g a`, for a fixed `a`.
pub fn cong_fn<H: Hol>(hol: &H, th: H::Thm, a: H::Term) -> Result<H::Thm> {
    hol.cong_app(th, hol.refl(a)?)
}

/// Split `⊢ a ∧ b` into `(⊢ a, ⊢ b)`.
pub fn conjuncts<H: Hol>(hol: &H, th: H::Thm) -> Result<(H::Thm, H::Thm)> {
    Ok((hol.and_elim_l(th.clone())?, hol.and_elim_r(th)?))
}

/// `⊢ φ` → `⊢ φ′`, rewriting `eq`'s LHS by its RHS throughout the conclusion.
pub fn rewrite<H: Hol>(hol: &H, th: H::Thm, eq: &H::Thm) -> Result<H::Thm> {
    let conv = hol.rw_all(&hol.concl(&th), eq)?;
    hol.eq_mp(conv, th)
}

/// `⊢ body` (`= f arg` β-reduced) → `⊢ f arg` — single-top-redex β-expand.
pub fn beta_expand<H: Hol>(hol: &H, f: &H::Term, arg: H::Term, body: H::Thm) -> Result<H::Thm> {
    let redex = hol.app(f.clone(), arg)?;
    hol.eq_mp(hol.sym(hol.beta_conv(redex)?)?, body)
}

/// `⊢ f arg` → `⊢ body` — single-top-redex β-reduce of the conclusion.
pub fn beta_reduce<H: Hol>(hol: &H, th: H::Thm) -> Result<H::Thm> {
    hol.eq_mp(hol.beta_conv(hol.concl(&th))?, th)
}

/// β-normalise a theorem's conclusion (full β).
pub fn beta_nf_concl<H: Hol>(hol: &H, th: H::Thm) -> Result<H::Thm> {
    hol.eq_mp(hol.beta_nf(hol.concl(&th))?, th)
}

/// `⊢ nf` (`= t` β-normalised) → `⊢ t` — full-β-expand.
pub fn beta_nf_expand<H: Hol>(hol: &H, t: H::Term, nf: H::Thm) -> Result<H::Thm> {
    hol.eq_mp(hol.sym(hol.beta_nf(t)?)?, nf)
}

// ============================================================================
// Conjunction-proof plumbing — generic over any `Hol`
// ============================================================================

/// Right-associated conjunction `t₀ ∧ (t₁ ∧ … ∧ tₙ)`. Errors on an empty
/// slice (the engine never builds an empty conjunction).
pub fn conj<H: Hol>(hol: &H, ts: &[H::Term]) -> Result<H::Term> {
    match ts {
        [] => Err(Error::ConnectiveRule(
            "inductive::hol: empty conjunction".into(),
        )),
        [last] => Ok(last.clone()),
        [head, rest @ ..] => hol.and(head.clone(), conj(hol, rest)?),
    }
}

/// Project conjunct `i` out of a proof of a right-associated conjunction
/// `c₀ ∧ (c₁ ∧ … ∧ c_{k-1})`.
pub fn project<H: Hol>(hol: &H, c: H::Thm, i: usize, k: usize) -> Result<H::Thm> {
    let mut t = c;
    for _ in 0..i {
        t = hol.and_elim_r(t)?;
    }
    if i + 1 < k { hol.and_elim_l(t) } else { Ok(t) }
}

/// `⊢ ⋀ thms` — the right-associated conjunction of the given proofs. Caller
/// guarantees a non-empty slice.
pub fn and_all<H: Hol>(hol: &H, thms: &[H::Thm]) -> Result<H::Thm> {
    let mut acc = thms[thms.len() - 1].clone();
    for t in thms[..thms.len() - 1].iter().rev() {
        acc = hol.and_intro(t.clone(), acc)?;
    }
    Ok(acc)
}

/// Discharge hypotheses `hyps` from `thm` as a single conjunctive antecedent:
/// `{h₀,…,hₙ} ⊢ c` ↦ `⊢ (⋀ hᵢ) ⟹ c`. Empty → unchanged; singleton → a plain
/// `imp_intro`.
pub fn discharge_conj<H: Hol>(hol: &H, thm: H::Thm, hyps: &[H::Term]) -> Result<H::Thm> {
    match hyps {
        [] => Ok(thm),
        [h] => hol.imp_intro(thm, h),
        _ => {
            let mut curried = thm;
            for h in hyps {
                curried = hol.imp_intro(curried, h)?;
            }
            let conj_term = conj(hol, hyps)?;
            let assumed = hol.assume(conj_term.clone())?;
            let mut cut = curried;
            for i in (0..hyps.len()).rev() {
                cut = hol.imp_elim(cut, project(hol, assumed.clone(), i, hyps.len())?)?;
            }
            hol.imp_intro(cut, &conj_term)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `discharge_conj` over `NativeHol` turns `{A, B} ⊢ A` into
    /// `⊢ (A ∧ B) ⟹ A`.
    #[test]
    fn discharge_conj_native_round_trips() {
        let hol = NativeHol;
        let (a, b) = (hol.var("A", hol.bool_ty()), hol.var("B", hol.bool_ty()));
        let thm = hol.assume(a.clone()).unwrap();
        let thm = hol.imp_intro(thm, &b).unwrap();
        let thm = hol.imp_elim(thm, hol.assume(b.clone()).unwrap()).unwrap(); // {A,B} ⊢ A
        assert_eq!(hol.hyps(&thm).len(), 2);

        let out = discharge_conj(&hol, thm, &[a.clone(), b.clone()]).unwrap();
        assert!(hol.hyps(&out).is_empty());
        let expected = hol.imp(conj(&hol, &[a.clone(), b]).unwrap(), a).unwrap();
        assert_eq!(&hol.concl(&out), &expected);
    }

    /// Build `∃x. x = p` through the trait + generic helpers: form the
    /// predicate `λx. x = p`, β-expand `⊢ p = p` to `⊢ (λx. x = p) p`, then
    /// `∃`-introduce. Exercises `lam` / `eq` / `refl` / `beta_expand` /
    /// `exists_intro` end to end over `NativeHol`.
    #[test]
    fn exists_intro_through_the_interface() {
        let hol = NativeHol;
        let bool_ty = hol.bool_ty();
        let p = hol.var("p", bool_ty.clone());
        let x = hol.var("x", bool_ty.clone());
        let pred = hol.lam("x", bool_ty.clone(), hol.eq(x, p.clone()).unwrap());

        let at_p = beta_expand(&hol, &pred, p.clone(), hol.refl(p.clone()).unwrap()).unwrap();
        let ex = hol.exists_intro(pred, p.clone(), at_p).unwrap();

        assert!(hol.hyps(&ex).is_empty());
        let expected = hol
            .exists(
                "x",
                bool_ty.clone(),
                hol.eq(hol.var("x", bool_ty), p).unwrap(),
            )
            .unwrap();
        assert_eq!(&hol.concl(&ex), &expected);
    }
}
