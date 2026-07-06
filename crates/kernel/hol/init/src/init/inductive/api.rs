//! Glue between the logic-agnostic **inductive-types API**
//! ([`covalence_inductive`]) and this crate's native HOL machinery.
//!
//! Three pieces:
//!
//! 1. [`covalence_inductive::Logic`] / [`covalence_inductive::LogicOps`]
//!    implemented for [`NativeHol`] — the native kernel is one `LogicOps`
//!    logic among (eventually) many, so generic consumers (the
//!    [`conformance`](covalence_inductive::conformance) suite, future
//!    layers like an ACL2-style theory) run against it unchanged.
//! 2. Native derivation helpers shared by the HOL backends:
//!    `relativize_induct` (turn a bare `⊢ ∀t. P t` into the bundle's
//!    membership-relativized form) and `derive_cases_native` (the
//!    exhaustiveness theorem, derived generically from the bundle's own
//!    `induct` — backend-independent, so both HOL backends share it).
//! 3. Small conjunction plumbing (`project_conj`).
//!
//! The backends themselves live in [`super::church`] (the impredicative
//! encoding) and [`super::engine`] (the typedef + recursion-engine
//! adapter).

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_inductive::{ArgSort, IndResult, InductiveError, InductiveSpec, Logic, LogicOps};

use super::hol::{Hol, NativeHol};
use crate::init::eq::{beta_expand, beta_nf};
use crate::init::ext::TermExt;
use crate::init::logic::exists_intro;

// ============================================================================
// NativeHol as a `covalence_inductive` logic
// ============================================================================

impl Logic for NativeHol {
    type Type = Type;
    type Term = Term;
    type Thm = Thm;
    type Error = covalence_core::Error;
}

impl LogicOps for NativeHol {
    fn bool_ty(&self) -> Type {
        Hol::bool_ty(self)
    }
    fn fun_ty(&self, a: Type, b: Type) -> Type {
        Hol::fun_ty(self, a, b)
    }

    fn var(&self, name: &str, ty: Type) -> Term {
        Hol::var(self, name, ty)
    }
    fn app(&self, f: Term, x: Term) -> Result<Term> {
        Hol::app(self, f, x)
    }
    fn lam(&self, name: &str, ty: Type, body: Term) -> Term {
        Hol::lam(self, name, ty, body)
    }
    fn eq(&self, a: Term, b: Term) -> Result<Term> {
        Hol::eq(self, a, b)
    }
    fn imp(&self, a: Term, b: Term) -> Result<Term> {
        Hol::imp(self, a, b)
    }
    fn and(&self, a: Term, b: Term) -> Result<Term> {
        Hol::and(self, a, b)
    }
    fn forall(&self, name: &str, ty: Type, body: Term) -> Result<Term> {
        Hol::forall(self, name, ty, body)
    }
    fn exists(&self, name: &str, ty: Type, body: Term) -> Result<Term> {
        Hol::exists(self, name, ty, body)
    }

    fn type_of(&self, t: &Term) -> Result<Type> {
        Hol::type_of(self, t)
    }
    fn dest_app(&self, t: &Term) -> Option<(Term, Term)> {
        Hol::dest_app(self, t)
    }
    fn dest_eq(&self, t: &Term) -> Option<(Term, Term)> {
        Hol::dest_eq(self, t)
    }
    fn concl(&self, th: &Thm) -> Term {
        Hol::concl(self, th)
    }
    fn hyps(&self, th: &Thm) -> Vec<Term> {
        Hol::hyps(self, th)
    }

    fn assume(&self, t: Term) -> Result<Thm> {
        Hol::assume(self, t)
    }
    fn refl(&self, t: Term) -> Result<Thm> {
        Hol::refl(self, t)
    }
    fn sym(&self, th: Thm) -> Result<Thm> {
        Hol::sym(self, th)
    }
    fn trans(&self, a: Thm, b: Thm) -> Result<Thm> {
        Hol::trans(self, a, b)
    }
    fn eq_mp(&self, eq: Thm, p: Thm) -> Result<Thm> {
        Hol::eq_mp(self, eq, p)
    }
    fn beta_conv(&self, redex: Term) -> Result<Thm> {
        Hol::beta_conv(self, redex)
    }
    fn cong_app(&self, f: Thm, x: Thm) -> Result<Thm> {
        Hol::cong_app(self, f, x)
    }
    fn inst(&self, th: Thm, name: &str, t: Term) -> Result<Thm> {
        Hol::inst(self, th, name, t)
    }
    fn all_intro(&self, th: Thm, name: &str, ty: Type) -> Result<Thm> {
        Hol::all_intro(self, th, name, ty)
    }
    fn all_elim(&self, th: Thm, t: Term) -> Result<Thm> {
        Hol::all_elim(self, th, t)
    }
    fn imp_intro(&self, th: Thm, h: &Term) -> Result<Thm> {
        Hol::imp_intro(self, th, h)
    }
    fn imp_elim(&self, imp: Thm, ante: Thm) -> Result<Thm> {
        Hol::imp_elim(self, imp, ante)
    }
    fn and_intro(&self, a: Thm, b: Thm) -> Result<Thm> {
        Hol::and_intro(self, a, b)
    }
    fn and_elim_l(&self, th: Thm) -> Result<Thm> {
        Hol::and_elim_l(self, th)
    }
    fn and_elim_r(&self, th: Thm) -> Result<Thm> {
        Hol::and_elim_r(self, th)
    }
}

// ============================================================================
// Shared native derivation helpers
// ============================================================================

/// Internal-error shorthand for backend derivations.
pub(crate) fn internal<T>(msg: impl Into<String>) -> IndResult<T, NativeHol> {
    Err(InductiveError::Internal(msg.into()))
}

/// Project conjunct `i` out of a right-associated conjunction proof of `k`
/// conjuncts.
pub(crate) fn project_conj(thm: Thm, i: usize, k: usize) -> Result<Thm> {
    let mut t = thm;
    for _ in 0..i {
        t = t.and_elim_r()?;
    }
    if i + 1 < k { t.and_elim_l() } else { Ok(t) }
}

/// From a bare induction conclusion `⊢ ∀t. P t` produce the bundle's
/// membership-relativized `⊢ ∀t. mem t ⟹ P t` (applied form throughout).
pub(crate) fn relativize_induct(unrel: Thm, mem: &Term, carrier: &Type) -> Result<Thm> {
    let tv = Term::free("__rel_t", carrier.clone());
    let at_t = unrel.all_elim(tv.clone())?; // ⊢ P t   (applied)
    let guard = Term::app(mem.clone(), tv);
    at_t.imp_intro(&guard)?
        .all_intro("__rel_t", carrier.clone())
}

/// The disjunct `∃y⃗. lhs = Cᵢ y⃗` (bound variables `y⃗` over the
/// constructor's argument types; recursive positions at `carrier`).
fn disjunct(
    spec: &InductiveSpec<Type>,
    carrier: &Type,
    ctors: &[Term],
    lhs: &Term,
    i: usize,
) -> Result<Term> {
    let c = &spec.ctors[i];
    // Markers for the bound argument slots (closed below, innermost last).
    let mut rhs = ctors[i].clone();
    let mut markers = Vec::with_capacity(c.args.len());
    for (j, (_, sort)) in c.args.iter().enumerate() {
        let ty = match sort {
            ArgSort::Rec => carrier.clone(),
            ArgSort::Ext(x) => x.clone(),
        };
        let m = Term::free(format!("__cases_c{j}"), ty.clone());
        rhs = rhs.apply(m.clone())?;
        markers.push((format!("__cases_c{j}"), ty));
    }
    let mut t = lhs.clone().equals(rhs)?;
    for (name, ty) in markers.into_iter().rev() {
        t = t.exists(&name, ty)?;
    }
    Ok(t)
}

/// As [`disjunct`], but with argument slots `..j` filled by the given
/// terms, slot `j` by the free marker `__cases_hole`, and slots `> j`
/// existentially bound. Used to build the ∃-introduction predicates.
fn disjunct_with_hole(
    spec: &InductiveSpec<Type>,
    carrier: &Type,
    ctors: &[Term],
    lhs: &Term,
    i: usize,
    fixed: &[Term],
    j: usize,
) -> Result<(Term, Type)> {
    let c = &spec.ctors[i];
    let hole_ty = match &c.args[j].1 {
        ArgSort::Rec => carrier.clone(),
        ArgSort::Ext(x) => x.clone(),
    };
    let hole = Term::free("__cases_hole", hole_ty.clone());
    let mut rhs = ctors[i].clone();
    let mut bound = Vec::new();
    for (m, (_, sort)) in c.args.iter().enumerate() {
        let ty = match sort {
            ArgSort::Rec => carrier.clone(),
            ArgSort::Ext(x) => x.clone(),
        };
        let arg = if m < j {
            fixed[m].clone()
        } else if m == j {
            hole.clone()
        } else {
            let mk = Term::free(format!("__cases_c{m}"), ty.clone());
            bound.push((format!("__cases_c{m}"), ty));
            mk
        };
        rhs = rhs.apply(arg)?;
    }
    let mut t = lhs.clone().equals(rhs)?;
    for (name, ty) in bound.into_iter().rev() {
        t = t.exists(&name, ty)?;
    }
    Ok((t, hole_ty))
}

/// The rule-form induction closure [`derive_cases_native`] drives (a
/// named alias for the `Fn` signature).
pub(crate) trait InductRule: Fn(&Term, Vec<Thm>) -> IndResult<Thm, NativeHol> {}
impl<F: Fn(&Term, Vec<Thm>) -> IndResult<Thm, NativeHol>> InductRule for F {}

/// Derive the **exhaustiveness** theorem
/// `⊢ ∀t. mem t ⟹ ⋁ᵢ ∃x⃗. t = Cᵢ x⃗` from the bundle's own `induct` —
/// backend-independent (both HOL backends share it): each case is proved
/// by `refl` + ∃-introduction + ∨-introduction.
pub(crate) fn derive_cases_native(
    spec: &InductiveSpec<Type>,
    carrier: &Type,
    ctors: &[Term],
    induct: &dyn InductRule,
) -> IndResult<Thm, NativeHol> {
    let n = spec.arity();
    // The motive `λs. D₀(s) ∨ (D₁(s) ∨ …)`.
    let sv = Term::free("__cases_t", carrier.clone());
    let or_chain = |lhs: &Term, from: usize| -> Result<Term> {
        let mut t = disjunct(spec, carrier, ctors, lhs, n - 1)?;
        for m in (from..n - 1).rev() {
            t = disjunct(spec, carrier, ctors, lhs, m)?.or(t)?;
        }
        Ok(t)
    };
    let motive = Term::abs(
        carrier.clone(),
        subst::close(&or_chain(&sv, 0)?, "__cases_t"),
    );

    let mut cases = Vec::with_capacity(n);
    for i in 0..n {
        let c = &spec.ctors[i];
        // Free argument variables named by the binder hints.
        let args: Vec<Term> = c
            .args
            .iter()
            .map(|(nm, sort)| {
                let ty = match sort {
                    ArgSort::Rec => carrier.clone(),
                    ArgSort::Ext(x) => x.clone(),
                };
                Term::free(nm.as_str(), ty)
            })
            .collect();
        let mut capp = ctors[i].clone();
        for a in &args {
            capp = capp.apply(a.clone())?;
        }

        // ⊢ Cᵢ x⃗ = Cᵢ x⃗, then ∃-introduce the RHS arguments innermost-out.
        let mut thm = Thm::refl(capp.clone())?;
        for j in (0..c.args.len()).rev() {
            let (body, hole_ty) = disjunct_with_hole(spec, carrier, ctors, &capp, i, &args, j)?;
            let pred = Term::abs(hole_ty, subst::close(&body, "__cases_hole"));
            let at_witness = beta_expand(&pred, args[j].clone(), thm)?;
            thm = exists_intro(pred, args[j].clone(), at_witness)?;
        }
        // ∨-introduce into position `i` of the right-nested chain.
        if i < n - 1 {
            thm = thm.or_intro_l(or_chain(&capp, i + 1)?)?;
        }
        for m in (0..i).rev() {
            thm = thm.or_intro_r(disjunct(spec, carrier, ctors, &capp, m)?)?;
        }
        // β-expand to the applied motive, then add the (unused) IHs.
        let mut case = beta_expand(&motive, capp, thm)?;
        for k in c.rec_positions().collect::<Vec<_>>().into_iter().rev() {
            case = case.imp_intro(&Term::app(motive.clone(), args[k].clone()))?;
        }
        cases.push(case);
    }
    induct(&motive, cases)
}

/// `⊢ lhs = rhs`, both sides β-normalising to the same normal form (the
/// computation-law prover — the [`crate::init::sexpr`] /
/// [`crate::init::tree`] `prove_rec_eq` pattern, shared by the backends).
pub(crate) fn prove_beta_eq(lhs: Term, rhs: Term) -> IndResult<Thm, NativeHol> {
    let l = beta_nf(lhs); // ⊢ lhs = nfL
    let r = beta_nf(rhs); // ⊢ rhs = nfR
    let (Some((_, nl)), Some((_, nr))) = (l.concl().as_eq(), r.concl().as_eq()) else {
        return internal("prove_beta_eq: beta_nf did not return an equation");
    };
    if nl != nr {
        return internal(format!(
            "prove_beta_eq: normal forms differ:\n  {nl}\n  {nr}"
        ));
    }
    Ok(l.trans(r.sym()?)?)
}
