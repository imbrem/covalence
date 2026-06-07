//! Pure theorems and the LCF rule API.
//!
//! `Thm` is the opaque kernel type. Its only constructor is the
//! private `Thm::build`, which type-checks the conclusion and every
//! hypothesis at kind `prop`. The rule methods are the only paths to
//! a `Thm` value; constructional soundness in the LCF sense.
//!
//! ## Observations and universality
//!
//! Observation leaves carry kernel-allocated [`DynObs`] handles,
//! compared by `Arc` pointer identity rather than by user-supplied
//! `Eq` impls — so a misbehaving observer cannot corrupt the
//! kernel's hyp `BTreeSet`. A theorem with no `Obs` leaves anywhere
//! (test via [`Thm::has_no_obs`]) is **universally true** with no
//! oracle dependencies, the same property HOL Light's `thm` has.
//!
//! The rule set is Pure-shaped:
//!
//! - LF: `assume`, `imp_intro`/`imp_elim`, `all_intro`/`all_elim`.
//! - Equality: `refl`, `trans`, `sym`, `cong_app`, `cong_abs`,
//!   `beta_conv`, `eta_conv`.
//! - Type-variable instantiation: `inst_tfree`.
//!
//! `define`, `observe`, and the user-supplied `O → Thm` conversion
//! are not in this MVP step.

use std::collections::BTreeSet;
use std::fmt;
use std::sync::Arc;

use crate::error::{Error, Result};
use crate::subst::{
    close, find_free_type, has_free_var, open, shift_by, subst_tfree_in_term, uses_bound_outer,
};
use crate::term::{Def, DynObs, Hint, ObsEq, Observer, Term, TermKind, Type, TypeEnv, type_of_in};

#[derive(Clone)]
pub struct Thm {
    hyps: Arc<BTreeSet<Term>>,
    concl: Term,
}

impl Thm {
    /// The single private constructor. Validates that every term is
    /// well-typed at kind `prop` AND — by reusing one [`TypeEnv`]
    /// across all of them — that every `Free` name has a single
    /// declared type across the whole theorem.
    ///
    /// Every rule API in this module bottoms out here.
    fn build(hyps: BTreeSet<Term>, concl: Term) -> Result<Thm> {
        let mut env = TypeEnv::default();
        let ty = type_of_in(&concl, &mut env)?;
        if !ty.is_prop() {
            return Err(Error::NotProp(ty));
        }
        for h in &hyps {
            let hty = type_of_in(h, &mut env)?;
            if !hty.is_prop() {
                return Err(Error::NotProp(hty));
            }
        }
        Ok(Thm {
            hyps: Arc::new(hyps),
            concl,
        })
    }

    pub fn hyps(&self) -> &BTreeSet<Term> {
        &self.hyps
    }
    pub fn concl(&self) -> &Term {
        &self.concl
    }
    pub fn into_parts(self) -> (Arc<BTreeSet<Term>>, Term) {
        (self.hyps, self.concl)
    }

    /// Returns `true` iff no `Obs` leaf appears anywhere in the
    /// theorem (conclusion or any hypothesis). Such a theorem is
    /// universally true with no oracle dependencies — equivalent to
    /// HOL Light's `thm`.
    pub fn has_no_obs(&self) -> bool {
        self.concl.has_no_obs() && self.hyps.iter().all(|h| h.has_no_obs())
    }

    /// Returns `true` iff every `Obs` leaf in the theorem (concl and
    /// hyps) carries an observer whose dynamic type is `O`. Trivially
    /// `true` for a theorem with no `Obs` leaves.
    pub fn all_obs_match<O: Observer>(&self) -> bool {
        self.concl.all_obs_match::<O>() && self.hyps.iter().all(|h| h.all_obs_match::<O>())
    }

    /// Walk the theorem and call `f` on every `Obs` leaf's observer
    /// downcast to `O`. Returns `Err(ObsDowncastTypeMismatch)` at
    /// the first leaf whose dynamic type does not match `O`.
    pub fn for_each_obs<O: Observer, F: FnMut(&O)>(&self, f: &mut F) -> Result<()> {
        self.concl.for_each_obs::<O, F>(f)?;
        for h in self.hyps.iter() {
            h.for_each_obs::<O, F>(f)?;
        }
        Ok(())
    }

    // ---- LF rules ----

    /// `{φ} ⊢ φ`, requiring `φ : prop`.
    pub fn assume(phi: Term) -> Result<Thm> {
        let mut hyps = BTreeSet::new();
        hyps.insert(phi.clone());
        Self::build(hyps, phi)
    }

    /// `Γ \ {φ} ⊢ φ ⟹ ψ`, given `Γ ⊢ ψ`.
    pub fn imp_intro(self, phi: &Term) -> Result<Thm> {
        let mut hyps = (*self.hyps).clone();
        hyps.remove(phi);
        let concl = Term::imp(phi.clone(), self.concl);
        Self::build(hyps, concl)
    }

    /// `Γ ∪ Γ' ⊢ ψ`, given `Γ ⊢ φ⟹ψ` and `Γ' ⊢ φ`.
    pub fn imp_elim(self, hyp: Thm) -> Result<Thm> {
        let TermKind::Imp(phi, psi) = self.concl.kind() else {
            return Err(Error::NotMetaImp(format!("{}", self.concl)));
        };
        if *phi != hyp.concl {
            return Err(Error::ImpAntecedentMismatch {
                expected: format!("{}", phi),
                got: format!("{}", hyp.concl),
            });
        }
        let psi = psi.clone();
        let hyps = union_hyps(&self.hyps, &hyp.hyps);
        Self::build(hyps, psi)
    }

    /// `Γ ⊢ ⋀x:τ. φ`, given `Γ ⊢ φ(x)` with `Free(x:τ)` not in `FV(Γ)`.
    pub fn all_intro(self, name: &str, ty: Type) -> Result<Thm> {
        for h in self.hyps.iter() {
            if has_free_var(h, name) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
        }
        if let Some(declared) = find_free_type(&self.concl, name)
            && declared != ty
        {
            return Err(Error::BinderTypeMismatch {
                name: name.into(),
                declared,
                expected: ty,
            });
        }
        let body = close(&self.concl, name);
        let all = Term::all(name, ty, body);
        Self::build((*self.hyps).clone(), all)
    }

    /// `Γ ⊢ φ[t/0]`, given `Γ ⊢ ⋀x:τ. φ` and `t : τ`.
    pub fn all_elim(self, witness: Term) -> Result<Thm> {
        let TermKind::All(_, ty, body) = self.concl.kind() else {
            return Err(Error::NotMetaAll(format!("{}", self.concl)));
        };
        let wit_ty = witness.type_of()?;
        if wit_ty != *ty {
            return Err(Error::TypeMismatch {
                expected: ty.clone(),
                got: wit_ty,
            });
        }
        let concl = open(body, &witness);
        Self::build((*self.hyps).clone(), concl)
    }

    // ---- Equality rules ----

    /// `⊢ t ≡ t`.
    pub fn refl(t: Term) -> Result<Thm> {
        let _ = t.type_of()?;
        let concl = Term::eq(t.clone(), t);
        Self::build(BTreeSet::new(), concl)
    }

    /// `Γ ∪ Γ' ⊢ t ≡ v`, given `Γ ⊢ t≡u` and `Γ' ⊢ u≡v`.
    pub fn trans(self, other: Thm) -> Result<Thm> {
        let TermKind::Eq(t, u1) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        let TermKind::Eq(u2, v) = other.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", other.concl)));
        };
        if u1 != u2 {
            return Err(Error::TransMiddleMismatch {
                left: format!("{}", u1),
                right: format!("{}", u2),
            });
        }
        let concl = Term::eq(t.clone(), v.clone());
        let hyps = union_hyps(&self.hyps, &other.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ u ≡ t`, given `Γ ⊢ t≡u`.
    pub fn sym(self) -> Result<Thm> {
        let TermKind::Eq(t, u) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        let concl = Term::eq(u.clone(), t.clone());
        Self::build((*self.hyps).clone(), concl)
    }

    /// `Γ ∪ Γ' ⊢ f(s) ≡ g(t)`, given `Γ ⊢ f≡g` and `Γ' ⊢ s≡t`. The new
    /// applications must type-check.
    pub fn cong_app(self, arg: Thm) -> Result<Thm> {
        let TermKind::Eq(f, g) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        let TermKind::Eq(s, t) = arg.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", arg.concl)));
        };
        let lhs = Term::app(f.clone(), s.clone());
        let rhs = Term::app(g.clone(), t.clone());
        // `build()` re-validates types end-to-end.
        let concl = Term::eq(lhs, rhs);
        let hyps = union_hyps(&self.hyps, &arg.hyps);
        Self::build(hyps, concl)
    }

    /// `Γ ⊢ (λy:τ. s[y/x]) ≡ (λy:τ. t[y/x])`, given `Γ ⊢ s≡t` with
    /// `Free(name:τ)` not in `FV(Γ)`. The supplied `ty` must match
    /// the declared type of `Free(name)` wherever it appears in the
    /// theorem.
    pub fn cong_abs(self, name: &str, ty: Type) -> Result<Thm> {
        let TermKind::Eq(s, t) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        for h in self.hyps.iter() {
            if has_free_var(h, name) {
                return Err(Error::FreeVarInHyps { name: name.into() });
            }
        }
        let declared = find_free_type(s, name).or_else(|| find_free_type(t, name));
        if let Some(declared) = declared
            && declared != ty
        {
            return Err(Error::BinderTypeMismatch {
                name: name.into(),
                declared,
                expected: ty,
            });
        }
        let s_abs = Term::abs(name, ty.clone(), close(s, name));
        let t_abs = Term::abs(name, ty, close(t, name));
        let concl = Term::eq(s_abs, t_abs);
        Self::build((*self.hyps).clone(), concl)
    }

    /// `⊢ (λx:τ. body) arg ≡ body[arg/0]`.
    pub fn beta_conv(app: Term) -> Result<Thm> {
        let TermKind::App(fun, arg) = app.kind() else {
            return Err(Error::NotApp(format!("{}", app)));
        };
        let TermKind::Abs(_, ty, body) = fun.kind() else {
            return Err(Error::NotAbs(format!("{}", fun)));
        };
        let arg_ty = arg.type_of()?;
        if arg_ty != *ty {
            return Err(Error::TypeMismatch {
                expected: ty.clone(),
                got: arg_ty,
            });
        }
        let rhs = open(body, arg);
        let concl = Term::eq(app.clone(), rhs);
        Self::build(BTreeSet::new(), concl)
    }

    /// `⊢ (λx:τ. f x) ≡ f`, when `Bound(0)` does not appear free in `f`.
    pub fn eta_conv(abs: Term) -> Result<Thm> {
        let TermKind::Abs(_, ty, body) = abs.kind() else {
            return Err(Error::NotAbs(format!("{}", abs)));
        };
        let TermKind::App(f, x) = body.kind() else {
            return Err(Error::EtaShape);
        };
        let TermKind::Bound(0) = x.kind() else {
            return Err(Error::EtaShape);
        };
        if uses_bound_outer(f, 0) {
            return Err(Error::EtaShape);
        }
        let _ = abs.type_of()?;
        let _ = ty;
        let f_outer = shift_by(f, -1, 0);
        let concl = Term::eq(abs.clone(), f_outer);
        Self::build(BTreeSet::new(), concl)
    }

    /// Introduce a fresh defined constant: emit `⊢ Def(name, body) ≡ body`.
    ///
    /// Each call allocates a *fresh* `Arc` for the body, so two
    /// distinct `define` calls — even with the same name and the same
    /// body term — produce distinct `Def`s. The kernel never reuses a
    /// `Def` identity, so users cannot accidentally derive
    /// `⊢ body₁ ≡ body₂` by `trans`+`sym`-ing two equations for "the
    /// same name" — the two `Def`s are simply different symbols that
    /// happen to share a display label.
    ///
    /// The `name` is display-only (an α-transparent [`Hint`]). The
    /// `body` must be a valid Pure term (typeable in isolation).
    ///
    /// ## Soundness
    ///
    /// Sound because the resulting `Def` is a brand-new symbol whose
    /// only equation says it equals `body`. In any model satisfying
    /// the prior theory, we extend by interpreting this `Def` as
    /// `⟦body⟧` — a conservative extension. No global signature is
    /// needed because the allocator gives us uniqueness per call.
    pub fn define(name: impl Into<Hint>, body: Term) -> Result<Thm> {
        // Validate the body type-checks in isolation.
        let _ = body.type_of()?;
        let d = Def::new_internal(name.into(), body.clone());
        let concl = Term::eq(Term::def(d), body);
        Self::build(BTreeSet::new(), concl)
    }

    /// `Γ[α:=σ] ⊢ φ[α:=σ]`.
    pub fn inst_tfree(self, name: &str, replacement: Type) -> Result<Thm> {
        let concl = subst_tfree_in_term(&self.concl, name, &replacement);
        let mut hyps = BTreeSet::new();
        for h in self.hyps.iter() {
            hyps.insert(subst_tfree_in_term(h, name, &replacement));
        }
        Self::build(hyps, concl)
    }

    /// `⊢ expr1 ≡ expr2`, where:
    /// - `expr1` and `expr2` each have the form `(obs head)(arg1)(arg2)…`
    ///   (zero or more applications of an `Obs` leaf at the head).
    /// - both head observers downcast successfully to Rust type `O`.
    /// - both expressions have the same Pure type.
    /// - the observer's [`ObsEq::obs_eq`] method, called with the two
    ///   observers and their args, returns `true`.
    ///
    /// ## Soundness
    ///
    /// The kernel rule is **unconditionally sound** regardless of
    /// what `O::obs_eq` returns. See [`ObsEq`]'s documentation for the
    /// parametric ε-model that makes this work. Observer impls are
    /// *not* part of the TCB — they are a per-Rust-type policy lever,
    /// not a soundness obligation. Different observer types `O`, `O'`
    /// get independent ε-families, so the rule never lets one
    /// observer's policy compromise another's.
    pub fn obs_eq<O: ObsEq>(expr1: Term, expr2: Term) -> Result<Thm> {
        let (obs1, args1) = decompose_obs_app(&expr1)?;
        let (obs2, args2) = decompose_obs_app(&expr2)?;
        let o1 = obs1.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let o2 = obs2.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty1 = expr1.type_of()?;
        let ty2 = expr2.type_of()?;
        if ty1 != ty2 {
            return Err(Error::TypeMismatch {
                expected: ty1,
                got: ty2,
            });
        }
        if !o1.obs_eq(o2, &args1, &args2) {
            return Err(Error::ObsEqRefused);
        }
        let concl = Term::eq(expr1, expr2);
        Self::build(BTreeSet::new(), concl)
    }
}

/// Walk down through `App`s collecting arguments left-to-right. If
/// the final node is an `Obs` leaf, return its observer and the args
/// list; otherwise return an error.
fn decompose_obs_app(t: &Term) -> Result<(&DynObs, Vec<Term>)> {
    let mut args_rev = Vec::new();
    let mut cur = t;
    loop {
        match cur.kind() {
            TermKind::App(f, x) => {
                args_rev.push(x.clone());
                cur = f;
            }
            TermKind::Obs(observer, _) => {
                args_rev.reverse();
                return Ok((observer, args_rev));
            }
            _ => return Err(Error::NotObsHead(format!("{}", t))),
        }
    }
}

impl fmt::Debug for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hyps.is_empty() {
            return write!(f, "⊢ {}", self.concl);
        }
        for (i, h) in self.hyps.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", h)?;
        }
        write!(f, " ⊢ {}", self.concl)
    }
}

fn union_hyps(a: &Arc<BTreeSet<Term>>, b: &Arc<BTreeSet<Term>>) -> BTreeSet<Term> {
    if Arc::ptr_eq(a, b) {
        return (**a).clone();
    }
    let mut out = (**a).clone();
    out.extend(b.iter().cloned());
    out
}
