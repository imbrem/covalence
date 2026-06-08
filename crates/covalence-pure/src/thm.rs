//! Pure theorems and the LCF rule API.
//!
//! `Thm` is the opaque kernel type. Its only constructor is the
//! private `Thm::build`, which type-checks the conclusion and every
//! hypothesis at kind `prop`. The rule methods are the only paths to
//! a `Thm` value; constructional soundness in the LCF sense.
//!
//! ## Observations and universality
//!
//! Observation leaves carry kernel-allocated [`Object`] handles,
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

use crate::builtins;
use crate::error::{Error, Result};
use crate::subst::{
    close, find_free_type, has_free_var, open, shift_by, subst_tfree_in_term, uses_bound_outer,
};
use crate::term::{
    Def, BinderHint, ObsEq, ObsImp, ObsTrue, Object, Observer, Term, TermKind, Type, TypeEnv, TypeKind,
    type_of_in,
};

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

    /// `Γ ∪ Γ' ⊢ q`, given `Γ ⊢ p ≡ q` and `Γ' ⊢ p`.
    ///
    /// Meta-equality MP. This is the Pure analogue of HOL Light's
    /// `EQ_MP` — but at the meta level. Standard primitive in
    /// Isabelle/Pure; soundness is the standard "if p and q are
    /// equal in the meta-logic and p is a theorem, so is q."
    ///
    /// Together with `cong_app`/`cong_abs` it makes Pure's `Eq` a true
    /// propositional equality.
    pub fn eq_mp(self, p_thm: Thm) -> Result<Thm> {
        let TermKind::Eq(p, q) = self.concl.kind() else {
            return Err(Error::NotMetaEq(format!("{}", self.concl)));
        };
        if *p != p_thm.concl {
            return Err(Error::ImpAntecedentMismatch {
                expected: format!("{}", p),
                got: format!("{}", p_thm.concl),
            });
        }
        let concl = q.clone();
        let hyps = union_hyps(&self.hyps, &p_thm.hyps);
        Self::build(hyps, concl)
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

    /// Introduce a fresh subtype τ ≤ α witnessed by a predicate `P`.
    ///
    /// Given a witness theorem `Γ ⊢ P x` for some `x : α` and
    /// `P : α → prop`, allocate a fresh type constructor and two
    /// fresh constants `abs : α → τ`, `rep : τ → α`, returning a
    /// [`TypeDef`] bundle of:
    ///
    /// - `tau`: the new type, parameterised by the free type variables
    ///   of α (so `inst_tfree` propagates correctly).
    /// - `abs`, `rep`: the bijection constants (Obs leaves; their Arc
    ///   identity ties them to this typedef).
    /// - `abs_rep`:    `Γ ⊢ ⋀a:τ. abs (rep a) ≡ a`
    /// - `rep_abs_fwd`: `Γ ⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r`
    /// - `rep_abs_back`: `Γ ⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r`
    ///
    /// The witness's hypotheses are propagated to all three returned
    /// theorems — matching HOL Light's discipline. Use the disjunct
    /// trick at the HOL layer (`Q := λx. P x ∨ x = ε P`) if you want
    /// to avoid the inhabitedness obligation.
    ///
    /// ## Soundness
    ///
    /// The fresh `tau`, `abs`, `rep` are interpreted in any model by
    /// fixing τ as a subset of α witnessed by the equivalence
    /// `P r ↔ rep (abs r) = r`. The witness theorem certifies that
    /// the subset is non-empty (so τ is inhabited) — without it the
    /// degenerate case is logically vacuous but the rule still
    /// admits a model (τ singleton at the canonical witness).
    pub fn new_type_definition(
        hint: impl Into<BinderHint>,
        abs_hint: impl Into<BinderHint>,
        rep_hint: impl Into<BinderHint>,
        witness: Thm,
    ) -> Result<TypeDef> {
        // 1. Decompose witness's concl as `P x` (an application).
        let TermKind::App(p, x) = witness.concl.kind() else {
            return Err(Error::BadTypeDefWitness(format!("{}", witness.concl)));
        };
        let p = p.clone();
        let x = x.clone();

        // 2. Read α from x's type.
        let alpha = x.type_of()?;

        // 3. Validate P : α → prop.
        let p_ty = p.type_of()?;
        let TypeKind::Fun(p_dom, p_cod) = p_ty.kind() else {
            return Err(Error::NotFunction(p_ty));
        };
        if *p_dom != alpha {
            return Err(Error::TypeMismatch {
                expected: alpha.clone(),
                got: p_dom.clone(),
            });
        }
        if !p_cod.is_prop() {
            return Err(Error::NotProp(p_cod.clone()));
        }

        // 4. Compute the type-variable arity from α's free TFrees.
        //    τ becomes parametric in those tvars (in canonical order),
        //    so `inst_tfree` after typedef substitutes inside τ's args.
        let tvar_names = alpha.free_tvars();
        let tvar_types: Vec<Type> = tvar_names.iter().map(|n| Type::tfree(n.clone())).collect();

        // 5. Allocate ONE fresh marker tying the typedef + abs + rep
        //    together via Arc identity. The marker is a kernel-private
        //    zero-sized struct with no methods, so user code can never
        //    forge or equate it across calls.
        let marker = TypeDefMarker::new();
        let tau = Type::tycon_obs(marker.clone(), hint.into(), tvar_types);

        // 6. Build abs and rep as Obs leaves wrapping per-role markers
        //    that carry a reference to the shared typedef marker. This
        //    gives abs and rep their own Arc identities while keeping
        //    them tied to the typedef.
        let abs_marker = TypeDefAbsMarker::new(&marker, abs_hint.into());
        let rep_marker = TypeDefRepMarker::new(&marker, rep_hint.into());
        let abs_ty = Type::fun(alpha.clone(), tau.clone());
        let rep_ty = Type::fun(tau.clone(), alpha.clone());
        let abs = Term::obs(abs_marker, abs_ty);
        let rep = Term::obs(rep_marker, rep_ty);

        // 7. Build the three bijection theorems.
        //
        //    abs_rep: ⋀a:τ. abs (rep a) ≡ a
        let bound0 = Term::bound(0);
        let abs_rep_body = Term::eq(
            Term::app(abs.clone(), Term::app(rep.clone(), bound0.clone())),
            bound0.clone(),
        );
        let abs_rep_concl = Term::all(BinderHint::new("a"), tau.clone(), abs_rep_body);

        //    rep_abs_eq : (rep (abs r) ≡ r)   (with r=bound 0)
        //    p_at_bound : P r
        let p_at_bound = Term::app(p, bound0.clone());
        let rep_abs_eq = Term::eq(
            Term::app(rep.clone(), Term::app(abs.clone(), bound0)),
            Term::bound(0),
        );
        //    fwd: ⋀r:α. P r ⟹ rep (abs r) ≡ r
        let fwd_concl = Term::all(
            BinderHint::new("r"),
            alpha.clone(),
            Term::imp(p_at_bound.clone(), rep_abs_eq.clone()),
        );
        //    back: ⋀r:α. rep (abs r) ≡ r ⟹ P r
        let back_concl = Term::all(
            BinderHint::new("r"),
            alpha,
            Term::imp(rep_abs_eq, p_at_bound),
        );

        // 8. Propagate witness's hyps to each emitted theorem — every
        //    fact about the new typedef depends on the witness's
        //    inhabitedness justification.
        let hyps: BTreeSet<Term> = (*witness.hyps).clone();
        let abs_rep = Self::build(hyps.clone(), abs_rep_concl)?;
        let rep_abs_fwd = Self::build(hyps.clone(), fwd_concl)?;
        let rep_abs_back = Self::build(hyps, back_concl)?;

        Ok(TypeDef {
            tau,
            abs,
            rep,
            abs_rep,
            rep_abs_fwd,
            rep_abs_back,
            tvars: tvar_names,
        })
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
    /// The `name` is display-only (an α-transparent [`BinderHint`]). The
    /// `body` must be a valid Pure term (typeable in isolation).
    ///
    /// ## Soundness
    ///
    /// Sound because the resulting `Def` is a brand-new symbol whose
    /// only equation says it equals `body`. In any model satisfying
    /// the prior theory, we extend by interpreting this `Def` as
    /// `⟦body⟧` — a conservative extension. No global signature is
    /// needed because the allocator gives us uniqueness per call.
    pub fn define(name: impl Into<BinderHint>, body: Term) -> Result<Thm> {
        let body_type = body.type_of()?;
        // Soundness check (Isabelle/Pure parity): no "phantom"
        // tvars — every free tvar appearing inside any type
        // annotation in `body` must also appear in `body_type`.
        // Without this, a phantom tvar inside `body` would be
        // invisible to `instance_type`, so `subst_tfree_in_term`
        // could leave a `Def` whose body still mentions the
        // phantom tvar at the original type — inconsistent with
        // the `Def ≡ body` equation it stands for.
        let type_tvars: std::collections::BTreeSet<smol_str::SmolStr> =
            body_type.free_tvars().into_iter().collect();
        let mut body_tvars = std::collections::BTreeSet::new();
        crate::subst::collect_term_tvars(&body, &mut body_tvars);
        for tv in &body_tvars {
            if !type_tvars.contains(tv) {
                return Err(crate::error::Error::DefPhantomTFree {
                    tvar: tv.clone(),
                    body_type,
                });
            }
        }
        let d = Def::new_internal(name.into(), body.clone(), body_type);
        let concl = Term::eq(Term::def(d), body);
        Self::build(BTreeSet::new(), concl)
    }

    /// Single-step computation rule on builtin primitives applied to
    /// concrete literal arguments. Returns `⊢ t ≡ result` where
    /// `result` is the canonical value of evaluating the operation;
    /// returns an `Err(NotReducible)` for terms that aren't a
    /// primitive-application with all-literal arguments (the rule is
    /// deliberately conservative — it doesn't reduce subterms or
    /// follow β/δ chains).
    ///
    /// **Catalogue**:
    ///
    /// - `App(Prim(NatArith Succ), NatLit a)` → `NatLit(a + 1)`
    /// - `App(Prim(NatArith Pred), NatLit a)` → `NatLit(a − 1)` saturating at 0
    /// - `App(App(Prim(NatArith Add), NatLit a), NatLit b)` → `NatLit(a + b)`
    /// - similarly for `Mul`, `Sub` (saturating), `Div` (`a/0 = 0`), `Mod` (`a%0 = 0`)
    /// - `App(Prim(IntArith Succ/Pred), IntLit a)` → `IntLit(a ± 1)`
    /// - `App(Prim(IntNeg), IntLit a)` → `IntLit(−a)`
    /// - `App(App(Prim(IntArith *), IntLit a), IntLit b)` for each binop
    /// - `App(App(Prim(BytesCat), Blob a), Blob b)` → `Blob(a ++ b)`
    /// - `App(App(Prim(BytesConsNat), NatLit n), Blob b)` → `Blob([n%256, ...b])`
    /// - `App(Prim(BytesLen), Blob b)` → `NatLit(b.len())`
    /// - `App(App(Prim(BytesAt), Blob b), NatLit i)` → `NatLit(b[i] or 0)`
    /// - `App(App(App(Prim(BytesSlice), Blob b), NatLit start), NatLit len)`
    ///   → `Blob(b[start..min(start+len, b.len())])`
    /// - `App(Prim(NatToInt), NatLit n)` → `IntLit(n)`
    pub fn reduce_prim(t: Term) -> Result<Thm> {
        let reduced = builtins::reduce_prim_term(&t).ok_or(Error::NotReducible)?;
        Self::build(BTreeSet::new(), Term::eq(t, reduced))
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
    /// `⊢ expr`, where:
    /// - `expr` decomposes as `(obs head)(arg1)(arg2)…` with an `Obs`
    ///   leaf at the head and zero or more applications.
    /// - the head observer downcasts to Rust type `O`.
    /// - `expr` has final Pure type `prop`.
    /// - `O::obs_true(args, hint)` returns `true`.
    ///
    /// ## Soundness
    ///
    /// The rule is **unconditionally sound** regardless of what
    /// `O::obs_true` returns. The standard ε-interpretation of any
    /// observation whose result type is `prop` maps it to `⊤`, so
    /// every `(obs O) args` of type `prop` is already true in the
    /// model. Per-`O` ε-families means a policy choice in `WasmObs`
    /// can't affect equations or assertions involving `HolLight`.
    ///
    /// `hint` is the same opaque pass-through as on `obs_eq`.
    pub fn obs_true<O: ObsTrue>(
        expr: Term,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
        let (obs, args) = decompose_obs_app(&expr)?;
        let o = obs.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty = expr.type_of()?;
        if !ty.is_prop() {
            return Err(Error::NotProp(ty));
        }
        if !o.obs_true(&args, hint.as_deref().map(|h| h)) {
            return Err(Error::ObsEqRefused);
        }
        Self::build(BTreeSet::new(), expr)
    }

    /// `⊢ hyps[0] ⟹ hyps[1] ⟹ … ⟹ hyps[n] ⟹ expr` — a **lazy
    /// theorem** declared by the observer policy. Used to encode
    /// HOL-style derivation rules as reusable implications: callers
    /// then chain `imp_elim` with concrete source theorems to get the
    /// specialised result.
    ///
    /// Validates:
    /// - `expr` decomposes as `(obs head)(arg1)(arg2)…`.
    /// - the head observer downcasts to `O`.
    /// - `expr` has final type `prop`.
    /// - every hyp has type `prop`.
    /// - `O::obs_imp(args, hyps, hint)` returns `true`.
    ///
    /// ## Soundness
    ///
    /// Strictly weaker than [`Thm::obs_true`]. Any chain of
    /// implications ending in a prop-typed obs application is sound to
    /// assert under the same parametric-ε model that makes `obs_true`
    /// sound. Per-`O` ε-families means a policy bug in `MyObs` can't
    /// touch implications about `HolLight`.
    pub fn obs_imp<O: ObsImp>(
        expr: Term,
        hyps: Vec<Term>,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
        let (obs, args) = decompose_obs_app(&expr)?;
        let o = obs.downcast::<O>().ok_or(Error::ObsDowncastTypeMismatch)?;
        let ty = expr.type_of()?;
        if !ty.is_prop() {
            return Err(Error::NotProp(ty));
        }
        for h in &hyps {
            let h_ty = h.type_of()?;
            if !h_ty.is_prop() {
                return Err(Error::NotProp(h_ty));
            }
        }
        if !o.obs_imp(&args, &hyps, hint.as_deref()) {
            return Err(Error::ObsEqRefused);
        }
        // Build hyp[0] ⟹ hyp[1] ⟹ ... ⟹ expr (right-associative).
        let mut result = expr;
        for h in hyps.into_iter().rev() {
            result = Term::imp(h, result);
        }
        Self::build(BTreeSet::new(), result)
    }

    pub fn obs_eq<O: ObsEq>(
        expr1: Term,
        expr2: Term,
        hint: Option<Arc<dyn crate::term::Hint>>,
    ) -> Result<Thm> {
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
        if !o1.obs_eq(o2, &args1, &args2, hint.as_deref()) {
            return Err(Error::ObsEqRefused);
        }
        let concl = Term::eq(expr1, expr2);
        Self::build(BTreeSet::new(), concl)
    }
}

/// Walk down through `App`s collecting arguments left-to-right. If
/// the final node is an `Obs` leaf, return its observer and the args
/// list; otherwise return an error.
fn decompose_obs_app(t: &Term) -> Result<(&Object, Vec<Term>)> {
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

// ============================================================================
// new_type_definition — result bundle and private markers
// ============================================================================

/// Result of [`Thm::new_type_definition`]: the fresh subtype τ along
/// with its abs/rep bijection constants and the three theorems that
/// witness the bijection. All three theorems carry the witness's
/// hypotheses.
#[derive(Clone, Debug)]
pub struct TypeDef {
    /// The freshly-introduced type. `TyConObs` carrying a marker Arc
    /// shared by `abs` and `rep`. Parametric in `tvars` (in canonical
    /// order, so `inst_tfree` propagates correctly).
    pub tau: Type,
    /// The fresh `abs : α → τ` constant. An `Obs` leaf whose marker
    /// references the typedef.
    pub abs: Term,
    /// The fresh `rep : τ → α` constant.
    pub rep: Term,
    /// `⊢ ⋀a:τ. abs (rep a) ≡ a`.
    pub abs_rep: Thm,
    /// `⊢ ⋀r:α. P r ⟹ rep (abs r) ≡ r`.
    pub rep_abs_fwd: Thm,
    /// `⊢ ⋀r:α. rep (abs r) ≡ r ⟹ P r`.
    pub rep_abs_back: Thm,
    /// Sorted list of type-variable names that appear in α. τ is
    /// parametric in exactly these tvars (positionally, in this order).
    pub tvars: Vec<smol_str::SmolStr>,
}

/// Private marker carried inside a `TypeDef`'s `Type::tycon_obs` and
/// (via the abs/rep markers below) inside its abs/rep `Term::obs`
/// leaves. Zero-sized, no methods — its sole purpose is to provide
/// fresh `Arc` identity per `new_type_definition` call. Cannot be
/// constructed outside this module.
#[derive(Debug, Clone)]
struct TypeDefMarker(Arc<TypeDefMarkerInner>);

#[derive(Debug)]
struct TypeDefMarkerInner;

impl TypeDefMarker {
    fn new() -> Self { TypeDefMarker(Arc::new(TypeDefMarkerInner)) }
}

/// Marker carried by a typedef's `abs` constant. Holds an Arc to the
/// shared typedef marker so it's uniquely tied to the typedef, plus
/// a display hint for pretty-printing.
struct TypeDefAbsMarker {
    #[allow(dead_code)]
    typedef: Arc<TypeDefMarkerInner>,
    hint: BinderHint,
}

impl TypeDefAbsMarker {
    fn new(m: &TypeDefMarker, hint: BinderHint) -> Self {
        TypeDefAbsMarker { typedef: Arc::clone(&m.0), hint }
    }
}

impl fmt::Debug for TypeDefAbsMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hint.is_empty() {
            write!(f, "abs")
        } else {
            write!(f, "{}", self.hint)
        }
    }
}

/// Marker for the typedef's `rep` constant.
struct TypeDefRepMarker {
    #[allow(dead_code)]
    typedef: Arc<TypeDefMarkerInner>,
    hint: BinderHint,
}

impl TypeDefRepMarker {
    fn new(m: &TypeDefMarker, hint: BinderHint) -> Self {
        TypeDefRepMarker { typedef: Arc::clone(&m.0), hint }
    }
}

impl fmt::Debug for TypeDefRepMarker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.hint.is_empty() {
            write!(f, "rep")
        } else {
            write!(f, "{}", self.hint)
        }
    }
}
