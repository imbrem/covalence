//! The **impredicative (Church-encoding) HOL backend** for the
//! inductive-types API — generalizes what [`crate::init::sexpr`] /
//! [`crate::init::tree`] / [`crate::init::prop`] hand-roll, and adds the
//! well-formedness predicate + genuine (membership-relativized) induction
//! those modules defer.
//!
//! ## The realization
//!
//! For a spec with constructors `Cᵢ : A₁ → … → Aₖ → T`, the carrier is the
//! rank-1 fold type over a fresh result type variable `'r`:
//!
//! ```text
//!   T⟨'r⟩ := H₁ → … → Hₙ → 'r        Hᵢ := B₁ → … → Bₖ → 'r
//!                                     (Bⱼ = 'r at Rec, the sort at Ext)
//! ```
//!
//! - **Constructors** are closed λ constants folding their arguments'
//!   folds into the matching handler.
//! - **Recursion is application**: `rec steps t = t[β] steps`, so the
//!   computation laws are pure β (`prove_beta_eq`, β-nf both sides).
//! - **Membership** is the impredicative least fixpoint
//!   `Wf := λs. ∀d. Closed d ⟹ d s` (the [`crate::init::prop`]
//!   `Derivable_…` shape), with `Closed d` the conjunction of one
//!   constructor-closure clause per `Cᵢ`.
//! - **Induction** is one `∀`-elimination of `d := motive` against `Wf` —
//!   the whole point of the encoding.
//! - **Freeness by observation**: distinctness via boolean tag folds at
//!   the observation instance `'r := bool`; injectivity at *external*
//!   positions via projection folds at `'r := ` the payload type (the
//!   [`crate::init::tree`] `leaf_inj` pattern).
//!
//! ## The honest limitation (recorded capability)
//!
//! Injectivity at **recursive** argument positions is *not derivable* for
//! a rank-1 Church encoding: recovering a subtree from a fold needs a
//! reconstruction fold whose result type is the carrier itself — a
//! statement that cannot even be ∀-quantified at rank 1 (the same wall
//! `tree::branch_inj` documents; at a collapsing instance of `'r` the
//! statement is false, so no polymorphic proof exists). The bundle
//! reports `rec_injective: false` and returns
//! [`InductiveError::Unsupported`]; exact-type backends (the recursion
//! engine) supply it instead.
//!
//! ## Reserved names
//!
//! Argument binder hints must avoid the backend's internal names (the
//! handler names, `d`, the `'r` type variable, and `__`-prefixed names);
//! external sorts and recursor result types must not mention `'r`.
//! [`ImpredicativeBackend::realize`] validates all of this up front.

use covalence_core::{Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_inductive::{
    ArgSort, BackendCaps, IndResult, InductiveBackend, InductiveError, InductiveFacts,
    InductiveSpec, InductiveTheory,
};
use smol_str::SmolStr;

use super::api::{derive_cases_native, internal, project_conj, prove_beta_eq};
use super::hol::NativeHol;
use super::util::and_all;
use crate::init::eq::{beta_expand, beta_nf, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::logic::truth;

/// The impredicative/Church backend. Realizes **any** valid v1 spec.
#[derive(Clone, Debug)]
pub struct ImpredicativeBackend {
    /// The fresh result-type variable name (default `"r"`).
    rvar: SmolStr,
    /// Per-constructor handler binder names (default `"f_" + name`).
    handler_names: Option<Vec<SmolStr>>,
}

impl Default for ImpredicativeBackend {
    fn default() -> Self {
        ImpredicativeBackend {
            rvar: SmolStr::new("r"),
            handler_names: None,
        }
    }
}

impl ImpredicativeBackend {
    pub fn new() -> Self {
        Self::default()
    }

    /// Override the handler binder names (one per constructor, in order) —
    /// used to reproduce hand-rolled encodings exactly (e.g.
    /// [`crate::init::sexpr`]'s `fa`/`fn_`/`fc`).
    pub fn with_handler_names(
        mut self,
        names: impl IntoIterator<Item = impl Into<SmolStr>>,
    ) -> Self {
        self.handler_names = Some(names.into_iter().map(Into::into).collect());
        self
    }
}

impl InductiveBackend<NativeHol> for ImpredicativeBackend {
    fn realize(
        &self,
        _logic: &NativeHol,
        spec: &InductiveSpec<Type>,
    ) -> IndResult<InductiveTheory<NativeHol>, NativeHol> {
        spec.validate().map_err(InductiveError::spec)?;
        let handlers: Vec<SmolStr> = match &self.handler_names {
            Some(names) => {
                if names.len() != spec.arity() {
                    return Err(InductiveError::Arity {
                        what: "handler names",
                        expected: spec.arity(),
                        got: names.len(),
                    });
                }
                names.clone()
            }
            None => spec
                .ctors
                .iter()
                .map(|c| SmolStr::new(format!("f_{}", c.name)))
                .collect(),
        };
        // Hygiene validation: handler names distinct; binder hints avoid
        // handler names, `d`, and `__`-prefixed internals; external sorts
        // avoid the result type variable.
        for (i, h) in handlers.iter().enumerate() {
            if handlers[..i].contains(h) {
                return Err(InductiveError::Unsupported {
                    what: "handler names",
                    why: format!("duplicate handler name `{h}`"),
                });
            }
        }
        let reserved = |n: &str| n == "d" || n.starts_with("__") || handlers.iter().any(|h| h == n);
        for c in &spec.ctors {
            for (n, sort) in &c.args {
                if reserved(n) {
                    return Err(InductiveError::Unsupported {
                        what: "argument binder hint",
                        why: format!("`{n}` collides with a backend-internal name"),
                    });
                }
                if let ArgSort::Ext(ty) = sort
                    && contains_rvar(ty, &self.rvar)
                {
                    return Err(InductiveError::Unsupported {
                        what: "external sort",
                        why: format!(
                            "type `{ty}` mentions the backend's result type variable `'{}`",
                            self.rvar
                        ),
                    });
                }
            }
        }

        let th = ChurchTheory::build(spec.clone(), self.rvar.clone(), handlers)?;
        Ok(InductiveTheory {
            spec: spec.clone(),
            ty: th.carrier.clone(),
            mem: th.wf.clone(),
            ctors: th.ctor_fns.clone(),
            facts: Box::new(th),
        })
    }
}

/// Whether `ty` mentions the free type variable `rvar`.
fn contains_rvar(ty: &Type, rvar: &str) -> bool {
    // A substitution probe: if replacing `'rvar` changes the type, it
    // occurs. (`bool` can never equal a `tfree`.)
    subst::subst_tfree_in_type(ty, rvar, &Type::bool()) != *ty
}

/// A realized Church bundle (also the [`InductiveFacts`] impl).
struct ChurchTheory {
    spec: InductiveSpec<Type>,
    rvar: SmolStr,
    handlers: Vec<SmolStr>,
    /// `T⟨'r⟩ = H₁ → … → Hₙ → 'r`.
    carrier: Type,
    /// The constructor closed-λ constants, spec order.
    ctor_fns: Vec<Term>,
    /// `Wf : T⟨'r⟩ → bool`.
    wf: Term,
}

impl ChurchTheory {
    fn build(
        spec: InductiveSpec<Type>,
        rvar: SmolStr,
        handlers: Vec<SmolStr>,
    ) -> IndResult<Self, NativeHol> {
        let mut th = ChurchTheory {
            spec,
            rvar,
            handlers,
            carrier: Type::bool(), // placeholder
            ctor_fns: Vec::new(),
            wf: covalence_hol_eval::mk_bool(true), // placeholder
        };
        th.carrier = th.carrier_ty();
        th.ctor_fns = (0..th.spec.arity())
            .map(|i| th.ctor_fn(i))
            .collect::<Result<_>>()?;
        th.wf = th.wf_term()?;
        Ok(th)
    }

    fn rty(&self) -> Type {
        Type::tfree(self.rvar.as_str())
    }

    /// The type of argument `j` of constructor `i`, with recursive slots
    /// at `rec`.
    fn arg_ty(&self, sort: &ArgSort<Type>, rec: &Type) -> Type {
        match sort {
            ArgSort::Rec => rec.clone(),
            ArgSort::Ext(ty) => ty.clone(),
        }
    }

    /// `Hᵢ = B₁ → … → Bₖ → 'r` (recursive slots at `'r`).
    fn handler_ty(&self, i: usize) -> Type {
        let mut ty = self.rty();
        for (_, sort) in self.spec.ctors[i].args.iter().rev() {
            ty = Type::fun(self.arg_ty(sort, &self.rty()), ty);
        }
        ty
    }

    /// `T⟨'r⟩ = H₁ → … → Hₙ → 'r`.
    fn carrier_ty(&self) -> Type {
        let mut ty = self.rty();
        for i in (0..self.spec.arity()).rev() {
            ty = Type::fun(self.handler_ty(i), ty);
        }
        ty
    }

    fn handler_var(&self, i: usize) -> Term {
        Term::free(self.handlers[i].as_str(), self.handler_ty(i))
    }

    /// Wrap a fold body in the handler abstractions (all of them, in
    /// order) → a term of the carrier type.
    fn close_handlers(&self, body: Term) -> Term {
        let mut t = body;
        for i in (0..self.spec.arity()).rev() {
            t = Term::abs(
                self.handler_ty(i),
                subst::close(&t, self.handlers[i].as_str()),
            );
        }
        t
    }

    /// The fold of a carrier term: `x h₁ … hₙ : 'r` (handler variables
    /// free — used under [`close_handlers`]).
    fn fold_of(&self, x: Term) -> Result<Term> {
        let mut t = x;
        for i in 0..self.spec.arity() {
            t = t.apply(self.handler_var(i))?;
        }
        Ok(t)
    }

    /// The constructor as a closed λ constant
    /// `λx₁…xₖ. λh₁…hₙ. hᵢ v₁ … vₖ` (`vⱼ` the raw argument at `Ext`, its
    /// fold at `Rec`).
    fn ctor_fn(&self, i: usize) -> Result<Term> {
        let c = &self.spec.ctors[i];
        let args: Vec<(SmolStr, Type)> = c
            .args
            .iter()
            .map(|(n, s)| (n.clone(), self.arg_ty(s, &self.carrier)))
            .collect();
        let mut body = self.handler_var(i);
        for ((n, ty), (_, sort)) in args.iter().zip(&c.args) {
            let v = Term::free(n.as_str(), ty.clone());
            let v = match sort {
                ArgSort::Rec => self.fold_of(v)?,
                ArgSort::Ext(_) => v,
            };
            body = body.apply(v)?;
        }
        let mut t = self.close_handlers(body);
        for (n, ty) in args.iter().rev() {
            t = Term::abs(ty.clone(), subst::close(&t, n.as_str()));
        }
        Ok(t)
    }

    /// `Cᵢ x⃗` in applied form.
    fn ctor_app(&self, i: usize, args: &[Term]) -> IndResult<Term, NativeHol> {
        let c = &self.spec.ctors[i];
        if args.len() != c.arity() {
            return Err(InductiveError::Arity {
                what: "constructor arguments",
                expected: c.arity(),
                got: args.len(),
            });
        }
        let mut t = self.ctor_fns[i].clone();
        for a in args {
            t = t.apply(a.clone())?;
        }
        Ok(t)
    }

    /// Fresh argument variables for constructor `i`, named by hints.
    fn arg_vars(&self, i: usize) -> Vec<Term> {
        self.spec.ctors[i]
            .args
            .iter()
            .map(|(n, s)| Term::free(n.as_str(), self.arg_ty(s, &self.carrier)))
            .collect()
    }

    /// The closure clause for constructor `i` under the predicate `d`:
    /// `∀x⃗. d r₁ ⟹ … ⟹ d rₘ ⟹ d (Cᵢ x⃗)`.
    fn clause(&self, d: &Term, i: usize) -> IndResult<Term, NativeHol> {
        let c = &self.spec.ctors[i];
        let args = self.arg_vars(i);
        let mut body = d.clone().apply(self.ctor_app(i, &args)?)?;
        for k in c.rec_positions().collect::<Vec<_>>().into_iter().rev() {
            body = d.clone().apply(args[k].clone())?.imp(body)?;
        }
        for ((n, s), _) in c.args.iter().zip(&args).rev() {
            body = body.forall(n.as_str(), self.arg_ty(s, &self.carrier))?;
        }
        Ok(body)
    }

    /// `Closed d` — the right-associated conjunction of the clauses.
    fn closed_term(&self, d: &Term) -> IndResult<Term, NativeHol> {
        let mut t = self.clause(d, self.spec.arity() - 1)?;
        for i in (0..self.spec.arity() - 1).rev() {
            t = self.clause(d, i)?.and(t)?;
        }
        Ok(t)
    }

    fn d_ty(&self) -> Type {
        Type::fun(self.carrier.clone(), Type::bool())
    }

    /// `Wf := λs. ∀d. Closed d ⟹ d s`.
    fn wf_term(&self) -> IndResult<Term, NativeHol> {
        let d = Term::free("d", self.d_ty());
        let s = Term::free("__wf_s", self.carrier.clone());
        let body = self
            .closed_term(&d)?
            .imp(d.apply(s.clone())?)?
            .forall("d", self.d_ty())?;
        Ok(Term::abs(
            self.carrier.clone(),
            subst::close(&body, "__wf_s"),
        ))
    }

    /// Reinstantiate a term's carrier `'r := r` (the observation trick).
    fn at_r(&self, t: &Term, r: &Type) -> Term {
        subst::subst_tfree_in_term(t, self.rvar.as_str(), r)
    }

    /// The fold result type read off the steps (peel `arity(0)` arrows
    /// off `steps[0]`'s type).
    fn result_ty(&self, steps: &[Term]) -> IndResult<Type, NativeHol> {
        if steps.len() != self.spec.arity() {
            return Err(InductiveError::Arity {
                what: "recursor steps",
                expected: self.spec.arity(),
                got: steps.len(),
            });
        }
        let mut ty = steps[0].type_of()?;
        for _ in 0..self.spec.ctors[0].arity() {
            match ty.kind().clone() {
                covalence_core::TypeKind::Fun(_, cod) => ty = cod,
                _ => {
                    return internal(format!("recursor step 0 has non-function type `{ty}`"));
                }
            }
        }
        if contains_rvar(&ty, &self.rvar) {
            return Err(InductiveError::Unsupported {
                what: "recursor result type",
                why: format!(
                    "`{ty}` mentions the backend's result type variable `'{}`",
                    self.rvar
                ),
            });
        }
        Ok(ty)
    }

    /// Boolean tag handlers: `hᵢ = λ… T`, `h_c = λ… F` for `c ≠ i`, at the
    /// observation instance `'r := bool`.
    fn tag_handlers(&self, i: usize) -> Vec<Term> {
        (0..self.spec.arity())
            .map(|c| {
                let mut t = covalence_hol_eval::mk_bool(c == i);
                for (_, sort) in self.spec.ctors[c].args.iter().rev() {
                    t = Term::abs(self.arg_ty(sort, &Type::bool()), t);
                }
                t
            })
            .collect()
    }

    /// Observe an assumed constructor equation through a fold: chain
    /// `cong_fn` over the handlers and β-normalise both sides, returning
    /// `{H} ⊢ nfL = nfR`.
    fn observe(&self, assumed: Thm, hs: &[Term]) -> IndResult<Thm, NativeHol> {
        let mut cong = assumed;
        for h in hs {
            cong = cong.cong_fn(h.clone())?;
        }
        let Some((l, r)) = cong.concl().as_eq() else {
            return internal("observe: congruence did not yield an equation");
        };
        let (l, r) = (l.clone(), r.clone());
        let lnf = beta_nf(l); // ⊢ lhs = nfL
        let rnf = beta_nf(r); // ⊢ rhs = nfR
        Ok(lnf.sym()?.trans(cong)?.trans(rnf)?)
    }
}

impl InductiveFacts<NativeHol> for ChurchTheory {
    fn rec_app(&self, steps: &[Term], t: &Term) -> IndResult<Term, NativeHol> {
        let beta = self.result_ty(steps)?;
        let mut r = self.at_r(t, &beta);
        for s in steps {
            r = r.apply(s.clone())?;
        }
        Ok(r)
    }

    fn comp(&self, steps: &[Term], i: usize) -> IndResult<Thm, NativeHol> {
        let c = self.spec.ctors.get(i).ok_or(InductiveError::CtorIndex {
            index: i,
            arity: self.spec.arity(),
        })?;
        let beta = self.result_ty(steps)?;
        let args = self.arg_vars(i);
        let lhs = self.rec_app(steps, &self.ctor_app(i, &args)?)?;
        // RHS: stepᵢ applied to raw externals and `rec`-images.
        let mut rhs = steps[i].clone();
        for (a, (_, sort)) in args.iter().zip(&c.args) {
            let v = match sort {
                ArgSort::Rec => self.rec_app(steps, a)?,
                ArgSort::Ext(_) => a.clone(),
            };
            rhs = rhs.apply(v)?;
        }
        let mut thm = prove_beta_eq(lhs, rhs)?;
        // ∀-close over the (instantiated) constructor arguments.
        let carrier_at = subst::subst_tfree_in_type(&self.carrier, self.rvar.as_str(), &beta);
        for (n, sort) in c.args.iter().rev() {
            thm = thm.all_intro(n.as_str(), self.arg_ty(sort, &carrier_at))?;
        }
        Ok(thm)
    }

    fn injective(&self, i: usize, k: usize, xs: &[Term], ys: &[Term]) -> IndResult<Thm, NativeHol> {
        let c = self.spec.ctors.get(i).ok_or(InductiveError::CtorIndex {
            index: i,
            arity: self.spec.arity(),
        })?;
        let (_, sort) = c.args.get(k).ok_or(InductiveError::ArgIndex {
            ctor: c.name.clone(),
            index: k,
            arity: c.arity(),
        })?;
        let obs = match sort {
            ArgSort::Ext(ty) => ty.clone(),
            ArgSort::Rec => {
                return Err(InductiveError::Unsupported {
                    what: "injectivity at a recursive argument position",
                    why: "a rank-1 Church encoding cannot recover subtrees from folds \
                          (the tree::branch_inj wall); use an exact-type backend"
                        .into(),
                });
            }
        };
        if xs.len() != c.arity() || ys.len() != c.arity() {
            return Err(InductiveError::Arity {
                what: "injectivity argument tuples",
                expected: c.arity(),
                got: xs.len().max(ys.len()),
            });
        }
        // Handlers at `'r := obs`: hᵢ projects slot k, others yield an
        // arbitrary (ε-chosen) element of `obs`.
        let arb = Term::app(
            Term::select_op(obs.clone()),
            Term::abs(obs.clone(), covalence_hol_eval::mk_bool(true)),
        );
        let hs: Vec<Term> = (0..self.spec.arity())
            .map(|cc| {
                let cargs = &self.spec.ctors[cc].args;
                // hᵢ = λp₁…pₖ. p_k (slot k bound by a marker); other
                // handlers ignore their arguments and yield `arb`.
                let mut t = if cc == i {
                    Term::free("__inj_pk", obs.clone())
                } else {
                    arb.clone()
                };
                for (jj, (_, sort)) in cargs.iter().enumerate().rev() {
                    let ty = self.arg_ty(sort, &obs);
                    if cc == i && jj == k {
                        t = Term::abs(ty, subst::close(&t, "__inj_pk"));
                    } else {
                        t = Term::abs(ty, t);
                    }
                }
                t
            })
            .collect();

        let lhs = self.at_r(&self.ctor_app(i, xs)?, &obs);
        let rhs = self.at_r(&self.ctor_app(i, ys)?, &obs);
        let eq = lhs.equals(rhs)?;
        let assumed = Thm::assume(eq.clone())?;
        let core = self.observe(assumed, &hs)?; // {H} ⊢ nf(xₖ) = nf(yₖ)
        // Bridge back to the given argument terms.
        let xk = beta_nf(xs[k].clone()); // ⊢ xₖ = nf(xₖ)
        let yk = beta_nf(ys[k].clone()); // ⊢ yₖ = nf(yₖ)
        Ok(xk.trans(core)?.trans(yk.sym()?)?.imp_intro(&eq)?)
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> IndResult<Thm, NativeHol> {
        let n = self.spec.arity();
        if i >= n || j >= n {
            return Err(InductiveError::CtorIndex {
                index: i.max(j),
                arity: n,
            });
        }
        if i == j {
            return Err(InductiveError::Unsupported {
                what: "distinctness",
                why: "constructor indices must differ".into(),
            });
        }
        let bool_ty = Type::bool();
        let hs = self.tag_handlers(i);
        let lhs = self.at_r(&self.ctor_app(i, xs)?, &bool_ty);
        let rhs = self.at_r(&self.ctor_app(j, ys)?, &bool_ty);
        let eq = lhs.equals(rhs)?;
        let assumed = Thm::assume(eq.clone())?;
        let core = self.observe(assumed, &hs)?; // {H} ⊢ T = F
        let Some((l, r)) = core.concl().as_eq() else {
            return internal("distinct: observation did not yield an equation");
        };
        if *l != covalence_hol_eval::mk_bool(true) || *r != covalence_hol_eval::mk_bool(false) {
            return internal(format!("distinct: tag fold yielded `{l} = {r}`"));
        }
        // {H} ⊢ F, discharge.
        Ok(core.eq_mp(truth())?.imp_intro(&eq)?)
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> IndResult<Thm, NativeHol> {
        let n = self.spec.arity();
        if cases.len() != n {
            return Err(InductiveError::Arity {
                what: "induction cases",
                expected: n,
                got: cases.len(),
            });
        }
        // Assemble `⊢ Closed motive` from the case proofs.
        let mut clauses = Vec::with_capacity(n);
        for (i, case) in cases.into_iter().enumerate() {
            let mut t = case;
            for (nm, sort) in self.spec.ctors[i].args.iter().rev() {
                t = t.all_intro(nm.as_str(), self.arg_ty(sort, &self.carrier))?;
            }
            clauses.push(t);
        }
        let closed = and_all(&clauses)?;
        // Unfold `Wf t`, specialise `d := motive`, discharge.
        let tv = Term::free("__wf_t", self.carrier.clone());
        let wf_t = Term::app(self.wf.clone(), tv);
        let unfolded = beta_reduce(Thm::assume(wf_t.clone())?)?; // {Wf t} ⊢ ∀d. Closed d ⟹ d t
        let spec_d = unfolded.all_elim(motive.clone())?;
        let at_t = spec_d.imp_elim(closed)?; // {Wf t} ⊢ motive t
        Ok(at_t
            .imp_intro(&wf_t)?
            .all_intro("__wf_t", self.carrier.clone())?)
    }

    fn cases(&self) -> IndResult<Thm, NativeHol> {
        derive_cases_native(&self.spec, &self.carrier, &self.ctor_fns, &|m, cs| {
            self.induct(m, cs)
        })
    }

    fn mem_ctor(&self, i: usize, args: &[Term], rec_mems: Vec<Thm>) -> IndResult<Thm, NativeHol> {
        let c = self.spec.ctors.get(i).ok_or(InductiveError::CtorIndex {
            index: i,
            arity: self.spec.arity(),
        })?;
        let rec_positions: Vec<usize> = c.rec_positions().collect();
        if args.len() != c.arity() {
            return Err(InductiveError::Arity {
                what: "constructor arguments",
                expected: c.arity(),
                got: args.len(),
            });
        }
        if rec_mems.len() != rec_positions.len() {
            return Err(InductiveError::Arity {
                what: "recursive membership proofs",
                expected: rec_positions.len(),
                got: rec_mems.len(),
            });
        }
        let dv = Term::free("__d", self.d_ty());
        let closed_d = self.closed_term(&dv)?;
        let assumed = Thm::assume(closed_d.clone())?;
        // The clause for `Cᵢ`, specialised at the given arguments.
        let mut thm = project_conj(assumed.clone(), i, self.spec.arity())?;
        for a in args {
            thm = thm.all_elim(a.clone())?;
        }
        // Discharge the recursive antecedents from the membership proofs.
        for (k, rm) in rec_positions.iter().zip(rec_mems) {
            let expected = Term::app(self.wf.clone(), args[*k].clone());
            if *rm.concl() != expected {
                return internal(format!(
                    "mem_ctor: recursive membership proof concludes `{}`, expected `{expected}`",
                    rm.concl()
                ));
            }
            let d_at = beta_reduce(rm)? // ⊢ ∀d. Closed d ⟹ d xₖ
                .all_elim(dv.clone())?
                .imp_elim(assumed.clone())?; // {Closed __d} ⊢ __d xₖ
            thm = thm.imp_elim(d_at)?;
        }
        // {Closed __d} ⊢ __d (Cᵢ x⃗) — discharge, generalise, fold `Wf`.
        let generalized = thm.imp_intro(&closed_d)?.all_intro("__d", self.d_ty())?;
        let target = self.ctor_app(i, args)?;
        Ok(beta_expand(&self.wf, target, generalized)?)
    }

    fn mem_trivial(&self) -> Option<Thm> {
        None
    }

    fn caps(&self) -> BackendCaps {
        BackendCaps {
            mem_trivial: false,
            rec_injective: false,
            prim_rec: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_inductive::conformance;

    fn logic() -> NativeHol {
        NativeHol
    }

    /// `btree := leaf nat | node btree btree` — a second datatype through
    /// the same generic backend (payload + two recursive arguments).
    fn btree_spec() -> InductiveSpec<Type> {
        InductiveSpec::new(
            "btree",
            vec![
                covalence_inductive::CtorSpec::new("leaf", [("n", ArgSort::Ext(Type::nat()))]),
                covalence_inductive::CtorSpec::new(
                    "node",
                    [("l", ArgSort::Rec), ("r_", ArgSort::Rec)],
                ),
            ],
        )
    }

    /// The full conformance suite on `btree` (default handler names).
    #[test]
    fn btree_conformance() {
        let th = ImpredicativeBackend::new()
            .realize(&logic(), &btree_spec())
            .unwrap();
        conformance::check_theory(&logic(), &th, &Type::bool()).unwrap();
        assert!(!th.facts.caps().mem_trivial);
    }

    /// A concrete computation over `btree`: the "sum of leaves" fold
    /// computes on `node (leaf a) (leaf b)` by the comp laws alone.
    #[test]
    fn btree_comp_laws_chain() {
        let th = ImpredicativeBackend::new()
            .realize(&logic(), &btree_spec())
            .unwrap();
        // steps: leaf ↦ its payload, node ↦ nat.add of the images.
        let id_step = {
            let n = Term::free("__n", Type::nat());
            Term::abs(Type::nat(), subst::close(&n, "__n"))
        };
        let add_step = covalence_hol_eval::defs::nat_add();
        let steps = [id_step, add_step];
        for i in 0..2 {
            let c = th.facts.comp(&steps, i).unwrap();
            assert!(c.hyps().is_empty(), "comp({i}) must be closed");
        }
        // rec (node (leaf a) (leaf b)) is well-typed at result `nat`.
        let a = Term::free("a", Type::nat());
        let b = Term::free("b", Type::nat());
        let leaf_a = Term::app(th.ctors[0].clone(), a);
        let leaf_b = Term::app(th.ctors[0].clone(), b);
        let tree = Term::app(Term::app(th.ctors[1].clone(), leaf_a), leaf_b);
        let folded = th.facts.rec_app(&steps, &tree).unwrap();
        assert_eq!(folded.type_of().unwrap(), Type::nat());
    }

    /// The Church backend also realizes the `nat` *shape* — the same spec
    /// the engine backend serves, for the backend-swap test in
    /// [`super::super::engine`].
    #[test]
    fn church_nat_conformance() {
        let th = ImpredicativeBackend::new()
            .realize(&logic(), &super::super::engine::nat_spec())
            .unwrap();
        conformance::check_theory(&logic(), &th, &Type::nat()).unwrap();
    }

    /// Hygiene: colliding binder hints and `'r`-mentioning external sorts
    /// are rejected up front.
    #[test]
    fn hygiene_validation() {
        // Arg hint colliding with a handler name.
        let bad = InductiveSpec::new(
            "bad",
            vec![covalence_inductive::CtorSpec::new(
                "c",
                [("f_c", ArgSort::Ext(Type::nat()))],
            )],
        );
        assert!(matches!(
            ImpredicativeBackend::new().realize(&logic(), &bad),
            Err(InductiveError::Unsupported { .. })
        ));
        // External sort mentioning the result type variable.
        let bad_r = InductiveSpec::new(
            "bad_r",
            vec![covalence_inductive::CtorSpec::new(
                "c",
                [("x", ArgSort::Ext(Type::tfree("r")))],
            )],
        );
        assert!(matches!(
            ImpredicativeBackend::new().realize(&logic(), &bad_r),
            Err(InductiveError::Unsupported { .. })
        ));
    }
}
