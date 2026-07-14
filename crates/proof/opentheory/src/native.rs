//! `NativeOt` — the native [`HolLightKernel`] backend over `covalence-core`.
//!
//! This is the concrete kernel the OpenTheory article interpreter runs
//! against. It implements the arena-style [`HolLightKernel`] trait (NameId
//! handles, `&mut self`) by delegating every inference rule to an
//! already-audited `covalence-core` / `covalence-hol-eval` operation.
//!
//! ## Trust
//!
//! **Zero TCB beyond core HOL.** Every theorem this backend produces is minted
//! by a `covalence-core` rule (`refl`, `trans`, `mk_comb`, `abs`, `beta_conv`,
//! `assume`, `eq_mp`, `deduct_antisym`, `inst`, `inst_tfree`, `define`,
//! `new_type_definition`); this module declares no [`Language`] rule and cannot
//! reach `Thm`'s private mint. Two deliberate design points keep it honest:
//!
//! - **Axioms are hypothesis-tracked, never minted.** `new_axiom(p)` is
//!   `Thm::assume(p)` — the result is `{p} ⊢ p`. An exported theorem that
//!   depends on an axiom therefore carries that axiom's term as a hypothesis;
//!   the honest reading is "verified *relative to* these assumptions". The
//!   `axiom`/`thm` article commands (and package assumption-filtering) treat
//!   those hypotheses accordingly.
//! - **Opaque constants are conservative.** The only primitive constants in
//!   OpenTheory are `=` (seeded here as [`Term::eq_op`]) and `select` (seeded
//!   via `new_constant` as [`Term::select_op`]); everything else enters through
//!   `defineConst` / `defineConstList` / `defineTypeOp`, i.e. `Thm::define` /
//!   `Thm::new_type_definition`, which mint fresh symbols conservatively.
//!
//! ## Numerals
//!
//! No kernel numeral literal (the built-in `Nat` term variant) is ever
//! constructed here. The
//! OpenTheory `std` library *defines* naturals and their binary
//! `bit0`/`bit1`/`zero`/`suc` numerals inside the articles themselves (already
//! in double/succ form), so numerals arrive as ordinary defined constants —
//! nothing special is needed and no extra TCB is incurred. A future backend may
//! instead map `Number.Natural.*` onto `covalence-init`'s nat theory (or an
//! internal HOL-in-Metamath); the [`HolLightKernel`] trait is exactly that swap
//! seam.
//!
//! [`Language`]: covalence_core

use std::collections::{BTreeMap, BTreeSet, HashMap};

use smol_str::SmolStr;

use covalence_core::{Error as CoreError, Term, TermKind, Type, TypeKind, Var, subst};
use covalence_hol::traits::{HolLightKernel, HolLightTerms, HolLightTypes};
use covalence_hol::types::{BOOL_TYCON_ID, EQ_CONST_ID, FUN_TYCON_ID, HolError, NameId};
use covalence_hol_api::{Hol, NativeHol};
use covalence_hol_eval::{EvalThm, TypeDefExt};

/// Map a `covalence-core` error into the trait's `HolError`.
fn ce(e: CoreError) -> HolError {
    HolError::TypeMismatch(e.to_string())
}

/// A registered constant: its term at the most-general (polymorphic) type,
/// plus that general type. Instantiation at a concrete type is a one-way
/// `match_types` + simultaneous tfree-substitution.
#[derive(Clone, Debug)]
struct ConstEntry {
    term: Term,
    ty: Type,
}

/// A registered type constructor.
#[derive(Clone, Debug)]
enum TyconEntry {
    /// Opaque/uninterpreted constructor of the given arity.
    Opaque { arity: usize },
    /// A `defineTypeOp`-introduced subtype `tau`, parametric in `tvars`
    /// (in the **article-declared** order, so `opType` applications
    /// instantiate positionally as the article intends).
    Defined { tau: Type, tvars: Vec<SmolStr> },
}

/// The native OpenTheory kernel backend.
pub struct NativeOt {
    /// NameId → string (populated by `register_name`; seeded with the
    /// three well-known ids).
    names: HashMap<NameId, SmolStr>,
    /// string → NameId (reverse of `names`).
    ids: HashMap<SmolStr, NameId>,
    /// Registered constants (keyed by NameId).
    consts: HashMap<NameId, ConstEntry>,
    /// Registered type constructors (keyed by NameId).
    tycons: HashMap<NameId, TyconEntry>,
    /// Terms introduced by `axiom` commands (hypothesis-tracked; never minted).
    axioms: Vec<Term>,
    /// Monotone counter for fresh internal variable names.
    fresh: u64,
}

impl Default for NativeOt {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeOt {
    pub fn new() -> Self {
        let mut names = HashMap::new();
        let mut ids = HashMap::new();
        for (id, s) in [
            (FUN_TYCON_ID, "->"),
            (BOOL_TYCON_ID, "bool"),
            (EQ_CONST_ID, "="),
        ] {
            names.insert(id, SmolStr::new(s));
            ids.insert(SmolStr::new(s), id);
        }

        let mut consts = HashMap::new();
        // Seed `=` at its most-general type `A → A → bool`.
        let a = Type::tfree("A");
        let eq_ty = Type::fun(a.clone(), Type::fun(a.clone(), Type::bool()));
        consts.insert(
            EQ_CONST_ID,
            ConstEntry {
                term: Term::eq_op(a),
                ty: eq_ty,
            },
        );

        NativeOt {
            names,
            ids,
            consts,
            tycons: HashMap::new(),
            axioms: Vec::new(),
            fresh: 0,
        }
    }

    /// NameId → string (falls back to a printable placeholder for ids the
    /// backend has never been told about — such ids never reach a rule).
    fn resolve(&self, id: NameId) -> SmolStr {
        self.names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| SmolStr::new(format!("?{id}")))
    }

    /// A fresh variable name not present in `avoid`.
    fn fresh_name(&mut self, avoid: &BTreeSet<SmolStr>) -> SmolStr {
        loop {
            let n = SmolStr::new(format!("%{}", self.fresh));
            self.fresh += 1;
            if !avoid.contains(&n) {
                return n;
            }
        }
    }

    /// Instantiate a registered constant at a concrete type, or `None` if the
    /// name is unregistered or `ty` is not an instance of its general type.
    fn instantiate_const(&self, name: NameId, ty: &Type) -> Option<Term> {
        let e = self.consts.get(&name)?;
        if &e.ty == ty {
            return Some(e.term.clone());
        }
        let mut sub = BTreeMap::new();
        subst::match_types(&e.ty, ty, &mut sub).ok()?;
        Some(subst::subst_tfrees_in_term(&e.term, &sub))
    }

    /// The element type `α` iff `ty` has `select`'s shape `(α → bool) → α`.
    fn select_elem(ty: &Type) -> Option<Type> {
        let TypeKind::Fun(pred, res) = ty.kind() else {
            return None;
        };
        let TypeKind::Fun(a, b) = pred.kind() else {
            return None;
        };
        if matches!(b.kind(), TypeKind::Bool) && a == res {
            Some(a.clone())
        } else {
            None
        }
    }

    /// Build a conservative opaque constant term of type `ty`: `ε(λx:ty. x = x)`
    /// wrapped in a fresh `Def`. Only used for the (in practice unreachable)
    /// non-`select` branch of `new_constant`.
    fn opaque_const_term(&self, name: &str, ty: &Type) -> Result<Term, HolError> {
        let v = Term::free("%opq", ty.clone());
        let eqvv = Term::app(Term::app(Term::eq_op(ty.clone()), v.clone()), v.clone());
        let var = v.as_free().expect("just built a Free");
        let pred = Term::abs(ty.clone(), subst::close_var(&eqvv, var));
        let body = Term::app(Term::select_op(ty.clone()), pred);
        let thm = EvalThm::define(name, body).map_err(ce)?;
        let (lhs, _) = thm
            .concl()
            .as_eq()
            .ok_or_else(|| HolError::Unsupported("define did not yield an equation".into()))?;
        Ok(lhs.clone())
    }

    /// Two-pass simultaneous free-variable substitution on a term.
    /// `pairs` is `(new_term, old_var)`; old vars must be `Free`.
    fn simul_vsubst(&mut self, tm: Term, pairs: &[(Term, Term)]) -> Result<Term, HolError> {
        // Collect names to avoid when generating fresh intermediates.
        let mut avoid = BTreeSet::new();
        collect_free_names(&tm, &mut avoid);
        for (n, o) in pairs {
            collect_free_names(n, &mut avoid);
            collect_free_names(o, &mut avoid);
        }

        let mut renamed: Vec<(Var, Term)> = Vec::new(); // (fresh_var, new_term)
        let mut cur = tm;
        for (new_tm, old) in pairs {
            let ov = old.as_free().ok_or(HolError::NotAVariable)?.clone();
            if new_tm == old {
                continue; // no-op
            }
            let fresh = self.fresh_name(&avoid);
            avoid.insert(fresh.clone());
            let fv = Var::new(fresh, ov.ty().clone());
            cur = subst::subst_free(&cur, &ov, &Term::free_var_of(&fv));
            renamed.push((fv, new_tm.clone()));
        }
        for (fv, new_tm) in &renamed {
            cur = subst::subst_free(&cur, fv, new_tm);
        }
        Ok(cur)
    }
}

/// True iff `pattern[σ] ≡ target` for some type substitution σ, accumulated in
/// `sub`. Walks the two terms in lockstep; every type-bearing leaf constrains σ
/// via one-way `match_types`. Term structure (including bound-variable indices
/// and constant/`Def` identity) must match exactly — only *types* may vary.
fn term_type_instance(pattern: &Term, target: &Term, sub: &mut BTreeMap<SmolStr, Type>) -> bool {
    match (pattern.kind(), target.kind()) {
        (TermKind::Bound(i), TermKind::Bound(j)) => i == j,
        (TermKind::Free(p), TermKind::Free(t)) => {
            p.name() == t.name() && subst::match_types(p.ty(), t.ty(), sub).is_ok()
        }
        (TermKind::Const(pn, pt), TermKind::Const(tn, tt)) => {
            pn == tn && subst::match_types(pt, tt, sub).is_ok()
        }
        (TermKind::Def(pd), TermKind::Def(td)) => {
            pd.ptr_id() == td.ptr_id()
                && subst::match_types(pd.instance_type(), td.instance_type(), sub).is_ok()
        }
        (TermKind::App(pf, px), TermKind::App(tf, tx)) => {
            term_type_instance(pf, tf, sub) && term_type_instance(px, tx, sub)
        }
        (TermKind::Abs(pt, pb), TermKind::Abs(tt, tb)) => {
            subst::match_types(pt, tt, sub).is_ok() && term_type_instance(pb, tb, sub)
        }
        (TermKind::Eq(pt), TermKind::Eq(tt)) => subst::match_types(pt, tt, sub).is_ok(),
        (TermKind::Select(pt), TermKind::Select(tt)) => subst::match_types(pt, tt, sub).is_ok(),
        // Fresh constants (abs/rep and typedef-introduced symbols, e.g.
        // `Set.fromPredicate`): same kernel-allocated identity, types may vary.
        (TermKind::FreshConst(pl), TermKind::FreshConst(tl)) => {
            pl.id() == tl.id() && subst::match_types(pl.ty(), tl.ty(), sub).is_ok()
        }
        // Non-type-bearing / literal leaves: require exact equality.
        _ => pattern == target,
    }
}

/// Collect the names of all `Free` variables occurring in `t`.
fn collect_free_names(t: &Term, out: &mut BTreeSet<SmolStr>) {
    match t.kind() {
        TermKind::Free(v) => {
            out.insert(SmolStr::new(v.name()));
        }
        TermKind::App(a, b) => {
            collect_free_names(a, out);
            collect_free_names(b, out);
        }
        TermKind::Abs(_, b) => collect_free_names(b, out),
        _ => {}
    }
}

// A tiny helper so we can build a `Term` from a `Var` without needing a public
// `Term::free_var` name to be stable.
trait FreeVarOf {
    fn free_var_of(v: &Var) -> Term;
}
impl FreeVarOf for Term {
    fn free_var_of(v: &Var) -> Term {
        Term::free(v.name(), v.ty().clone())
    }
}

// ===========================================================================
// HolLightTypes
// ===========================================================================

impl HolLightTypes for NativeOt {
    type Type = Type;

    fn fun_id(&self) -> NameId {
        FUN_TYCON_ID
    }
    fn bool_id(&self) -> NameId {
        BOOL_TYCON_ID
    }

    fn register_name(&mut self, name_id: NameId, name: &str) {
        let s = SmolStr::new(name);
        self.names.insert(name_id, s.clone());
        self.ids.insert(s, name_id);
    }

    fn mk_tyvar(&mut self, name: NameId) -> Type {
        Type::tfree(self.resolve(name))
    }

    fn mk_tyapp(&mut self, name: NameId, args: Vec<Type>) -> Type {
        match name {
            FUN_TYCON_ID if args.len() == 2 => Type::fun(args[0].clone(), args[1].clone()),
            BOOL_TYCON_ID if args.is_empty() => Type::bool(),
            _ => {
                self.tycons
                    .entry(name)
                    .or_insert(TyconEntry::Opaque { arity: args.len() });
                Type::tycon(self.resolve(name), args)
            }
        }
    }

    fn bool_type(&mut self) -> Type {
        Type::bool()
    }
    fn fun_type(&mut self, a: Type, b: Type) -> Type {
        Type::fun(a, b)
    }

    fn dest_tyvar(&self, ty: Self::Type) -> Option<NameId> {
        match ty.kind() {
            TypeKind::TFree(n) => Some(self.ids.get(n).copied().unwrap_or_else(|| synth_id(n))),
            _ => None,
        }
    }

    fn dest_tyapp(&self, ty: Self::Type) -> Option<(NameId, Vec<Type>)> {
        match ty.kind() {
            TypeKind::Fun(a, b) => Some((FUN_TYCON_ID, vec![a.clone(), b.clone()])),
            TypeKind::Bool => Some((BOOL_TYCON_ID, vec![])),
            TypeKind::Tycon(name, args) => Some((
                self.ids
                    .get(name)
                    .copied()
                    .unwrap_or_else(|| synth_id(name)),
                args.iter().cloned().collect(),
            )),
            _ => None,
        }
    }

    fn type_eq(&self, a: Type, b: Type) -> bool {
        a == b
    }

    fn tyvars(&self, ty: Type) -> Vec<NameId> {
        ty.free_tvars()
            .into_iter()
            .map(|n| self.ids.get(&n).copied().unwrap_or_else(|| synth_id(&n)))
            .collect()
    }

    fn type_inst(&mut self, ty: Type, pairs: &[(Type, NameId)]) -> Type {
        let sub: BTreeMap<SmolStr, Type> = pairs
            .iter()
            .map(|(t, n)| (self.resolve(*n), t.clone()))
            .collect();
        subst::subst_tfrees_in_type(&ty, &sub)
    }
}

/// Deterministic high-bit-tagged NameId for a string the backend never
/// interned (only reachable via inspection methods, never a rule).
fn synth_id(s: &str) -> NameId {
    let mut h: u64 = 1469598103934665603;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    (1u64 << 63) | (h >> 1)
}

// ===========================================================================
// HolLightTerms
// ===========================================================================

impl HolLightTerms for NativeOt {
    type Term = Term;

    fn eq_id(&self) -> NameId {
        EQ_CONST_ID
    }

    fn mk_var(&mut self, name: NameId, ty: Type) -> Term {
        Term::free(self.resolve(name), ty)
    }

    fn mk_const(&mut self, name: NameId, ty: Type) -> Term {
        self.instantiate_const(name, &ty)
            .unwrap_or_else(|| Term::free(self.resolve(name), ty))
    }

    fn mk_comb(&mut self, f: Term, x: Term) -> Term {
        Term::app(f, x)
    }

    fn mk_abs(&mut self, var: Term, body: Term) -> Term {
        match var.as_free() {
            Some(v) => Term::abs(v.ty().clone(), subst::close_var(&body, v)),
            None => body,
        }
    }

    fn mk_eq(&mut self, lhs: Term, rhs: Term) -> Term {
        let ty = lhs.type_of().unwrap_or_else(|_| Type::bool());
        Term::app(Term::app(Term::eq_op(ty), lhs), rhs)
    }

    fn dest_var(&self, tm: Term) -> Option<(NameId, Type)> {
        match tm.kind() {
            TermKind::Free(v) => Some((
                self.ids
                    .get(v.name())
                    .copied()
                    .unwrap_or_else(|| synth_id(v.name())),
                v.ty().clone(),
            )),
            _ => None,
        }
    }

    fn dest_const(&self, tm: Term) -> Option<(NameId, Type)> {
        match tm.kind() {
            TermKind::Eq(a) => Some((
                EQ_CONST_ID,
                Type::fun(a.clone(), Type::fun(a.clone(), Type::bool())),
            )),
            TermKind::Def(d) => Some((
                self.ids
                    .get(d.name())
                    .copied()
                    .unwrap_or_else(|| synth_id(d.name())),
                d.instance_type().clone(),
            )),
            TermKind::Const(n, ty) => Some((
                self.ids.get(n).copied().unwrap_or_else(|| synth_id(n)),
                ty.clone(),
            )),
            _ => None,
        }
    }

    fn dest_comb(&self, tm: Term) -> Option<(Term, Term)> {
        tm.as_app().map(|(f, x)| (f.clone(), x.clone()))
    }

    fn dest_abs(&mut self, tm: Term) -> Option<(Term, Term)> {
        let (ty, body) = tm.as_abs().map(|(t, b)| (t.clone(), b.clone()))?;
        let mut avoid = BTreeSet::new();
        collect_free_names(&body, &mut avoid);
        let name = self.fresh_name(&avoid);
        let fresh = Term::free(name, ty);
        let opened = subst::open(&body, &fresh);
        Some((fresh, opened))
    }

    fn dest_eq(&self, tm: Term) -> Option<(Term, Term)> {
        tm.as_eq().map(|(a, b)| (a.clone(), b.clone()))
    }

    fn type_of(&mut self, tm: Term) -> Type {
        tm.type_of().unwrap_or_else(|_| Type::bool())
    }

    fn term_eq(&self, a: Term, b: Term) -> bool {
        a == b
    }

    fn aconv(&self, a: Term, b: Term) -> bool {
        // De Bruijn binders ⇒ structural equality *is* α-equivalence.
        a == b
    }

    fn frees(&mut self, tm: Term) -> Vec<Term> {
        let mut seen = BTreeSet::new();
        let mut out = Vec::new();
        collect_frees(&tm, &mut seen, &mut out);
        out
    }

    fn vfree_in(&self, var: Term, tm: Term) -> bool {
        match var.as_free() {
            Some(v) => subst::has_free_var_typed(&tm, v),
            None => false,
        }
    }

    fn vsubst(&mut self, tm: Term, pairs: &[(Term, Term)]) -> Result<Term, HolError> {
        self.simul_vsubst(tm, pairs)
    }

    fn inst_term(&mut self, tm: Term, pairs: &[(Type, NameId)]) -> Term {
        let sub: BTreeMap<SmolStr, Type> = pairs
            .iter()
            .map(|(t, n)| (self.resolve(*n), t.clone()))
            .collect();
        subst::subst_tfrees_in_term(&tm, &sub)
    }
}

/// Collect `Free` leaves as terms, order-stable and deduplicated by (name,ty).
fn collect_frees(t: &Term, seen: &mut BTreeSet<(SmolStr, Type)>, out: &mut Vec<Term>) {
    match t.kind() {
        TermKind::Free(v) => {
            let key = (SmolStr::new(v.name()), v.ty().clone());
            if seen.insert(key) {
                out.push(t.clone());
            }
        }
        TermKind::App(a, b) => {
            collect_frees(a, seen, out);
            collect_frees(b, seen, out);
        }
        TermKind::Abs(_, b) => collect_frees(b, seen, out),
        _ => {}
    }
}

// ===========================================================================
// HolLightKernel
// ===========================================================================

impl HolLightKernel for NativeOt {
    type Thm = EvalThm;

    fn hyps(&self, th: EvalThm) -> Vec<Term> {
        th.hyps().iter().cloned().collect()
    }

    fn concl(&self, th: EvalThm) -> Term {
        th.concl().clone()
    }

    fn refl(&mut self, tm: Term) -> Result<EvalThm, HolError> {
        EvalThm::refl(tm).map_err(ce)
    }

    fn trans(&mut self, th1: EvalThm, th2: EvalThm) -> Result<EvalThm, HolError> {
        th1.trans(th2).map_err(ce)
    }

    fn mk_comb_rule(&mut self, th1: EvalThm, th2: EvalThm) -> Result<EvalThm, HolError> {
        th1.mk_comb(th2).map_err(ce)
    }

    fn abs_rule(&mut self, var: Term, th: EvalThm) -> Result<EvalThm, HolError> {
        let v = var.as_free().ok_or(HolError::NotAVariable)?;
        let (name, ty) = (v.name().to_string(), v.ty().clone());
        th.abs(&name, ty).map_err(ce)
    }

    fn beta_conv(&mut self, tm: Term) -> Result<EvalThm, HolError> {
        EvalThm::beta_conv(tm).map_err(ce)
    }

    fn assume_rule(&mut self, tm: Term) -> Result<EvalThm, HolError> {
        EvalThm::assume(tm).map_err(ce)
    }

    fn eq_mp(&mut self, th1: EvalThm, th2: EvalThm) -> Result<EvalThm, HolError> {
        th1.eq_mp(th2).map_err(ce)
    }

    fn deduct_antisym(&mut self, th1: EvalThm, th2: EvalThm) -> Result<EvalThm, HolError> {
        th1.deduct_antisym(th2).map_err(ce)
    }

    fn inst_rule(&mut self, pairs: &[(Term, Term)], th: EvalThm) -> Result<EvalThm, HolError> {
        // Simultaneous term-var instantiation via two-pass fresh renaming on
        // the single-variable `Thm::inst` primitive.
        let mut avoid = BTreeSet::new();
        collect_free_names(th.concl(), &mut avoid);
        for h in th.hyps().iter() {
            collect_free_names(h, &mut avoid);
        }
        for (n, o) in pairs {
            collect_free_names(n, &mut avoid);
            collect_free_names(o, &mut avoid);
        }

        let mut renamed: Vec<(SmolStr, Term)> = Vec::new();
        let mut cur = th;
        for (new_tm, old) in pairs {
            let ov = old.as_free().ok_or(HolError::NotAVariable)?;
            let old_name = ov.name().to_string();
            let old_ty = ov.ty().clone();
            // Type of the replacement must match the variable's type.
            if new_tm.type_of().map_err(ce)? != old_ty {
                return Err(HolError::NotAnInstance);
            }
            if new_tm == old {
                continue; // no-op
            }
            let fresh = self.fresh_name(&avoid);
            avoid.insert(fresh.clone());
            let fresh_var = Term::free(fresh.clone(), old_ty);
            cur = cur.inst(&old_name, fresh_var).map_err(ce)?;
            renamed.push((fresh, new_tm.clone()));
        }
        for (fresh, new_tm) in renamed {
            cur = cur.inst(&fresh, new_tm).map_err(ce)?;
        }
        Ok(cur)
    }

    fn inst_type_rule(
        &mut self,
        pairs: &[(Type, NameId)],
        th: EvalThm,
    ) -> Result<EvalThm, HolError> {
        // Simultaneous type-var instantiation via two-pass fresh renaming on
        // the single-tyvar `Thm::inst_tfree` primitive.
        let mut avoid: BTreeSet<SmolStr> = BTreeSet::new();
        subst::collect_term_tvars(th.concl(), &mut avoid);
        for h in th.hyps().iter() {
            subst::collect_term_tvars(h, &mut avoid);
        }
        for (t, _) in pairs {
            for n in t.free_tvars() {
                avoid.insert(n);
            }
        }
        for (_, n) in pairs {
            avoid.insert(self.resolve(*n));
        }

        let mut renamed: Vec<(SmolStr, Type)> = Vec::new();
        let mut cur = th;
        let mut ctr: u64 = 0;
        for (new_ty, old_id) in pairs {
            let old_name = self.resolve(*old_id);
            if matches!(new_ty.kind(), TypeKind::TFree(n) if n == &old_name) {
                continue; // no-op
            }
            let fresh = loop {
                let n = SmolStr::new(format!("%T{ctr}"));
                ctr += 1;
                if !avoid.contains(&n) {
                    break n;
                }
            };
            avoid.insert(fresh.clone());
            cur = cur
                .inst_tfree(&old_name, Type::tfree(fresh.clone()))
                .map_err(ce)?;
            renamed.push((fresh, new_ty.clone()));
        }
        for (fresh, new_ty) in renamed {
            cur = cur.inst_tfree(&fresh, new_ty).map_err(ce)?;
        }
        Ok(cur)
    }

    fn new_axiom(&mut self, tm: Term) -> Result<EvalThm, HolError> {
        // Hypothesis-tracked: `{tm} ⊢ tm`. Never minted.
        self.axioms.push(tm.clone());
        EvalThm::assume(tm).map_err(ce)
    }

    fn new_basic_definition(&mut self, tm: Term) -> Result<EvalThm, HolError> {
        let (lhs, rhs) = tm
            .as_eq()
            .ok_or_else(|| HolError::BadDefinition(format!("{tm:?}")))?;
        let v = lhs
            .as_free()
            .ok_or_else(|| HolError::BadDefinition("lhs is not a variable".into()))?;
        let name = v.name().to_string();
        let thm = EvalThm::define(&name, rhs.clone()).map_err(ce)?;

        // Recover the fresh `Def` term from the theorem's conclusion `Def = t`.
        let (def_lhs, _) = thm
            .concl()
            .as_eq()
            .ok_or_else(|| HolError::Unsupported("define did not yield an equation".into()))?;
        let gen_ty = def_lhs.type_of().map_err(ce)?;
        let id = self
            .ids
            .get(name.as_str())
            .copied()
            .unwrap_or_else(|| synth_id(&name));
        self.consts.insert(
            id,
            ConstEntry {
                term: def_lhs.clone(),
                ty: gen_ty,
            },
        );
        Ok(thm)
    }

    fn new_basic_type_definition(
        &mut self,
        tyname: NameId,
        abs_name: NameId,
        rep_name: NameId,
        tyvars: &[NameId],
        abs_var_name: NameId,
        rep_var_name: NameId,
        th: EvalThm,
    ) -> Result<(EvalThm, EvalThm), HolError> {
        // Capture the predicate `P` from the witness `⊢ P w` BEFORE `th` is
        // consumed by `new_type_definition`.
        let wconcl = th.concl().clone();
        let (pred, _w) = wconcl
            .as_app()
            .ok_or_else(|| HolError::BadTypeDefinition("witness is not `P w`".into()))?;
        let pred = pred.clone();

        let hint = self.resolve(tyname);
        let abs_hint = self.resolve(abs_name);
        let rep_hint = self.resolve(rep_name);
        let td = EvalThm::new_type_definition(hint, abs_hint, rep_hint, th).map_err(ce)?;

        // Register the fresh subtype under the article's tyvar order.
        let article_tvars: Vec<SmolStr> = if tyvars.is_empty() {
            td.tvars.clone()
        } else {
            tyvars.iter().map(|id| self.resolve(*id)).collect()
        };
        self.tycons.insert(
            tyname,
            TyconEntry::Defined {
                tau: td.tau.clone(),
                tvars: article_tvars,
            },
        );

        // Register abs/rep constants at their general types.
        let abs_ty = td.abs.type_of().map_err(ce)?;
        let rep_ty = td.rep.type_of().map_err(ce)?;
        self.consts.insert(
            abs_name,
            ConstEntry {
                term: td.abs.clone(),
                ty: abs_ty.clone(),
            },
        );
        self.consts.insert(
            rep_name,
            ConstEntry {
                term: td.rep.clone(),
                ty: rep_ty,
            },
        );

        // α is `abs`'s domain (abs : α → τ).
        let alpha = match abs_ty.kind() {
            TypeKind::Fun(a, _) => a.clone(),
            _ => {
                return Err(HolError::BadTypeDefinition(
                    "abs is not a function type".into(),
                ));
            }
        };
        let tau = td.tau.clone();
        let hol = NativeHol;

        // thm1 : ⊢ abs (rep a) = a     (a : τ)
        let a_var = Term::free(self.resolve(abs_var_name), tau);
        let thm1 = hol.all_elim(td.abs_rep().map_err(ce)?, a_var).map_err(ce)?;

        // thm2 : ⊢ (P r) = (rep (abs r) = r)     (r : α)
        let r = Term::free(self.resolve(rep_var_name), alpha);
        let p_r = hol.app(pred.clone(), r.clone()).map_err(ce)?;

        // fwd : ⊢ P r ⟹ rep (abs r) = r ; MP with assume(P r) ⇒ {P r} ⊢ rep(abs r)=r
        let fwd = hol
            .all_elim(td.rep_abs_fwd().map_err(ce)?, r.clone())
            .map_err(ce)?;
        let a1 = EvalThm::assume(p_r).map_err(ce)?;
        let d1 = hol.imp_elim(fwd, a1).map_err(ce)?;

        // back : ⊢ rep (abs r) = r ⟹ P r ; MP with assume(rep(abs r)=r) ⇒ {..} ⊢ P r
        let back = hol
            .all_elim(td.rep_abs_back().map_err(ce)?, r)
            .map_err(ce)?;
        let a2 = EvalThm::assume(d1.concl().clone()).map_err(ce)?;
        let d2 = hol.imp_elim(back, a2).map_err(ce)?;

        // ⊢ (P r) = (rep (abs r) = r)
        let thm2 = d2.deduct_antisym(d1).map_err(ce)?;

        Ok((thm1, thm2))
    }

    fn new_type(&mut self, name: NameId, arity: usize) -> Result<(), HolError> {
        self.tycons.insert(name, TyconEntry::Opaque { arity });
        Ok(())
    }

    fn new_constant(&mut self, name: NameId, ty: Type) -> Result<(), HolError> {
        let term = if Self::select_elem(&ty).is_some() {
            let elem = Self::select_elem(&ty).unwrap();
            Term::select_op(elem)
        } else {
            let s = self.resolve(name);
            self.opaque_const_term(&s, &ty)?
        };
        self.consts.insert(name, ConstEntry { term, ty });
        Ok(())
    }

    fn get_axioms(&self) -> Vec<EvalThm> {
        self.axioms
            .iter()
            .filter_map(|t| EvalThm::assume(t.clone()).ok())
            .collect()
    }

    fn mk_type_validated(&mut self, name: NameId, args: Vec<Type>) -> Result<Type, HolError> {
        match name {
            FUN_TYCON_ID => {
                if args.len() != 2 {
                    return Err(HolError::WrongTypeArity {
                        expected: 2,
                        got: args.len(),
                    });
                }
                Ok(Type::fun(args[0].clone(), args[1].clone()))
            }
            BOOL_TYCON_ID => {
                if !args.is_empty() {
                    return Err(HolError::WrongTypeArity {
                        expected: 0,
                        got: args.len(),
                    });
                }
                Ok(Type::bool())
            }
            _ => match self.tycons.get(&name).cloned() {
                Some(TyconEntry::Opaque { arity }) => {
                    if args.len() != arity {
                        return Err(HolError::WrongTypeArity {
                            expected: arity,
                            got: args.len(),
                        });
                    }
                    Ok(Type::tycon(self.resolve(name), args))
                }
                Some(TyconEntry::Defined { tau, tvars }) => {
                    if args.len() != tvars.len() {
                        return Err(HolError::WrongTypeArity {
                            expected: tvars.len(),
                            got: args.len(),
                        });
                    }
                    let sub: BTreeMap<SmolStr, Type> = tvars.into_iter().zip(args).collect();
                    Ok(subst::subst_tfrees_in_type(&tau, &sub))
                }
                // An unregistered type constructor is a *primitive* uninterpreted
                // type (e.g. `ind`, whose only characterisation is the infinity
                // axiom): auto-register it as opaque of the observed arity. Sound
                // — an opaque `Tycon` is just an uninterpreted type, and the name
                // is an efficiency token, not a soundness one.
                None => {
                    self.tycons
                        .insert(name, TyconEntry::Opaque { arity: args.len() });
                    Ok(Type::tycon(self.resolve(name), args))
                }
            },
        }
    }

    fn discharges_as_axiom(&self, hyp: Term) -> bool {
        // A hypothesis is axiom-discharged if it is a *type instance* of some
        // tracked axiom term: `∃σ. axiom[σ] ≡ hyp`. (Plain equality is the
        // σ = identity case.) Sound because `⊢ axiom` ⟹ `⊢ axiom[σ]` by
        // INST_TYPE — the hypothesis is exactly that instance.
        self.axioms.iter().any(|ax| {
            let mut sub = BTreeMap::new();
            term_type_instance(ax, &hyp, &mut sub)
        })
    }

    fn mk_const_validated(&mut self, name: NameId, ty: Type) -> Result<Term, HolError> {
        match self.consts.get(&name) {
            None => {
                // `select` is OpenTheory's only polymorphic primitive constant
                // (type `(α → bool) → α`). Any *undefined* constant of exactly
                // that shape must be it — articles never declare an opaque
                // constant of their own, so this is sound and name-agnostic
                // (the corpus writes it bare as `"select"`).
                if Self::select_elem(&ty).is_some() {
                    // Register at the *general* type `(A → bool) → A` so later
                    // uses at other instances resolve, then instantiate to `ty`.
                    let a = Type::tfree("A");
                    let gen_ty = Type::fun(Type::fun(a.clone(), Type::bool()), a.clone());
                    self.consts.insert(
                        name,
                        ConstEntry {
                            term: Term::select_op(a),
                            ty: gen_ty,
                        },
                    );
                    self.mk_const_validated(name, ty)
                } else {
                    Err(HolError::UnknownConstant(name))
                }
            }
            Some(e) => {
                if e.ty == ty {
                    Ok(e.term.clone())
                } else {
                    let mut sub = BTreeMap::new();
                    subst::match_types(&e.ty, &ty, &mut sub)
                        .map_err(|_| HolError::NotAnInstance)?;
                    Ok(subst::subst_tfrees_in_term(&e.term, &sub))
                }
            }
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(all(test, feature = "native"))]
mod tests {
    use super::*;

    fn bool_ty() -> Type {
        Type::bool()
    }

    #[test]
    fn define_yields_equation() {
        // Assumption check: `Thm::define` conclusion parses with `as_eq`.
        let t = Term::abs(bool_ty(), {
            // λx:bool. x  (identity on bool)
            let v = Term::free("x", bool_ty());
            let var = v.as_free().unwrap();
            subst::close_var(&v, var)
        });
        let thm = EvalThm::define("myid", t).unwrap();
        assert!(
            thm.concl().as_eq().is_some(),
            "define concl must be `c = t`"
        );
    }

    #[test]
    fn refl_assume_eqmp_roundtrip() {
        let mut k = NativeOt::new();
        let p = Term::free("p", bool_ty());
        // ⊢ p = p
        let refl = k.refl(p.clone()).unwrap();
        assert!(k.concl(refl.clone()).as_eq().is_some());
        // {p} ⊢ p
        let asm = k.assume_rule(p.clone()).unwrap();
        assert_eq!(k.hyps(asm.clone()).len(), 1);
        // deduct_antisym of two assumes ⇒ ⊢ p = q (biconditional at bool)
        let q = Term::free("q", bool_ty());
        let asq = k.assume_rule(q.clone()).unwrap();
        let iff = k.deduct_antisym(asm, asq).unwrap();
        assert!(k.concl(iff).as_eq().is_some());
    }

    #[test]
    fn poly_const_instantiation() {
        let mut k = NativeOt::new();
        // `=` at instance bool→bool→bool.
        let inst = Type::fun(bool_ty(), Type::fun(bool_ty(), bool_ty()));
        let eq_at_bool = k.mk_const_validated(EQ_CONST_ID, inst).unwrap();
        match eq_at_bool.kind() {
            TermKind::Eq(a) => assert_eq!(a, &bool_ty()),
            other => panic!("expected Eq(bool), got {other:?}"),
        }
    }

    #[test]
    fn simultaneous_inst_swap() {
        // From ⊢ x = y derive ⊢ y = x via the *simultaneous* subst {x↦y, y↦x}.
        let mut k = NativeOt::new();
        let x = Term::free("x", bool_ty());
        let y = Term::free("y", bool_ty());
        // Build ⊢ x = y by assuming it? No — use refl then... construct a real
        // theorem: assume (x = y) gives {x=y} ⊢ x=y; that's enough to exercise
        // simultaneous inst on the conclusion.
        let eq_xy = k.mk_eq(x.clone(), y.clone());
        let th = k.assume_rule(eq_xy).unwrap();
        let swapped = k
            .inst_rule(&[(y.clone(), x.clone()), (x.clone(), y.clone())], th)
            .unwrap();
        // Conclusion must be y = x, NOT x = x (which a sequential subst yields).
        let c = k.concl(swapped);
        let (l, r) = c.as_eq().unwrap();
        assert_eq!(l, &y, "lhs should be y after simultaneous swap");
        assert_eq!(r, &x, "rhs should be x after simultaneous swap");
    }

    #[test]
    fn type_definition_shapes() {
        // Witness: ⊢ (λx:bool. x = x) T   via  refl T  then fold to `P w`.
        let mut k = NativeOt::new();
        let tt = Term::free("w", bool_ty());
        // P = λx:bool. x = x
        let pbody = {
            let v = Term::free("x", bool_ty());
            let eqvv = k.mk_eq(v.clone(), v.clone());
            let var = v.as_free().unwrap();
            Term::abs(bool_ty(), subst::close_var(&eqvv, var))
        };
        // witness ⊢ P w : build `refl w`  ⊢ w = w, then EQ_MP with
        // ⊢ (w = w) = (P w)?  Simpler: assume (P w).
        let p_w = Term::app(pbody.clone(), tt.clone());
        let witness = k.assume_rule(p_w).unwrap();

        let tyname = 42;
        let absn = 43;
        let repn = 44;
        let avar = 45;
        let rvar = 46;
        k.register_name(tyname, "MyTy");
        k.register_name(absn, "myAbs");
        k.register_name(repn, "myRep");
        k.register_name(avar, "a");
        k.register_name(rvar, "r");

        let (thm1, thm2) = k
            .new_basic_type_definition(tyname, absn, repn, &[], avar, rvar, witness)
            .unwrap();
        // thm1 : abs (rep a) = a  → an equation
        assert!(k.concl(thm1).as_eq().is_some());
        // thm2 : (P r) = (rep (abs r) = r) → an equation whose rhs is itself an eq
        let c2 = k.concl(thm2);
        let (_pr, rhs) = c2.as_eq().expect("thm2 is an equation");
        assert!(rhs.as_eq().is_some(), "thm2 rhs should be `rep(abs r) = r`");
    }
}
