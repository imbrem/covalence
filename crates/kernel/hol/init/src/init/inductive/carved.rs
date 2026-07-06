//! The **carved (exact-type) SExpr backend** — a full-capability
//! realization of the `sexpr` spec (`atom bytes | snil | scons sexpr
//! sexpr`) as a genuine kernel subtype, closing the capability gaps the
//! rank-1 Church encoding provably cannot (`rec_injective`, primitive
//! recursion — the `cdr` extractor wall).
//!
//! ## The construction (universal path-function domain)
//!
//! The carrier is carved from the **universal domain**
//!
//! ```text
//!   U   :=  list bool → LB          (paths → node labels)
//!   LB  :=  coprod bytes (coprod unit unit)
//! ```
//!
//! a binary tree presented as its path→label table: `inl b` labels an
//! `atom b` leaf, `inr (inl ())` an `snil` leaf, `inr (inr ())` an `scons`
//! node. The `U`-level constructors place their label at the empty path
//! and route non-empty paths into the children (`false` = head, `true` =
//! tail); leaves answer the `snil` label off their root, which is junk
//! below `Wf` and therefore harmless:
//!
//! ```text
//!   atomU b    := λp. cond (p = nil) (inl b) snilLab
//!   snilU      := λp. snilLab
//!   sconsU x y := λp. cond (p = nil) sconsLab
//!                      (cond (head p = some true) (y (tail p)) (x (tail p)))
//! ```
//!
//! This is the **pair/prod route to freeness**: `sconsU` is an injective
//! pairing on `U` with *definable projections* — `carU u := λq. u (cons
//! false q)`, `cdrU u := λq. u (cons true q)` — so `cdrU (sconsU x y) = y`
//! is a pointwise computation + function extensionality, and `scons`
//! injectivity **at recursive positions** follows by congruence. The label
//! at the empty path separates the constructors (distinctness via
//! `inl ≠ inr`).
//!
//! The exact type is then `sexpr := { u : U | Wf u }` by
//! [`Thm::new_type_definition`], with `Wf` the impredicative least
//! predicate closed under the three `U`-constructors — structural
//! induction transports through `abs`/`rep` in the standard way, so
//! `mem = λt. ⊤` and every bundle guard discharges for free.
//!
//! ## The recursor: the generic engine, run at this type
//!
//! Everything recursion-shaped comes from the **generic recursion engine**
//! ([`super::graph`]/[`super::existence`]/[`super::uniqueness`]/
//! [`super::determinacy`]/[`super::recursor`]): [`SExprInductive`] is the
//! [`Inductive`] feeder (induction + freeness, all proved here), and
//! [`recursion_equations`] returns the ε-recursor with its
//! **paramorphic** defining equations — steps receive the raw recursive
//! arguments *and* their images, which is exactly the
//! [`BackendCaps::prim_rec`] capability, with iteration (`comp`) served by
//! wrapping. Equations are proved once at a polymorphic result type and
//! instantiated per use.
//!
//! All introduced constants are fresh [`Thm::define`] `Def`s (small terms,
//! β-inert for the engine's normalization passes), built exactly once in a
//! process-global [`LazyLock`].
//!
//! Consumers: the Lisp/ACL2 groundwork theory (`crate::init::lisp`, planned).

use std::sync::LazyLock;

use covalence_core::{Error, Result, Term, Type, subst};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::TypeDefExt;
use covalence_hol_eval::derived::DerivedRules;
use covalence_inductive::{
    ArgSort, BackendCaps, IndResult, InductiveBackend, InductiveError, InductiveFacts,
    InductiveSpec, InductiveTheory,
};

use super::Inductive;
use super::api::{derive_cases_native, internal, prove_beta_eq, relativize_induct};
use super::hol::NativeHol;
use super::recursor::recursion_equations;
use super::sig::{Arg, Constructor, InductiveSig};
use crate::init::cat::fun_ext;
use crate::init::cond::{cond_false, cond_true};
use crate::init::coprod::{inl_inj, inl_ne_inr, inr_inj};
use crate::init::eq::{beta_expand, beta_reduce};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::list::{cons, head, list, nil, nil_ne_cons, tail};
use crate::init::list::{head_cons, tail_cons};
use crate::init::logic::truth;
use crate::init::option::some_inj;

use covalence_hol_eval::defs::{cond, inl, inr, some, unit_nil};

// ============================================================================
// Types + label terms
// ============================================================================

fn bytes_ty() -> Type {
    Type::bytes()
}

/// The path type `list bool`.
fn path_ty() -> Type {
    list(Type::bool())
}

/// The inner label sum `coprod unit unit` (`snil` | `scons` tags).
fn tag_ty() -> Type {
    covalence_hol_eval::defs::coprod(Type::unit(), Type::unit())
}

/// The label type `LB := coprod bytes (coprod unit unit)`.
fn lab_ty() -> Type {
    covalence_hol_eval::defs::coprod(bytes_ty(), tag_ty())
}

/// The universal domain `U := list bool → LB`.
fn dom_ty() -> Type {
    Type::fun(path_ty(), lab_ty())
}

/// `inl b : LB` — the `atom` label.
fn atom_lab(b: Term) -> Result<Term> {
    inl(bytes_ty(), tag_ty()).apply(b)
}

/// `inr (inl ()) : LB` — the `snil` label.
fn snil_lab() -> Result<Term> {
    inr(bytes_ty(), tag_ty()).apply(inl(Type::unit(), Type::unit()).apply(unit_nil())?)
}

/// `inr (inr ()) : LB` — the `scons` label.
fn scons_lab() -> Result<Term> {
    inr(bytes_ty(), tag_ty()).apply(inr(Type::unit(), Type::unit()).apply(unit_nil())?)
}

fn nil_path() -> Term {
    nil(Type::bool())
}

/// `cons d q : list bool`.
fn cons_path(d: Term, q: Term) -> Result<Term> {
    cons(Type::bool()).apply(d)?.apply(q)
}

// ============================================================================
// Small proof plumbing
// ============================================================================

/// `⊢ C x₁ … xₙ = body[x⃗]` — unfold a [`Thm::define`]d constant through
/// its λ-body, one argument at a time (`cong_fn` + top β).
pub(crate) fn apply_def(def_eq: &Thm, args: &[Term]) -> Result<Thm> {
    let mut acc = def_eq.clone();
    for a in args {
        acc = acc.cong_fn(a.clone())?;
        let rhs = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        acc = acc.trans(Thm::beta_conv(rhs)?)?;
    }
    Ok(acc)
}

/// `⊢ p = F` from `{Γ, p} ⊢ F` (deduction antisymmetry; `Γ` survives).
fn eq_f(p: &Term, f_under_p: Thm) -> Result<Thm> {
    let p_from_f = Thm::assume(Term::bool_lit(false))?.false_elim(p.clone())?; // {F} ⊢ p
    p_from_f.deduct_antisym(f_under_p)
}

/// Match a `cond α c x y` spine, returning `(c, x, y)`.
fn split_cond(t: &Term) -> Result<(Term, Term, Term)> {
    let bad = || Error::ConnectiveRule(format!("carved: expected a cond spine, got `{t}`"));
    let (cxy, y) = t.as_app().ok_or_else(bad)?;
    let (cx, x) = cxy.as_app().ok_or_else(bad)?;
    let (_, c) = cx.as_app().ok_or_else(bad)?;
    Ok((c.clone(), x.clone(), y.clone()))
}

/// Fire the leading `cond` of `acc`'s RHS: rewrite its condition to the
/// literal via `c_val : ⊢ c = T/F`, then take the selected branch.
fn fire_cond(acc: Thm, c_val: &Thm) -> Result<Thm> {
    let acc = acc.rhs_conv(|t| t.rw_all(c_val))?;
    let rhs = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    let (c, x, y) = split_cond(&rhs)?;
    let b = c
        .as_bool()
        .ok_or_else(|| Error::ConnectiveRule("carved: cond condition not a literal".into()))?;
    let alpha = x.type_of()?;
    let clause = if b {
        cond_true(&alpha, &x, &y)?
    } else {
        cond_false(&alpha, &x, &y)?
    };
    acc.trans(clause)
}

/// `⊢ (nil = nil) = T` (at `list bool`).
fn nil_eq_nil_t() -> Result<Thm> {
    Thm::refl(nil_path())?.eqt_intro()
}

/// `⊢ (cons d q = nil) = F` (at `list bool`).
fn cons_eq_nil_f(d: &Term, q: &Term) -> Result<Thm> {
    let p = cons_path(d.clone(), q.clone())?.equals(nil_path())?;
    // {p} ⊢ F : ¬(nil = cons d q) against the symmetric assumption.
    let f = nil_ne_cons(&Type::bool(), d, q)?.not_elim(Thm::assume(p.clone())?.sym()?)?;
    eq_f(&p, f)
}

/// `⊢ (head (cons true q) = some true) = T`.
fn head_true_t(q: &Term) -> Result<Thm> {
    head_cons(&Type::bool(), &Term::bool_lit(true), q)?.eqt_intro()
}

/// `⊢ (head (cons false q) = some true) = F`.
fn head_false_f(q: &Term) -> Result<Thm> {
    let some_t = some(Type::bool()).apply(Term::bool_lit(true))?;
    let p = head(Type::bool())
        .apply(cons_path(Term::bool_lit(false), q.clone())?)?
        .equals(some_t)?;
    // {p} ⊢ some false = some true, hence F = T, hence F.
    let hc = head_cons(&Type::bool(), &Term::bool_lit(false), q)?; // ⊢ head (cons F q) = some false
    let ff_tt = hc.sym()?.trans(Thm::assume(p.clone())?)?; // {p} ⊢ some F = some T
    let f_eq_t =
        some_inj(&Type::bool(), &Term::bool_lit(false), &Term::bool_lit(true))?.imp_elim(ff_tt)?; // {p} ⊢ F = T
    let f = f_eq_t.sym()?.eq_mp(truth())?; // {p} ⊢ F
    eq_f(&p, f)
}

// ============================================================================
// The carved theory (built once)
// ============================================================================

/// The carved `sexpr` type: the fresh subtype, its constructors and
/// extractors (all [`Thm::define`]d constants), the well-formedness
/// machinery on the domain, and the freeness/induction theorems the
/// recursion engine consumes. Built exactly once ([`carved`]).
pub struct CarvedSExpr {
    // -- U-level constructors + Wf --
    u_atom: Term,
    u_atom_eq: Thm,
    u_nil: Term,
    u_nil_eq: Thm,
    u_cons: Term,
    u_cons_eq: Thm,
    u_car_eq: Thm,
    u_cdr_eq: Thm,
    /// `Wf : U → bool`.
    wf: Term,
    wf_eq: Thm,
    /// `⊢ Wf (atomU __wb)` (free `__wb : bytes`).
    wf_atom: Thm,
    /// `⊢ Wf snilU`.
    wf_nil: Thm,
    /// `⊢ Wf __wx ⟹ Wf __wy ⟹ Wf (sconsU __wx __wy)`.
    wf_cons: Thm,
    // -- the subtype --
    /// The carved type `sexpr`.
    pub tau: Type,
    abs: Term,
    rep: Term,
    /// `⊢ ∀a:sexpr. abs (rep a) = a`.
    abs_rep: Thm,
    /// `⊢ ∀r:U. Wf r ⟹ rep (abs r) = r`.
    rep_abs_fwd: Thm,
    /// `⊢ Wf (rep __sr)` (free `__sr : sexpr`).
    wf_rep: Thm,
    // -- carved constructors + extractors --
    /// `atom : bytes → sexpr`.
    pub atom: Term,
    atom_eq: Thm,
    /// `snil : sexpr`.
    pub snil: Term,
    snil_eq: Thm,
    /// `scons : sexpr → sexpr → sexpr`.
    pub scons: Term,
    scons_eq: Thm,
    /// `car : sexpr → sexpr` (ACL2 semantics: `car (atom b) = car snil = snil`).
    pub car: Term,
    car_eq: Thm,
    /// `cdr : sexpr → sexpr` (same default).
    pub cdr: Term,
    cdr_eq: Thm,
    /// The engine signature (`atom`/`snil`/`scons` with hints `b`/`h`,`t`).
    sig: InductiveSig,
}

/// The process-global carved theory. All fresh identity (`Def`s, the
/// subtype) is allocated exactly once.
pub fn carved() -> Result<&'static CarvedSExpr> {
    static CARVED: LazyLock<std::result::Result<CarvedSExpr, String>> =
        LazyLock::new(|| CarvedSExpr::build().map_err(|e| e.to_string()));
    CARVED
        .as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("carved sexpr build failed: {e}")))
}

/// Split a `⊢ C = body` definition into `(C, the equation)`.
fn defined(name: &str, body: Term) -> Result<(Term, Thm)> {
    let eq = Thm::define(name, body)?;
    let c = eq.concl().as_eq().ok_or(Error::NotAnEquation)?.0.clone();
    Ok((c, eq))
}

impl CarvedSExpr {
    fn build() -> Result<CarvedSExpr> {
        // ---- U-level constructor bodies ----
        let b = Term::free("__b", bytes_ty());
        let p = Term::free("__p", path_ty());
        let x = Term::free("__x", dom_ty());
        let y = Term::free("__y", dom_ty());

        // atomU := λb p. cond (p = nil) (inl b) snilLab
        let atom_body = {
            let c = cond(lab_ty())
                .apply(p.clone().equals(nil_path())?)?
                .apply(atom_lab(b.clone())?)?
                .apply(snil_lab()?)?;
            let inner = Term::abs(path_ty(), subst::close(&c, "__p"));
            Term::abs(bytes_ty(), subst::close(&inner, "__b"))
        };
        let (u_atom, u_atom_eq) = defined("sexpr.rep.atom", atom_body)?;

        // snilU := λp. snilLab
        let (u_nil, u_nil_eq) = defined("sexpr.rep.nil", Term::abs(path_ty(), snil_lab()?))?;

        // sconsU := λx y p. cond (p = nil) sconsLab
        //            (cond (head p = some true) (y (tail p)) (x (tail p)))
        let cons_body = {
            let tail_p = tail(Type::bool()).apply(p.clone())?;
            let go_true = y.clone().apply(tail_p.clone())?;
            let go_false = x.clone().apply(tail_p)?;
            let test = head(Type::bool())
                .apply(p.clone())?
                .equals(some(Type::bool()).apply(Term::bool_lit(true))?)?;
            let inner_cond = cond(lab_ty())
                .apply(test)?
                .apply(go_true)?
                .apply(go_false)?;
            let c = cond(lab_ty())
                .apply(p.clone().equals(nil_path())?)?
                .apply(scons_lab()?)?
                .apply(inner_cond)?;
            let l_p = Term::abs(path_ty(), subst::close(&c, "__p"));
            let l_y = Term::abs(dom_ty(), subst::close(&l_p, "__y"));
            Term::abs(dom_ty(), subst::close(&l_y, "__x"))
        };
        let (u_cons, u_cons_eq) = defined("sexpr.rep.cons", cons_body)?;

        // carU := λu q. u (cons false q); cdrU := λu q. u (cons true q).
        let proj_body = |flag: bool| -> Result<Term> {
            let u = Term::free("__u", dom_ty());
            let q = Term::free("__q", path_ty());
            let at = u
                .clone()
                .apply(cons_path(Term::bool_lit(flag), q.clone())?)?;
            let inner = Term::abs(path_ty(), subst::close(&at, "__q"));
            Ok(Term::abs(dom_ty(), subst::close(&inner, "__u")))
        };
        let (u_car, u_car_eq) = defined("sexpr.rep.car", proj_body(false)?)?;
        let (u_cdr, u_cdr_eq) = defined("sexpr.rep.cdr", proj_body(true)?)?;

        // ---- Wf: the impredicative least predicate on U ----
        let d_ty = Type::fun(dom_ty(), Type::bool());
        let dv = Term::free("__ud", d_ty.clone());
        let wf_body = {
            let s = Term::free("__us", dom_ty());
            let body = Self::closed_under(&u_atom, &u_nil, &u_cons, &dv)?
                .imp(dv.clone().apply(s.clone())?)?
                .forall("__ud", d_ty.clone())?;
            Term::abs(dom_ty(), subst::close(&body, "__us"))
        };
        let (wf, wf_eq) = defined("sexpr.wf", wf_body)?;

        // Wf-introduction facts. `wf_at(t) : ⊢ Wf t = (∀d. closed d ⟹ d t)`.
        let wf_at = |t: &Term| apply_def(&wf_eq, std::slice::from_ref(t));
        let closed_dv = Self::closed_under(&u_atom, &u_nil, &u_cons, &dv)?;
        let assumed = Thm::assume(closed_dv.clone())?;

        // ⊢ Wf (atomU __wb)
        let wf_atom = {
            let wb = Term::free("__wb", bytes_ty());
            let target = u_atom.clone().apply(wb)?;
            let d_at = assumed
                .clone()
                .and_elim_l()?
                .all_elim(Term::free("__wb", bytes_ty()))?; // {closed} ⊢ d (atomU __wb)
            let gen_ = d_at
                .imp_intro(&closed_dv)?
                .all_intro("__ud", d_ty.clone())?;
            wf_at(&target)?.sym()?.eq_mp(gen_)?
        };

        // ⊢ Wf snilU
        let wf_nil = {
            let d_at = assumed.clone().and_elim_r()?.and_elim_l()?; // {closed} ⊢ d snilU
            let gen_ = d_at
                .imp_intro(&closed_dv)?
                .all_intro("__ud", d_ty.clone())?;
            wf_at(&u_nil)?.sym()?.eq_mp(gen_)?
        };

        // ⊢ Wf __wx ⟹ Wf __wy ⟹ Wf (sconsU __wx __wy)
        let wf_cons = {
            let wx = Term::free("__wx", dom_ty());
            let wy = Term::free("__wy", dom_ty());
            let wf_x = wf.clone().apply(wx.clone())?;
            let wf_y = wf.clone().apply(wy.clone())?;
            // {Wf x, closed} ⊢ d x  (unfold the hypothesis, specialise d).
            let unfold = |v: &Term, hyp: &Term| -> Result<Thm> {
                wf_at(v)?
                    .eq_mp(Thm::assume(hyp.clone())?)? // {Wf v} ⊢ ∀d. closed d ⟹ d v
                    .all_elim(dv.clone())?
                    .imp_elim(assumed.clone())
            };
            let d_x = unfold(&wx, &wf_x)?;
            let d_y = unfold(&wy, &wf_y)?;
            let clause = assumed
                .clone()
                .and_elim_r()?
                .and_elim_r()?
                .all_elim(wx.clone())?
                .all_elim(wy.clone())?; // {closed} ⊢ d x ⟹ d y ⟹ d (sconsU x y)
            let d_c = clause.imp_elim(d_x)?.imp_elim(d_y)?;
            let gen_ = d_c.imp_intro(&closed_dv)?.all_intro("__ud", d_ty.clone())?;
            let target = u_cons.clone().apply(wx)?.apply(wy)?;
            wf_at(&target)?
                .sym()?
                .eq_mp(gen_)?
                .imp_intro(&wf_y)?
                .imp_intro(&wf_x)?
        };

        // ---- carve the subtype ----
        let td = Thm::new_type_definition("sexpr", "sexpr.abs", "sexpr.rep", wf_nil.clone())?;
        let tau = td.tau.clone();
        let abs = td.abs.clone();
        let rep = td.rep.clone();
        let abs_rep = td.abs_rep()?;
        let rep_abs_fwd = td.rep_abs_fwd()?;

        // ⊢ Wf (rep __sr): rep(abs(rep s)) = rep s (congruence over abs_rep),
        // then the backward bijection direction.
        let wf_rep = {
            let s = Term::free("__sr", tau.clone());
            let ar = abs_rep.clone().all_elim(s.clone())?; // ⊢ abs (rep s) = s
            let rr = ar.cong_arg(rep.clone())?; // ⊢ rep (abs (rep s)) = rep s
            td.rep_abs_back()?
                .all_elim(rep.clone().apply(s)?)?
                .imp_elim(rr)?
        };

        // ---- carved constructors + extractors ----
        let (atom, atom_eq) = {
            let bb = Term::free("__b", bytes_ty());
            let body = abs.clone().apply(u_atom.clone().apply(bb)?)?;
            defined(
                "sexpr.atom",
                Term::abs(bytes_ty(), subst::close(&body, "__b")),
            )?
        };
        let (snil, snil_eq) = defined("sexpr.nil", abs.clone().apply(u_nil.clone())?)?;
        let (scons, scons_eq) = {
            let h = Term::free("__h", tau.clone());
            let t = Term::free("__t", tau.clone());
            let body = abs.clone().apply(
                u_cons
                    .clone()
                    .apply(rep.clone().apply(h.clone())?)?
                    .apply(rep.clone().apply(t.clone())?)?,
            )?;
            let l_t = Term::abs(tau.clone(), subst::close(&body, "__t"));
            defined(
                "sexpr.cons",
                Term::abs(tau.clone(), subst::close(&l_t, "__h")),
            )?
        };
        let proj_c = |name: &str, u_proj: &Term| -> Result<(Term, Thm)> {
            let s = Term::free("__s", tau.clone());
            let body = abs
                .clone()
                .apply(u_proj.clone().apply(rep.clone().apply(s.clone())?)?)?;
            defined(name, Term::abs(tau.clone(), subst::close(&body, "__s")))
        };
        let (car, car_eq) = proj_c("sexpr.car", &u_car)?;
        let (cdr, cdr_eq) = proj_c("sexpr.cdr", &u_cdr)?;

        // ---- the engine signature ----
        let sig = InductiveSig {
            ty: tau.clone(),
            relation: "G",
            ctors: vec![
                Constructor::new(
                    atom.clone(),
                    vec![Arg::Param {
                        ty: bytes_ty(),
                        name: "b",
                    }],
                ),
                Constructor::nullary(snil.clone()),
                Constructor::new(
                    scons.clone(),
                    vec![
                        Arg::Rec {
                            name: "h",
                            image: "bh",
                        },
                        Arg::Rec {
                            name: "t",
                            image: "bt",
                        },
                    ],
                ),
            ],
        };

        Ok(CarvedSExpr {
            u_atom,
            u_atom_eq,
            u_nil,
            u_nil_eq,
            u_cons,
            u_cons_eq,
            u_car_eq,
            u_cdr_eq,
            wf,
            wf_eq,
            wf_atom,
            wf_nil,
            wf_cons,
            tau,
            abs,
            rep,
            abs_rep,
            rep_abs_fwd,
            wf_rep,
            atom,
            atom_eq,
            snil,
            snil_eq,
            scons,
            scons_eq,
            car,
            car_eq,
            cdr,
            cdr_eq,
            sig,
        })
    }

    /// `closed(d)` — `d` is closed under the three `U`-constructors:
    /// `(∀b. d (atomU b)) ∧ (d snilU ∧ (∀x y. d x ⟹ d y ⟹ d (sconsU x y)))`.
    fn closed_under(u_atom: &Term, u_nil: &Term, u_cons: &Term, d: &Term) -> Result<Term> {
        let b = Term::free("__wb", bytes_ty());
        let c_atom = d
            .clone()
            .apply(u_atom.clone().apply(b)?)?
            .forall("__wb", bytes_ty())?;
        let c_nil = d.clone().apply(u_nil.clone())?;
        let x = Term::free("__wx", dom_ty());
        let y = Term::free("__wy", dom_ty());
        let c_cons = d
            .clone()
            .apply(x.clone())?
            .imp(
                d.clone().apply(y.clone())?.imp(
                    d.clone()
                        .apply(u_cons.clone().apply(x.clone())?.apply(y.clone())?)?,
                )?,
            )?
            .forall("__wy", dom_ty())?
            .forall("__wx", dom_ty())?;
        c_atom.and(c_nil.and(c_cons)?)
    }

    // ------------------------------------------------------------------
    // U-level computation lemmas
    // ------------------------------------------------------------------

    /// `⊢ atomU b nil = inl b`.
    fn u_atom_at_nil(&self, b: &Term) -> Result<Thm> {
        let acc = apply_def(&self.u_atom_eq, &[b.clone(), nil_path()])?;
        fire_cond(acc, &nil_eq_nil_t()?)
    }

    /// `⊢ atomU b (cons d q) = snilLab`.
    fn u_atom_at_cons(&self, b: &Term, d: &Term, q: &Term) -> Result<Thm> {
        let acc = apply_def(
            &self.u_atom_eq,
            &[b.clone(), cons_path(d.clone(), q.clone())?],
        )?;
        fire_cond(acc, &cons_eq_nil_f(d, q)?)
    }

    /// `⊢ snilU p = snilLab`.
    fn u_nil_at(&self, p: &Term) -> Result<Thm> {
        apply_def(&self.u_nil_eq, std::slice::from_ref(p))
    }

    /// `⊢ sconsU x y nil = sconsLab`.
    fn u_cons_at_nil(&self, x: &Term, y: &Term) -> Result<Thm> {
        let acc = apply_def(&self.u_cons_eq, &[x.clone(), y.clone(), nil_path()])?;
        fire_cond(acc, &nil_eq_nil_t()?)
    }

    /// `⊢ sconsU x y (cons true q) = y q` / `… (cons false q) = x q`.
    fn u_cons_at_dir(&self, x: &Term, y: &Term, flag: bool, q: &Term) -> Result<Thm> {
        let d = Term::bool_lit(flag);
        let acc = apply_def(
            &self.u_cons_eq,
            &[x.clone(), y.clone(), cons_path(d.clone(), q.clone())?],
        )?;
        let acc = fire_cond(acc, &cons_eq_nil_f(&d, q)?)?;
        let acc = if flag {
            fire_cond(acc, &head_true_t(q)?)?
        } else {
            fire_cond(acc, &head_false_f(q)?)?
        };
        // `… = (y|x) (tail (cons d q))`; collapse the tail.
        acc.rhs_conv(|t| t.rw_all(&tail_cons(&Type::bool(), &d, q)?))
    }

    /// `⊢ projU (sconsU x y) = x|y` — the projections compute (pointwise +
    /// function extensionality).
    fn u_proj_cons(&self, take_cdr: bool, x: &Term, y: &Term) -> Result<Thm> {
        let proj_eq = if take_cdr {
            &self.u_cdr_eq
        } else {
            &self.u_car_eq
        };
        let scons_xy = self.u_cons.clone().apply(x.clone())?.apply(y.clone())?;
        let acc = apply_def(proj_eq, std::slice::from_ref(&scons_xy))?; // ⊢ projU (sconsU x y) = λq. sconsU x y (cons flag q)
        let lam = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let q = Term::free("__q", path_ty());
        let pw = Thm::beta_conv(lam.clone().apply(q.clone())?)?
            .trans(self.u_cons_at_dir(x, y, take_cdr, &q)?)?; // ⊢ (λq. …) q = target q
        acc.trans(fun_ext(pw, "__q", &path_ty())?)
    }

    /// `⊢ projU (atomU b) = snilU` and `⊢ projU snilU = snilU` — the
    /// ACL2-style defaults: projecting a leaf answers `snilU`.
    fn u_proj_leaf(&self, take_cdr: bool, leaf: LeafKind<'_>) -> Result<Thm> {
        let proj_eq = if take_cdr {
            &self.u_cdr_eq
        } else {
            &self.u_car_eq
        };
        let flag = Term::bool_lit(take_cdr);
        let leaf_tm = match leaf {
            LeafKind::Atom(b) => self.u_atom.clone().apply(b.clone())?,
            LeafKind::Nil => self.u_nil.clone(),
        };
        let acc = apply_def(proj_eq, std::slice::from_ref(&leaf_tm))?;
        let lam = acc.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
        let q = Term::free("__q", path_ty());
        // (λq. leaf (cons flag q)) q = leaf (cons flag q) = snilLab = snilU q.
        let at_cons = match leaf {
            LeafKind::Atom(b) => self.u_atom_at_cons(b, &flag, &q)?,
            LeafKind::Nil => self.u_nil_at(&cons_path(flag.clone(), q.clone())?)?,
        };
        let pw = Thm::beta_conv(lam.clone().apply(q.clone())?)?
            .trans(at_cons)?
            .trans(self.u_nil_at(&q)?.sym()?)?; // ⊢ (λq. …) q = snilU q
        acc.trans(fun_ext(pw, "__q", &path_ty())?)
    }

    // ------------------------------------------------------------------
    // rep-computation on the carved type
    // ------------------------------------------------------------------

    /// `⊢ rep (abs u) = u` from a proof of `⊢/Γ Wf u`.
    fn fwd(&self, u: &Term, wf_u: Thm) -> Result<Thm> {
        self.rep_abs_fwd.clone().all_elim(u.clone())?.imp_elim(wf_u)
    }

    /// `⊢ rep (atom b) = atomU b`.
    fn rep_atom(&self, b: &Term) -> Result<Thm> {
        let unf = apply_def(&self.atom_eq, std::slice::from_ref(b))?; // atom b = abs (atomU b)
        let u = self.u_atom.clone().apply(b.clone())?;
        unf.cong_arg(self.rep.clone())?
            .trans(self.fwd(&u, self.wf_atom.clone().inst("__wb", b.clone())?)?)
    }

    /// `⊢ rep snil = snilU`.
    fn rep_nil(&self) -> Result<Thm> {
        self.snil_eq
            .clone()
            .cong_arg(self.rep.clone())?
            .trans(self.fwd(&self.u_nil.clone(), self.wf_nil.clone())?)
    }

    /// `⊢ rep (scons h t) = sconsU (rep h) (rep t)`.
    fn rep_cons(&self, h: &Term, t: &Term) -> Result<Thm> {
        let unf = apply_def(&self.scons_eq, &[h.clone(), t.clone()])?;
        let rh = self.rep.clone().apply(h.clone())?;
        let rt = self.rep.clone().apply(t.clone())?;
        let u = self.u_cons.clone().apply(rh.clone())?.apply(rt.clone())?;
        let wf_u = self
            .wf_cons
            .clone()
            .inst("__wx", rh)?
            .inst("__wy", rt)?
            .imp_elim(self.wf_rep.clone().inst("__sr", h.clone())?)?
            .imp_elim(self.wf_rep.clone().inst("__sr", t.clone())?)?;
        unf.cong_arg(self.rep.clone())?.trans(self.fwd(&u, wf_u)?)
    }

    // ------------------------------------------------------------------
    // car/cdr computation laws (public: the Lisp layer's seam)
    // ------------------------------------------------------------------

    /// `⊢ car (scons h t) = h` / `⊢ cdr (scons h t) = t`.
    pub fn proj_scons(&self, take_cdr: bool, h: &Term, t: &Term) -> Result<Thm> {
        let (proj_eq, target) = if take_cdr {
            (&self.cdr_eq, t)
        } else {
            (&self.car_eq, h)
        };
        let scons_ht = self.scons.clone().apply(h.clone())?.apply(t.clone())?;
        let rh = self.rep.clone().apply(h.clone())?;
        let rt = self.rep.clone().apply(t.clone())?;
        apply_def(proj_eq, std::slice::from_ref(&scons_ht))? // proj (scons h t) = abs (projU (rep (scons h t)))
            .rhs_conv(|tm| tm.rw_all(&self.rep_cons(h, t)?))? // = abs (projU (sconsU (rep h) (rep t)))
            .rhs_conv(|tm| tm.rw_all(&self.u_proj_cons(take_cdr, &rh, &rt)?))? // = abs (rep target)
            .trans(self.abs_rep.clone().all_elim(target.clone())?)
    }

    /// `⊢ car (atom b) = snil` (etc.): projecting a leaf answers `snil`.
    pub fn proj_leaf(&self, take_cdr: bool, leaf: LeafKind<'_>) -> Result<Thm> {
        let proj_eq = if take_cdr { &self.cdr_eq } else { &self.car_eq };
        let (leaf_c, rep_leaf) = match leaf {
            LeafKind::Atom(b) => (self.atom.clone().apply(b.clone())?, self.rep_atom(b)?),
            LeafKind::Nil => (self.snil.clone(), self.rep_nil()?),
        };
        apply_def(proj_eq, std::slice::from_ref(&leaf_c))?
            .rhs_conv(|tm| tm.rw_all(&rep_leaf))?
            .rhs_conv(|tm| tm.rw_all(&self.u_proj_leaf(take_cdr, leaf)?))?
            .trans(self.snil_eq.clone().sym()?)
    }

    // ------------------------------------------------------------------
    // Freeness
    // ------------------------------------------------------------------

    /// `⊢ (atom b = atom b2) ⟹ b = b2`.
    fn inj_atom(&self, b: &Term, b2: &Term) -> Result<Thm> {
        let lhs = self.atom.clone().apply(b.clone())?;
        let rhs = self.atom.clone().apply(b2.clone())?;
        let eq = lhs.equals(rhs)?;
        // reps agree, so the labels at nil agree: inl b = inl b2.
        let reps = self
            .rep_atom(b)?
            .sym()?
            .trans(Thm::assume(eq.clone())?.cong_arg(self.rep.clone())?)?
            .trans(self.rep_atom(b2)?)?; // {eq} ⊢ atomU b = atomU b2
        let labs = self
            .u_atom_at_nil(b)?
            .sym()?
            .trans(reps.cong_fn(nil_path())?)?
            .trans(self.u_atom_at_nil(b2)?)?; // {eq} ⊢ inl b = inl b2
        inl_inj(&bytes_ty(), &tag_ty(), b, b2)?
            .imp_elim(labs)?
            .imp_intro(&eq)
    }

    /// `⊢ (scons h t = scons h2 t2) ⟹ xₖ = yₖ` at position `k` (0 = head,
    /// 1 = tail) — **recursive-position injectivity**, by the projection.
    fn inj_scons_at(&self, k: usize, h: &Term, t: &Term, h2: &Term, t2: &Term) -> Result<Thm> {
        let lhs = self.scons.clone().apply(h.clone())?.apply(t.clone())?;
        let rhs = self.scons.clone().apply(h2.clone())?.apply(t2.clone())?;
        let eq = lhs.equals(rhs)?;
        let take_cdr = k == 1;
        let proj = if take_cdr { &self.cdr } else { &self.car };
        let core = self
            .proj_scons(take_cdr, h, t)?
            .sym()?
            .trans(Thm::assume(eq.clone())?.cong_arg(proj.clone())?)?
            .trans(self.proj_scons(take_cdr, h2, t2)?)?; // {eq} ⊢ xₖ = yₖ
        core.imp_intro(&eq)
    }

    /// The `(rep …, label-at-nil)` pair for constructor `i` at `args`:
    /// `⊢ rep (Cᵢ x⃗) = Uᵢ …` and `⊢ Uᵢ … nil = labᵢ`.
    fn rep_and_label(&self, i: usize, args: &[Term]) -> Result<(Thm, Thm)> {
        match (i, args) {
            (0, [b]) => Ok((self.rep_atom(b)?, self.u_atom_at_nil(b)?)),
            (1, []) => Ok((self.rep_nil()?, self.u_nil_at(&nil_path())?)),
            (2, [h, t]) => {
                let rh = self.rep.clone().apply(h.clone())?;
                let rt = self.rep.clone().apply(t.clone())?;
                Ok((self.rep_cons(h, t)?, self.u_cons_at_nil(&rh, &rt)?))
            }
            _ => Err(Error::ConnectiveRule(format!(
                "carved distinct: bad constructor/arity ({i}, {})",
                args.len()
            ))),
        }
    }

    /// `⊢ ¬(labᵢ = labⱼ)` for `i < j` (labels of distinct constructors).
    fn lab_ne(&self, i: usize, j: usize, args_i: &[Term]) -> Result<Thm> {
        let one = unit_nil();
        let inl_one = inl(Type::unit(), Type::unit()).apply(one.clone())?;
        let inr_one = inr(Type::unit(), Type::unit()).apply(one)?;
        match (i, j) {
            // atom vs snil/scons: inl b ≠ inr tag.
            (0, 1) => inl_ne_inr(&bytes_ty(), &tag_ty(), &args_i[0], &inl_one),
            (0, 2) => inl_ne_inr(&bytes_ty(), &tag_ty(), &args_i[0], &inr_one),
            // snil vs scons: inr (inl ()) ≠ inr (inr ()) via inr-injectivity.
            (1, 2) => {
                let lhs = inr(bytes_ty(), tag_ty()).apply(inl_one.clone())?;
                let rhs = inr(bytes_ty(), tag_ty()).apply(inr_one.clone())?;
                let eq = lhs.equals(rhs)?;
                let inner = inr_inj(&bytes_ty(), &tag_ty(), &inl_one, &inr_one)?
                    .imp_elim(Thm::assume(eq.clone())?)?; // {eq} ⊢ inl () = inr ()
                let one2 = unit_nil();
                let f = inl_ne_inr(&Type::unit(), &Type::unit(), &one2, &one2)?.not_elim(inner)?; // {eq} ⊢ F
                f.imp_intro(&eq)?.not_intro()
            }
            _ => Err(Error::ConnectiveRule(format!(
                "carved lab_ne: bad pair ({i}, {j})"
            ))),
        }
    }

    /// `⊢ (Cᵢ x⃗ = Cⱼ y⃗) ⟹ F` for `i ≠ j`.
    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        if i == j {
            return Err(Error::ConnectiveRule(
                "carved distinct: constructor indices must differ".into(),
            ));
        }
        let (rep_i, lab_i) = self.rep_and_label(i, xs)?;
        let (rep_j, lab_j) = self.rep_and_label(j, ys)?;
        let ci = apply_ctor(&self.sig, i, xs)?;
        let cj = apply_ctor(&self.sig, j, ys)?;
        let eq = ci.equals(cj)?;
        // {eq} ⊢ labᵢ = labⱼ.
        let reps = rep_i
            .sym()?
            .trans(Thm::assume(eq.clone())?.cong_arg(self.rep.clone())?)?
            .trans(rep_j)?;
        let labs = lab_i
            .sym()?
            .trans(reps.cong_fn(nil_path())?)?
            .trans(lab_j)?;
        let f = if i < j {
            self.lab_ne(i, j, xs)?.not_elim(labs)?
        } else {
            self.lab_ne(j, i, ys)?.not_elim(labs.sym()?)?
        };
        f.imp_intro(&eq)
    }

    // ------------------------------------------------------------------
    // Structural induction (curried, applied form)
    // ------------------------------------------------------------------

    /// Rule-form structural induction on the carved type: from
    /// `⊢ P (atom b)` (free `b`), `⊢ P snil`, and
    /// `⊢ P h ⟹ P t ⟹ P (scons h t)` (free `h`, `t`) — applied form,
    /// binder-hint names — conclude `⊢ ∀s. P s` (applied).
    pub fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        let [case_atom, case_nil, case_cons]: [Thm; 3] = cases
            .try_into()
            .map_err(|_| Error::ConnectiveRule("carved induct: expected 3 cases".into()))?;

        // S := λu. Wf u ∧ P (abs u).
        let s_lam = {
            let u = Term::free("__su", dom_ty());
            let body = self
                .wf
                .clone()
                .apply(u.clone())?
                .and(motive.clone().apply(self.abs.clone().apply(u.clone())?)?)?;
            Term::abs(dom_ty(), subst::close(&body, "__su"))
        };

        // ⊢ P x = P y from ⊢ x = y.
        let p_cong = |eq: Thm| -> Result<Thm> { Thm::refl(motive.clone())?.cong_app(eq) };

        // -- clause 0: ∀b. S (atomU b) --
        let cl_atom = {
            let b = Term::free("__wb", bytes_ty());
            let target = self.u_atom.clone().apply(b.clone())?;
            let wf_part = self.wf_atom.clone(); // free __wb already
            // P (atom b) = P (abs (atomU b)).
            let unf = apply_def(&self.atom_eq, std::slice::from_ref(&b))?;
            let p_part = p_cong(unf)?.eq_mp(case_atom.inst("b", b.clone())?)?;
            beta_expand(&s_lam, target, wf_part.and_intro(p_part)?)?
                .all_intro("__wb", bytes_ty())?
        };

        // -- clause 1: S snilU --
        let cl_nil = {
            let p_part = p_cong(self.snil_eq.clone())?.eq_mp(case_nil)?;
            beta_expand(
                &s_lam,
                self.u_nil.clone(),
                self.wf_nil.clone().and_intro(p_part)?,
            )?
        };

        // -- clause 2: ∀x y. S x ⟹ S y ⟹ S (sconsU x y) --
        let cl_cons = {
            let x = Term::free("__wx", dom_ty());
            let y = Term::free("__wy", dom_ty());
            let hyp_x = s_lam.clone().apply(x.clone())?;
            let hyp_y = s_lam.clone().apply(y.clone())?;
            let sx = beta_reduce(Thm::assume(hyp_x.clone())?)?; // {S x} ⊢ Wf x ∧ P (abs x)
            let sy = beta_reduce(Thm::assume(hyp_y.clone())?)?;
            let wf_x = sx.clone().and_elim_l()?;
            let wf_y = sy.clone().and_elim_l()?;
            let p_x = sx.and_elim_r()?;
            let p_y = sy.and_elim_r()?;

            let wf_part = self
                .wf_cons
                .clone()
                .inst("__wx", x.clone())?
                .inst("__wy", y.clone())?
                .imp_elim(wf_x.clone())?
                .imp_elim(wf_y.clone())?;

            // P (scons (abs x) (abs y)) from the case.
            let p_at = case_cons
                .inst("h", self.abs.clone().apply(x.clone())?)?
                .inst("t", self.abs.clone().apply(y.clone())?)?
                .imp_elim(p_x)?
                .imp_elim(p_y)?;
            // scons (abs x) (abs y) = abs (sconsU x y).
            let unf = apply_def(
                &self.scons_eq,
                &[
                    self.abs.clone().apply(x.clone())?,
                    self.abs.clone().apply(y.clone())?,
                ],
            )?
            .rhs_conv(|tm| tm.rw_all(&self.fwd(&x, wf_x.clone())?))?
            .rhs_conv(|tm| tm.rw_all(&self.fwd(&y, wf_y.clone())?))?;
            let p_part = p_cong(unf)?.eq_mp(p_at)?;

            let target = self.u_cons.clone().apply(x)?.apply(y)?;
            beta_expand(&s_lam, target, wf_part.and_intro(p_part)?)?
                .imp_intro(&hyp_y)?
                .imp_intro(&hyp_x)?
                .all_intro("__wy", dom_ty())?
                .all_intro("__wx", dom_ty())?
        };

        let closed_s = cl_atom.and_intro(cl_nil.and_intro(cl_cons)?)?;

        // ∀s:sexpr. P s: unfold Wf (rep s), specialise d := S, transport.
        let s = Term::free("__ss", self.tau.clone());
        let rep_s = self.rep.clone().apply(s.clone())?;
        let g = apply_def(&self.wf_eq, std::slice::from_ref(&rep_s))?
            .eq_mp(self.wf_rep.clone().inst("__sr", s.clone())?)?; // ⊢ ∀d. closed d ⟹ d (rep s)
        let s_at = g.all_elim(s_lam.clone())?.imp_elim(closed_s)?; // ⊢ S (rep s)  (redex)
        let split = beta_reduce(s_at)?.and_elim_r()?; // ⊢ P (abs (rep s))
        let p_s = p_cong(self.abs_rep.clone().all_elim(s.clone())?)?.eq_mp(split)?;
        p_s.all_intro("__ss", self.tau.clone())
    }
}

/// Which leaf a projection is applied to (for the ACL2-default laws).
#[derive(Clone, Copy)]
pub enum LeafKind<'a> {
    /// `atom b`.
    Atom(&'a Term),
    /// `snil`.
    Nil,
}

/// `Cᵢ x⃗` from the signature's constructor terms.
fn apply_ctor(sig: &InductiveSig, i: usize, args: &[Term]) -> Result<Term> {
    let mut t = sig.ctors[i].ctor.clone();
    for a in args {
        t = t.apply(a.clone())?;
    }
    Ok(t)
}

// ============================================================================
// The engine feeder
// ============================================================================

/// The carved type's [`Inductive`] feeder — supplies structural induction
/// and freeness to the generic recursion engine.
pub struct SExprInductive(&'static CarvedSExpr);

/// The feeder over the process-global carved theory.
pub fn sexpr_inductive() -> Result<SExprInductive> {
    Ok(SExprInductive(carved()?))
}

impl Inductive for SExprInductive {
    fn sig(&self) -> &InductiveSig {
        &self.0.sig
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> Result<Thm> {
        // The engine supplies the recursive case with a *conjunctive*
        // antecedent `(P h ∧ P t) ⟹ P (scons h t)`; curry it for the core.
        let [a, n, c]: [Thm; 3] = cases
            .try_into()
            .map_err(|_| Error::ConnectiveRule("sexpr induct: expected 3 cases".into()))?;
        let ph = Term::app(motive.clone(), Term::free("h", self.0.tau.clone()));
        let pt = Term::app(motive.clone(), Term::free("t", self.0.tau.clone()));
        let curried = c
            .imp_elim(Thm::assume(ph.clone())?.and_intro(Thm::assume(pt.clone())?)?)?
            .imp_intro(&pt)?
            .imp_intro(&ph)?;
        self.0.induct(motive, vec![a, n, curried])
    }

    fn injective(&self, i: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        match (i, xs, ys) {
            (0, [b], [b2]) => self.0.inj_atom(b, b2),
            (2, [h, t], [h2, t2]) => {
                // ⊢ eq ⟹ (h = h2 ∧ t = t2): conjoin the per-position facts.
                let eq = apply_ctor(&self.0.sig, 2, xs)?.equals(apply_ctor(&self.0.sig, 2, ys)?)?;
                let head = self
                    .0
                    .inj_scons_at(0, h, t, h2, t2)?
                    .imp_elim(Thm::assume(eq.clone())?)?;
                let tail = self
                    .0
                    .inj_scons_at(1, h, t, h2, t2)?
                    .imp_elim(Thm::assume(eq.clone())?)?;
                head.and_intro(tail)?.imp_intro(&eq)
            }
            _ => Err(Error::ConnectiveRule(format!(
                "sexpr injective: no injectivity for constructor {i} at these arities"
            ))),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> Result<Thm> {
        self.0.distinct(i, j, xs, ys)
    }
}

// ============================================================================
// The recursor (generic engine, cached at a polymorphic result type)
// ============================================================================

/// The polymorphic result-type variable the cached engine run uses.
const REC_B: &str = "__srec_b";
/// The three step variables (reserved names).
const STEP_VARS: [&str; 3] = ["__sfa", "__sfn", "__sfc"];

/// The para step types at result `beta`: `bytes → β`, `β`,
/// `sexpr → sexpr → β → β → β`.
fn para_step_tys(tau: &Type, beta: &Type) -> [Type; 3] {
    [
        Type::fun(bytes_ty(), beta.clone()),
        beta.clone(),
        Type::fun(
            tau.clone(),
            Type::fun(
                tau.clone(),
                Type::fun(beta.clone(), Type::fun(beta.clone(), beta.clone())),
            ),
        ),
    ]
}

/// The engine run — once, at the polymorphic `'__srec_b`.
fn rec_poly() -> Result<&'static (Term, Vec<Thm>)> {
    static REC: LazyLock<std::result::Result<(Term, Vec<Thm>), String>> = LazyLock::new(|| {
        (|| {
            let theory = sexpr_inductive()?;
            let beta = Type::tfree(REC_B);
            let tys = para_step_tys(&theory.0.tau, &beta);
            let steps: Vec<Term> = STEP_VARS
                .iter()
                .zip(tys)
                .map(|(n, ty)| Term::free(*n, ty))
                .collect();
            recursion_equations(&theory, &steps, &beta)
        })()
        .map_err(|e: Error| e.to_string())
    });
    REC.as_ref()
        .map_err(|e| Error::ConnectiveRule(format!("carved sexpr recursor failed: {e}")))
}

/// The recursor term and equations instantiated at result type `beta`.
fn rec_at(beta: &Type) -> Result<(Term, Vec<Thm>)> {
    let (rec, eqs) = rec_poly()?;
    let rec_b = subst::subst_tfree_in_term(rec, REC_B, beta);
    let eqs_b = eqs
        .iter()
        .map(|e| e.clone().inst_tfree(REC_B, beta.clone()))
        .collect::<Result<_>>()?;
    Ok((rec_b, eqs_b))
}

// ============================================================================
// The recursor, exposed for defining recursive functions (the Lisp layer)
// ============================================================================

impl CarvedSExpr {
    /// The paramorphic recursor `rec s⃗ : sexpr → β` at result type `beta`,
    /// fully applied to the three step terms (their types are
    /// [`para_step_tys`]`(tau, beta)`). This is the term the Lisp layer
    /// [`Thm::define`]s a total recursive function as.
    pub(crate) fn prec(&self, steps: &[Term], beta: &Type) -> Result<Term> {
        let (rec, _) = rec_at(beta)?;
        let mut r = rec;
        for s in steps {
            r = r.apply(s.clone())?;
        }
        Ok(r)
    }

    /// The paramorphic computation equation for constructor `i` with the
    /// three steps substituted: `⊢ ∀x⃗. rec s⃗ (Cᵢ x⃗) = sᵢ x⃗ (rec s⃗ r⃗)`
    /// (`r⃗` = the recursive arguments among `x⃗`). The `rec s⃗ …`
    /// applications match [`Self::prec`]`(steps, beta).apply(…)` verbatim,
    /// so an unfolded definition rewrites against this equation directly.
    pub(crate) fn prec_eq(&self, steps: &[Term], i: usize, beta: &Type) -> Result<Thm> {
        let (_, eqs) = rec_at(beta)?;
        let mut eq = eqs.get(i).cloned().ok_or_else(|| {
            Error::ConnectiveRule(format!("carved prec_eq: bad constructor index {i}"))
        })?;
        for (name, s) in STEP_VARS.iter().zip(steps) {
            eq = eq.inst(name, s.clone())?;
        }
        Ok(eq)
    }
}

// ============================================================================
// The bundle: InductiveBackend + InductiveFacts
// ============================================================================

/// The carved (exact-type) `sexpr` backend — full capabilities:
/// `mem_trivial`, `rec_injective`, `prim_rec`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CarvedSExprBackend;

/// The carved backend value.
pub fn carved_backend() -> CarvedSExprBackend {
    CarvedSExprBackend
}

impl InductiveBackend<NativeHol> for CarvedSExprBackend {
    fn realize(
        &self,
        _logic: &NativeHol,
        spec: &InductiveSpec<Type>,
    ) -> IndResult<InductiveTheory<NativeHol>, NativeHol> {
        spec.validate().map_err(InductiveError::spec)?;
        // The carved carrier realizes exactly the `sexpr` shape:
        // [Ext(bytes)], [], [Rec, Rec].
        let shape_ok = spec.ctors.len() == 3
            && matches!(spec.ctors[0].args.as_slice(), [(_, ArgSort::Ext(t))] if *t == bytes_ty())
            && spec.ctors[1].args.is_empty()
            && matches!(
                spec.ctors[2].args.as_slice(),
                [(_, ArgSort::Rec), (_, ArgSort::Rec)]
            );
        if !shape_ok {
            return Err(InductiveError::SpecMismatch(format!(
                "the carved backend realizes the `sexpr` shape \
                 (atom bytes | snil | scons rec rec) only, got `{}`",
                spec.name
            )));
        }
        let cs = carved()?;
        let mem = Term::abs(cs.tau.clone(), Term::bool_lit(true));
        Ok(InductiveTheory {
            spec: spec.clone(),
            ty: cs.tau.clone(),
            mem: mem.clone(),
            ctors: vec![cs.atom.clone(), cs.snil.clone(), cs.scons.clone()],
            facts: Box::new(CarvedTheory {
                spec: spec.clone(),
                mem,
            }),
        })
    }
}

struct CarvedTheory {
    spec: InductiveSpec<Type>,
    /// `λt:sexpr. ⊤`.
    mem: Term,
}

impl CarvedTheory {
    fn steps3<'a>(&self, steps: &'a [Term]) -> IndResult<&'a [Term; 3], NativeHol> {
        steps.try_into().map_err(|_| InductiveError::Arity {
            what: "recursor steps",
            expected: 3,
            got: steps.len(),
        })
    }

    /// Wrap iteration steps into para shape: the `scons` step drops the raw
    /// arguments (`λ__h __t __bh __bt. s __bh __bt`).
    fn wrap_iter(&self, steps: &[Term; 3], tau: &Type, beta: &Type) -> Result<[Term; 3]> {
        let bh = Term::free("__bh", beta.clone());
        let bt = Term::free("__bt", beta.clone());
        let body = steps[2].clone().apply(bh)?.apply(bt)?;
        let l_bt = Term::abs(beta.clone(), subst::close(&body, "__bt"));
        let l_bh = Term::abs(beta.clone(), subst::close(&l_bt, "__bh"));
        let l_t = Term::abs(tau.clone(), l_bh);
        let l_h = Term::abs(tau.clone(), l_t);
        Ok([steps[0].clone(), steps[1].clone(), l_h])
    }

    /// `beta` from the `snil` step.
    fn result_ty(&self, steps: &[Term; 3]) -> Result<Type> {
        steps[1].type_of()
    }

    /// The para equations with the step variables instantiated.
    fn pcomp_at(&self, steps: &[Term; 3], i: usize) -> IndResult<Thm, NativeHol> {
        if i >= 3 {
            return Err(InductiveError::CtorIndex { index: i, arity: 3 });
        }
        let beta = self.result_ty(steps)?;
        let (_, eqs) = rec_at(&beta)?;
        let mut eq = eqs[i].clone();
        for (name, s) in STEP_VARS.iter().zip(steps) {
            eq = eq.inst(name, s.clone())?;
        }
        Ok(eq)
    }
}

impl InductiveFacts<NativeHol> for CarvedTheory {
    fn rec_app(&self, steps: &[Term], t: &Term) -> IndResult<Term, NativeHol> {
        let steps = self.steps3(steps)?;
        let beta = self.result_ty(steps)?;
        let tau = &carved()?.tau;
        let wrapped = self.wrap_iter(steps, tau, &beta)?;
        self.prec_app(&wrapped, t)
    }

    fn comp(&self, steps: &[Term], i: usize) -> IndResult<Thm, NativeHol> {
        let steps = self.steps3(steps)?;
        let beta = self.result_ty(steps)?;
        let cs = carved()?;
        let wrapped = self.wrap_iter(steps, &cs.tau, &beta)?;
        let eq = self.pcomp_at(&wrapped, i)?;
        if i < 2 {
            // atom/snil have no recursive arguments: para = iteration shape.
            return Ok(eq);
        }
        // scons: β-bridge `(λ__h __t __bh __bt. s __bh __bt) h t (rec h) (rec t)`
        // to the contract's `s (rec h) (rec t)`.
        let h = Term::free("h", cs.tau.clone());
        let t = Term::free("t", cs.tau.clone());
        let raw = eq.all_elim(h.clone())?.all_elim(t.clone())?;
        let Some((_, rhs)) = raw.concl().as_eq() else {
            return internal("carved comp: recursion equation is not an equation");
        };
        let target = steps[2]
            .clone()
            .apply(self.rec_app(steps.as_slice(), &h)?)?
            .apply(self.rec_app(steps.as_slice(), &t)?)?;
        let bridge = prove_beta_eq(rhs.clone(), target)?;
        Ok(raw
            .trans(bridge)?
            .all_intro("t", cs.tau.clone())?
            .all_intro("h", cs.tau.clone())?)
    }

    fn prec_app(&self, steps: &[Term], t: &Term) -> IndResult<Term, NativeHol> {
        let steps = self.steps3(steps)?;
        let beta = self.result_ty(steps)?;
        let (rec, _) = rec_at(&beta)?;
        let mut r = rec;
        for s in steps {
            r = r.apply(s.clone())?;
        }
        Ok(r.apply(t.clone())?)
    }

    fn pcomp(&self, steps: &[Term], i: usize) -> IndResult<Thm, NativeHol> {
        let steps = self.steps3(steps)?;
        self.pcomp_at(steps, i)
    }

    fn injective(&self, i: usize, k: usize, xs: &[Term], ys: &[Term]) -> IndResult<Thm, NativeHol> {
        let cs = carved()?;
        match (i, k, xs, ys) {
            (0, 0, [b], [b2]) => Ok(cs.inj_atom(b, b2)?),
            (2, 0 | 1, [h, t], [h2, t2]) => Ok(cs.inj_scons_at(k, h, t, h2, t2)?),
            (0 | 2, _, _, _) => Err(InductiveError::ArgIndex {
                ctor: self.spec.ctors[i].name.clone(),
                index: k,
                arity: self.spec.ctors[i].arity(),
            }),
            _ => Err(InductiveError::Unsupported {
                what: "injectivity",
                why: format!("constructor {i} has no argument {k}"),
            }),
        }
    }

    fn distinct(&self, i: usize, j: usize, xs: &[Term], ys: &[Term]) -> IndResult<Thm, NativeHol> {
        Ok(carved()?.distinct(i, j, xs, ys)?)
    }

    fn induct(&self, motive: &Term, cases: Vec<Thm>) -> IndResult<Thm, NativeHol> {
        let cs = carved()?;
        let bare = cs.induct(motive, cases)?; // ⊢ ∀s. P s
        Ok(relativize_induct(bare, &self.mem, &cs.tau)?)
    }

    fn cases(&self) -> IndResult<Thm, NativeHol> {
        let cs = carved()?;
        let ctors = [cs.atom.clone(), cs.snil.clone(), cs.scons.clone()];
        derive_cases_native(&self.spec, &cs.tau, &ctors, &|m, c| self.induct(m, c))
    }

    fn mem_ctor(&self, i: usize, args: &[Term], _rec_mems: Vec<Thm>) -> IndResult<Thm, NativeHol> {
        let cs = carved()?;
        let c = self
            .spec
            .ctors
            .get(i)
            .ok_or(InductiveError::CtorIndex { index: i, arity: 3 })?;
        if args.len() != c.arity() {
            return Err(InductiveError::Arity {
                what: "constructor arguments",
                expected: c.arity(),
                got: args.len(),
            });
        }
        let target = apply_ctor(&cs.sig, i, args)?;
        // `mem = λt. ⊤`: a β-expansion of `⊢ ⊤`.
        Ok(crate::init::eq::beta_expand(&self.mem, target, truth())?)
    }

    fn mem_trivial(&self) -> Option<Thm> {
        let cs = carved().ok()?;
        let tv = Term::free("__t", cs.tau.clone());
        crate::init::eq::beta_expand(&self.mem, tv, truth())
            .and_then(|t| t.all_intro("__t", cs.tau.clone()))
            .ok()
    }

    fn caps(&self) -> BackendCaps {
        BackendCaps {
            mem_trivial: true,
            rec_injective: true,
            prim_rec: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::sexpr::sexpr_spec;
    use covalence_inductive::conformance;

    fn logic() -> NativeHol {
        NativeHol
    }

    fn theory() -> InductiveTheory<NativeHol> {
        carved_backend().realize(&logic(), &sexpr_spec()).unwrap()
    }

    /// Full conformance (comp + pcomp + induct + mem + distinct) at a
    /// concrete result type — the carved bundle is full-caps.
    #[test]
    fn carved_conformance_full_caps() {
        let th =
            conformance::check_backend(&logic(), &carved_backend(), &sexpr_spec(), &Type::nat())
                .unwrap();
        let caps = th.facts.caps();
        assert!(caps.mem_trivial && caps.rec_injective && caps.prim_rec);
        let triv = th.facts.mem_trivial().expect("exact carrier");
        assert!(triv.hyps().is_empty());
    }

    /// **The backend-swap test at the flagship spec**: the same generic
    /// consumer runs against the Church bundle and the carved bundle.
    #[test]
    fn backend_swap_church_vs_carved() {
        let church = crate::init::sexpr::sexpr_backend();
        let backends: [&dyn InductiveBackend<NativeHol>; 2] = [&church, &CarvedSExprBackend];
        for b in backends {
            conformance::check_backend(&logic(), b, &sexpr_spec(), &Type::bool()).unwrap();
        }
    }

    /// `cdr (scons h t) = t` — the rec-position extractor the Church
    /// encoding provably cannot state (the I2 wall), now a theorem.
    #[test]
    fn cdr_scons_computes() {
        let cs = carved().unwrap();
        let h = Term::free("h", cs.tau.clone());
        let t = Term::free("t", cs.tau.clone());
        let thm = cs.proj_scons(true, &h, &t).unwrap();
        assert!(thm.hyps().is_empty());
        let scons_ht = cs.scons.clone().apply(h).unwrap().apply(t.clone()).unwrap();
        let expected = cs.cdr.clone().apply(scons_ht).unwrap().equals(t).unwrap();
        assert_eq!(thm.concl(), &expected);
    }

    /// Recursive-position injectivity through the bundle (`Unsupported`
    /// for Church; a genuine theorem here).
    #[test]
    fn rec_position_injectivity() {
        let th = theory();
        let cs = carved().unwrap();
        let vars = |n: &str| Term::free(n, cs.tau.clone());
        let (h, t, h2, t2) = (vars("h"), vars("t"), vars("h2"), vars("t2"));
        for k in [0usize, 1] {
            let inj = th
                .facts
                .injective(2, k, &[h.clone(), t.clone()], &[h2.clone(), t2.clone()])
                .unwrap();
            assert!(inj.hyps().is_empty(), "injective(2,{k}) must be closed");
        }
    }

    /// All six ordered distinctness pairs are theorems.
    #[test]
    fn distinctness_all_pairs() {
        let th = theory();
        let cs = carved().unwrap();
        let b = Term::free("b", bytes_ty());
        let h = Term::free("h", cs.tau.clone());
        let t = Term::free("t", cs.tau.clone());
        let args: [&[Term]; 3] = [&[b], &[], &[h, t]];
        for i in 0..3 {
            for j in 0..3 {
                if i == j {
                    continue;
                }
                let d = th.facts.distinct(i, j, args[i], args[j]).unwrap();
                assert!(d.hyps().is_empty(), "distinct({i},{j}) must be closed");
            }
        }
    }

    /// The paramorphic equations serve raw arguments: `pcomp` at `scons`
    /// concludes `∀h t. prec s⃗ (scons h t) = s₂ h t (prec s⃗ h) (prec s⃗ t)`.
    #[test]
    fn pcomp_scons_shape() {
        let th = theory();
        let cs = carved().unwrap();
        let beta = Type::nat();
        let tys = para_step_tys(&cs.tau, &beta);
        let steps: Vec<Term> = ["sa", "sn", "sc"]
            .iter()
            .zip(tys)
            .map(|(n, ty)| Term::free(*n, ty))
            .collect();
        let pc = th.facts.pcomp(&steps, 2).unwrap();
        assert!(pc.hyps().is_empty());
        let h = Term::free("h", cs.tau.clone());
        let t = Term::free("t", cs.tau.clone());
        let inst = pc.all_elim(h.clone()).unwrap().all_elim(t.clone()).unwrap();
        let lhs = th
            .facts
            .prec_app(
                &steps,
                &cs.scons
                    .clone()
                    .apply(h.clone())
                    .unwrap()
                    .apply(t.clone())
                    .unwrap(),
            )
            .unwrap();
        let rhs = steps[2]
            .clone()
            .apply(h.clone())
            .unwrap()
            .apply(t.clone())
            .unwrap()
            .apply(th.facts.prec_app(&steps, &h).unwrap())
            .unwrap()
            .apply(th.facts.prec_app(&steps, &t).unwrap())
            .unwrap();
        assert_eq!(inst.concl(), &lhs.equals(rhs).unwrap());
    }

    /// ACL2-default projections: `car (atom b) = snil`, `car snil = snil`.
    #[test]
    fn leaf_projections_default_to_snil() {
        let cs = carved().unwrap();
        let b = Term::free("b", bytes_ty());
        for take_cdr in [false, true] {
            let a = cs.proj_leaf(take_cdr, LeafKind::Atom(&b)).unwrap();
            assert!(a.hyps().is_empty());
            assert_eq!(a.concl().as_eq().unwrap().1, &cs.snil);
            let n = cs.proj_leaf(take_cdr, LeafKind::Nil).unwrap();
            assert!(n.hyps().is_empty());
            assert_eq!(n.concl().as_eq().unwrap().1, &cs.snil);
        }
    }
}
