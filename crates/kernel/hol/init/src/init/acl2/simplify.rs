//! **The generic premise builder** — an object-level, derivation-emitting
//! simplifier + IH splicer (design
//! `notes/vibes/lisp/acl2-premise-builder.md`): goal + induction variable
//! → the exact base/step premise theorems the IND (and IND-ORD) clause
//! consumes, produced automatically.
//!
//! Architecture (design §2): **plan-then-emit**. The [`Planner`] first
//! builds an *untrusted syntactic rewrite plan* ([`Rw`]/[`Holds`] trees —
//! pure Rust, no kernel calls except cached ground-computation facts,
//! budget-bounded), then the emitter turns exactly the plan nodes used
//! into [`super::hilbert::Script`] steps over the committed derivation
//! constructors (`axiom_inst`/`def_inst`/`cong_impl`/`mp`/`eq_trans`/
//! `derive_under`). Every emitted step is kernel-re-checked; a wrong
//! plan errors — it never mints. Rule sources (§5.2, the complete list):
//!
//! - **R1** congruence descent (`CongImpl` rows; never into `IF`),
//! - **R2** guard-disciplined user-row `Def` unfolding (committed only
//!   if the unfolded body's leading `IF` resolves; else rolled back),
//! - **R3** `IF` resolution (`if-true`/`if-false` on the guard *as
//!   written*),
//! - **R4** hypothesis/IH rewrites (ground `EQUAL` hypotheses, L→R),
//! - **R5** computation folding ([`comp_fact`] — the generalized
//!   `comp_cert`),
//! - **R6** oriented axiom rewrites from a tiny hand-audited allowlist
//!   (`car-cons`/`cdr-cons`, plus the §8 arithmetic rows), side
//!   conditions to the holds-prover.
//!
//! Hypothesis-free plan subtrees emit as single [`Fact`]s (decision 4 —
//! the deduction-compiler cost fix), and repeated schema/def/computation
//! instances are memoized in the [`FactCache`] (§10). Failures are
//! structured [`IndFailure`] values — the builder never asserts.

use std::cell::{Cell, RefCell};
use std::fmt;

use covalence_core::{Error, Result, Term, Type};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{as_int, mk_int};
use smol_str::SmolStr;

use crate::init::acl2::defun::{Acl2Session, defun_ground};
use crate::init::acl2::derivable::{
    Acl2Env, AxiomRow, Discharge, derivable, derive_axiom, derive_comp, derive_comp_folded,
    derive_def, derive_ind, derive_ind_ord, derive_inst, finite_sigma, model_eq_target,
    model_implies_target, object_vars, parse_equal, strip_implies, subst_ground, sym_lit_of,
    transport_equal, transport_equal_open, uncons,
};
use crate::init::acl2::hilbert::{Fact, KCache, Script, cong_impl, equal_parts, mp};
use crate::init::acl2::ordinal::ordinals;
use crate::init::acl2::prims::prims;
use crate::init::acl2::term::Terms;
use crate::init::coprod::cases as coprod_cases;
use crate::init::eq::beta_reduce;
use crate::init::ext::{TermExt, ThmExt};
use crate::init::int;
use crate::init::logic::exists_elim;

fn bad(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("acl2 simplify: {}", msg.into()))
}

// ============================================================================
// Failure reporting (design §7.3 — the honest rejection values)
// ============================================================================

/// Why a plan (or the whole builder) got stuck. Every failure is a
/// value — nothing is asserted, nothing minted.
#[derive(Clone)]
pub enum Stuck {
    /// Both sides of an `EQUAL` goal normalized, but to different forms.
    Join { lhs_nf: Term, rhs_nf: Term },
    /// A holds-goal reduced to an unresolved `IF` guard / stuck form.
    Guard { guard: Term },
    /// An R6 rule matched but its side condition was not discharged.
    SideCondition { axiom: SmolStr, cond: Term },
    /// A plan budget was exhausted (`what` names which).
    Budget { what: &'static str },
    /// The goal (or a subterm) is outside the deep ground fragment.
    OutOfFragment { term: Term, why: String },
    /// An unexpected kernel error during emission (a builder bug — the
    /// kernel refused a step; nothing was minted).
    Kernel { msg: String },
}

impl From<Error> for Stuck {
    fn from(e: Error) -> Self {
        Stuck::Kernel { msg: e.to_string() }
    }
}

impl fmt::Display for Stuck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stuck::Join { lhs_nf, rhs_nf } => write!(
                f,
                "sides normalize to {lhs_nf} vs {rhs_nf} — no rule closes the gap"
            ),
            Stuck::Guard { guard } => write!(f, "stuck on unresolved guard {guard}"),
            Stuck::SideCondition { axiom, cond } => {
                write!(f, "side condition {cond} of `{axiom}` not discharged")
            }
            Stuck::Budget { what } => write!(f, "budget exhausted ({what})"),
            Stuck::OutOfFragment { term, why } => {
                write!(f, "outside the deep fragment ({term}): {why}")
            }
            Stuck::Kernel { msg } => write!(f, "kernel refused an emission step: {msg}"),
        }
    }
}

impl fmt::Debug for Stuck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Which premise of an attempt failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PremiseId {
    /// The simplifier-only (no-induction) pass.
    NoInduction,
    /// The base premise.
    Base,
    /// The step premise.
    Step,
    /// The `i`-th IND-ORD obligation (0 = `O-P`, 1.. = decreases).
    Obligation(usize),
    /// Projection/transport of a successful derivation.
    Transport,
}

/// One failed attempt (candidate variable × failing premise × why).
#[derive(Clone)]
pub struct Attempt {
    /// The induction variable tried (`None` = the simplifier-only pass).
    pub var: Option<Vec<u8>>,
    /// Which premise got stuck.
    pub premise: PremiseId,
    /// Why.
    pub stuck: Stuck,
}

impl fmt::Display for Attempt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.var {
            None => write!(f, "simplification: {}", self.stuck),
            Some(v) => write!(
                f,
                "induction on {}: {:?} premise stuck: {}",
                String::from_utf8_lossy(v),
                self.premise,
                self.stuck
            ),
        }
    }
}

/// The structured rejection: every attempt, in order. Rendered into the
/// surface rejection text by the lang-side wiring (P1).
#[derive(Clone)]
pub struct IndFailure {
    /// Every attempt made, in order.
    pub attempts: Vec<Attempt>,
}

impl fmt::Display for IndFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for a in &self.attempts {
            if !first {
                write!(f, "; also tried ")?;
            }
            write!(f, "{a}")?;
            first = false;
        }
        Ok(())
    }
}

impl fmt::Debug for IndFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

type SResult<T> = std::result::Result<T, Stuck>;

// ============================================================================
// Budgets (design §5.4)
// ============================================================================

/// The plan budgets. Exhaustion = a stuck report, never a wrong answer.
#[derive(Clone, Copy)]
pub struct Limits {
    /// Committed `Def` unfolds per position (R2).
    pub unfolds_per_position: usize,
    /// Head-loop iterations per position.
    pub head_steps: usize,
    /// Total plan nodes per `norm`/`holds` run.
    pub plan_nodes: usize,
    /// Cases-split depth of the holds-prover.
    pub holds_depth: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            unfolds_per_position: 1,
            head_steps: 8,
            plan_nodes: 2_000,
            holds_depth: 3,
        }
    }
}

// ============================================================================
// The FactCache (design §10.1)
// ============================================================================

/// Memoizes the raw clause firings (`derive_axiom`/`derive_def` — one
/// `derive_mixed` walk each), their ground instances, and computation
/// facts, plus the deduction-compiler's schema instances ([`KCache`]).
/// Purely a cost lever: every value is a re-checked derivation, keyed by
/// the exact instance terms, and every consumer re-checks statements —
/// a wrong entry errors, it never mis-derives. **Per env generation**:
/// derivations do not transport across generations, so keep the cache
/// beside the session and drop it with it (a stale cross-env entry
/// would fail the `Step::Fact` re-check downstream — fail-safe).
#[derive(Default)]
pub struct FactCache {
    /// The deduction-compiler instance cache (shared with `Script::close`).
    pub kc: KCache,
    ax_raw: RefCell<Vec<(SmolStr, Fact)>>,
    ax_inst: RefCell<Vec<((SmolStr, Vec<(Vec<u8>, Term)>), Fact)>>,
    def_raw: RefCell<Vec<(SmolStr, Fact)>>,
    def_inst: RefCell<Vec<((SmolStr, Vec<(Vec<u8>, Term)>), Fact)>>,
    comp: RefCell<Vec<((usize, Vec<Term>), Option<Fact>)>>,
}

/// INST a derived fact at a finite substitution, folding the image
/// through [`subst_ground`] (the committed `axiom_inst` recipe).
fn inst_fact(env: &Acl2Env, f: &Fact, binds: &[(Vec<u8>, Term)]) -> Result<Fact> {
    let b: Vec<(&[u8], Term)> = binds
        .iter()
        .map(|(n, t)| (n.as_slice(), t.clone()))
        .collect();
    let s = finite_sigma(&env.tm, &b)?;
    let raw = derive_inst(env, &f.phi, &s, f.thm.clone())?;
    let fold = subst_ground(&env.tm, &f.phi, &s)?;
    let phi = fold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    Ok(Fact {
        phi,
        thm: raw.rewrite(&fold)?,
    })
}

fn sorted_key(name: &str, binds: &[(Vec<u8>, Term)]) -> (SmolStr, Vec<(Vec<u8>, Term)>) {
    let mut k = binds.to_vec();
    k.sort_by(|a, b| a.0.cmp(&b.0));
    (SmolStr::new(name), k)
}

impl FactCache {
    fn axiom_raw(&self, env: &Acl2Env, name: &str) -> Result<Fact> {
        if let Some((_, f)) = self.ax_raw.borrow().iter().find(|(n, _)| n == name) {
            return Ok(f.clone());
        }
        let (_, enc) = env.axiom(name)?;
        let f = Fact {
            phi: enc.clone(),
            thm: derive_axiom(env, name)?,
        };
        self.ax_raw
            .borrow_mut()
            .push((SmolStr::new(name), f.clone()));
        Ok(f)
    }

    /// Cached `axiom_inst` (owned binds).
    pub fn axiom_inst(&self, env: &Acl2Env, name: &str, binds: &[(Vec<u8>, Term)]) -> Result<Fact> {
        if binds.is_empty() {
            return self.axiom_raw(env, name);
        }
        let key = sorted_key(name, binds);
        if let Some((_, f)) = self.ax_inst.borrow().iter().find(|(k, _)| *k == key) {
            return Ok(f.clone());
        }
        let raw = self.axiom_raw(env, name)?;
        let f = inst_fact(env, &raw, binds)?;
        self.ax_inst.borrow_mut().push((key, f.clone()));
        Ok(f)
    }

    fn def_raw(&self, env: &Acl2Env, sym: &str) -> Result<Fact> {
        if let Some((_, f)) = self.def_raw.borrow().iter().find(|(n, _)| n == sym) {
            return Ok(f.clone());
        }
        let (j, u) = env.user(sym)?;
        let f = Fact {
            phi: u.def_enc.clone(),
            thm: derive_def(env, j)?,
        };
        self.def_raw
            .borrow_mut()
            .push((SmolStr::new(sym), f.clone()));
        Ok(f)
    }

    /// Cached `def_inst` (owned binds).
    pub fn def_inst(&self, env: &Acl2Env, sym: &str, binds: &[(Vec<u8>, Term)]) -> Result<Fact> {
        if binds.is_empty() {
            return self.def_raw(env, sym);
        }
        let key = sorted_key(sym, binds);
        if let Some((_, f)) = self.def_inst.borrow().iter().find(|(k, _)| *k == key) {
            return Ok(f.clone());
        }
        let raw = self.def_raw(env, sym)?;
        let f = inst_fact(env, &raw, binds)?;
        self.def_inst.borrow_mut().push((key, f.clone()));
        Ok(f)
    }

    /// Cached [`comp_fact`] (negative results cached too).
    pub fn comp(&self, env: &Acl2Env, k: usize, vals: &[Term]) -> Result<Option<Fact>> {
        let key = (k, vals.to_vec());
        if let Some((_, f)) = self.comp.borrow().iter().find(|(kk, _)| *kk == key) {
            return Ok(f.clone());
        }
        let f = comp_fact(env, k, vals)?;
        self.comp.borrow_mut().push((key, f.clone()));
        Ok(f)
    }
}

// ============================================================================
// Encoding helpers (untrusted, syntactic)
// ============================================================================

/// The payload of a `(QUOTE v)` encoding.
fn as_quote(tm: &Terms, t: &Term) -> Option<Term> {
    let (h, tail) = uncons(tm, t)?;
    if h != tm.qsym {
        return None;
    }
    let (v, rest) = uncons(tm, &tail)?;
    (rest == tm.th.nil).then_some(v)
}

/// `aint`-headed (self-evaluating integer literal)?
fn is_aint(tm: &Terms, t: &Term) -> bool {
    matches!(t.as_app(), Some((f, _)) if *f == tm.th.aint)
}

/// Split an application encoding into `(head bytes ≠ QUOTE, args)`.
/// `IF` is included (head `b"IF"`).
fn app_parts(tm: &Terms, t: &Term) -> Option<(Vec<u8>, Vec<Term>)> {
    let (h, tail) = uncons(tm, t)?;
    let name = sym_lit_of(tm, &h)?;
    if name == b"QUOTE" {
        return None;
    }
    let mut args = Vec::new();
    let mut cur = tail;
    while cur != tm.th.nil {
        let (a, rest) = uncons(tm, &cur)?;
        args.push(a);
        cur = rest;
    }
    Some((name, args))
}

/// Syntactic substitution over the ground pseudo-term fragment —
/// replicates exactly what [`subst_ground`] computes (identity default,
/// opaque quotes/ints, heads untouched), so the planner's images agree
/// with the emitted `INST` folds (asserted again at emission).
fn subst_pat(tm: &Terms, t: &Term, sigma: &[(Vec<u8>, Term)]) -> SResult<Term> {
    if *t == tm.th.nil {
        return Ok(t.clone());
    }
    if let Some(name) = sym_lit_of(tm, t) {
        return Ok(sigma
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| t.clone()));
    }
    if is_aint(tm, t) || as_quote(tm, t).is_some() {
        return Ok(t.clone());
    }
    let Some((name, args)) = app_parts(tm, t) else {
        return Err(Stuck::OutOfFragment {
            term: t.clone(),
            why: "not an encoded pseudo-term".into(),
        });
    };
    let new: Vec<Term> = args
        .iter()
        .map(|a| subst_pat(tm, a, sigma))
        .collect::<SResult<_>>()?;
    Ok(tm.app(&name, &new)?)
}

/// First-order matching over encodings (design §5.1): axiom encodings
/// double as patterns, their object variables are the pattern variables
/// (σ maps names to arbitrary encoded terms). Rust-only and unverified —
/// the emitted `axiom_inst` + MP chain is what the kernel checks.
fn match_enc(tm: &Terms, pat: &Term, t: &Term, sigma: &mut Vec<(Vec<u8>, Term)>) -> bool {
    if let Some(name) = sym_lit_of(tm, pat) {
        if let Some((_, v)) = sigma.iter().find(|(n, _)| *n == name) {
            return v == t;
        }
        sigma.push((name, t.clone()));
        return true;
    }
    if *pat == tm.th.nil || is_aint(tm, pat) || as_quote(tm, pat).is_some() {
        return pat == t;
    }
    let (Some((pn, pa)), Some((tn, ta))) = (app_parts(tm, pat), app_parts(tm, t)) else {
        return false;
    };
    pn == tn && pa.len() == ta.len() && pa.iter().zip(&ta).all(|(p, a)| match_enc(tm, p, a, sigma))
}

// ============================================================================
// R5 — computation folding (the generalized `comp_cert`, design §5.2)
// ============================================================================

fn as_aint_payload(tm: &Terms, v: &Term) -> Option<Term> {
    let (f, i) = v.as_app()?;
    (*f == tm.th.aint).then(|| i.clone())
}

fn as_aint_lit(tm: &Terms, v: &Term) -> Option<i128> {
    let i = as_int(&as_aint_payload(tm, v)?)?;
    i128::try_from(&i).ok()
}

fn as_asym_payload(tm: &Terms, v: &Term) -> Option<Term> {
    let (f, s) = v.as_app()?;
    (*f == tm.th.asym).then(|| s.clone())
}

/// The computation-clause fact for table row `k` at carrier values:
/// `⊢ D ⌜(EQUAL (F 'v⃗) 'w)⌝`, the model image folded by a public model
/// law (prim heads via the S1 law dispatch, user heads via
/// [`defun_ground`]). `Ok(None)` = no law covers these values — not a
/// rewrite (fail-safe, mirrors the committed `CertEngine::comp_cert`).
pub fn comp_fact(env: &Acl2Env, k: usize, vals: &[Term]) -> Result<Option<Fact>> {
    let tm = &*env.tm;
    let pr = tm.pr;
    let row = env
        .rows
        .get(k)
        .ok_or_else(|| bad(format!("comp_fact: bad table row {k}")))?;
    if vals.len() != row.arity {
        return Err(bad(format!(
            "comp_fact: row `{}` wants {} arguments",
            row.sym, row.arity
        )));
    }
    let sym = row.sym.as_str();
    let finish = |w: Term, thm: Thm| -> Result<Option<Fact>> {
        let qvals: Vec<Term> = vals.iter().map(|v| tm.quote(v)).collect::<Result<_>>()?;
        let phi = tm.mk_equal(&tm.app(sym.as_bytes(), &qvals)?, &tm.quote(&w)?)?;
        if thm.concl() != &derivable(env, &phi)? {
            return Err(bad(format!(
                "comp_fact: folded computation does not state ⌜(EQUAL (F 'v⃗) 'w)⌝ for {phi}"
            )));
        }
        Ok(Some(Fact { phi, thm }))
    };
    // CONS needs no fold: `acons v₀ v₁` IS the canonical value.
    if sym == "CONS" {
        let w = tm
            .th
            .cons
            .clone()
            .apply(vals[0].clone())?
            .apply(vals[1].clone())?;
        return finish(w, derive_comp(env, k, vals)?);
    }
    let law: Option<Thm> = match sym {
        "CAR" | "CDR" => {
            let cdr = sym == "CDR";
            let v = &vals[0];
            if let Some((h, t)) = uncons(tm, v) {
                let l = if cdr { pr.cdr_cons() } else { pr.car_cons() }?;
                Some(l.all_elim(h)?.all_elim(t)?)
            } else if *v == tm.th.nil {
                Some(if cdr { pr.cdr_nil() } else { pr.car_nil() }?)
            } else if let Some(i) = as_aint_payload(tm, v) {
                let l = if cdr { pr.cdr_int() } else { pr.car_int() }?;
                Some(l.all_elim(i)?)
            } else if let Some(s) = as_asym_payload(tm, v) {
                let l = if cdr { pr.cdr_sym() } else { pr.car_sym() }?;
                Some(l.all_elim(s)?)
            } else {
                None
            }
        }
        "CONSP" => {
            let v = &vals[0];
            if let Some((h, t)) = uncons(tm, v) {
                Some(pr.consp_cons()?.all_elim(h)?.all_elim(t)?)
            } else if *v == tm.th.nil {
                Some(pr.consp_nil()?)
            } else {
                None
            }
        }
        "INTEGERP" => {
            let v = &vals[0];
            if let Some(i) = as_aint_payload(tm, v) {
                Some(pr.intp_int()?.all_elim(i)?)
            } else if let Some(s) = as_asym_payload(tm, v) {
                Some(pr.intp_sym()?.all_elim(s)?)
            } else if *v == tm.th.nil {
                Some(pr.intp_nil()?)
            } else if let Some((h, t)) = uncons(tm, v) {
                Some(pr.intp_cons()?.all_elim(h)?.all_elim(t)?)
            } else {
                None
            }
        }
        "EQUAL" => {
            if vals[0] == vals[1] {
                Some(pr.equal_refl()?.all_elim(vals[0].clone())?)
            } else if let (Some(i), Some(j)) =
                (as_aint_lit(tm, &vals[0]), as_aint_lit(tm, &vals[1]))
            {
                let ne = pr.int_ne(i, j)?;
                Some(
                    pr.equal_ne()?
                        .all_elim(vals[0].clone())?
                        .all_elim(vals[1].clone())?
                        .imp_elim(ne)?,
                )
            } else {
                None
            }
        }
        "BINARY-+" => match (as_aint_lit(tm, &vals[0]), as_aint_lit(tm, &vals[1])) {
            (Some(i), Some(j)) => Some(pr.plus_lit(i, j)?),
            _ => None,
        },
        "<" => match (as_aint_lit(tm, &vals[0]), as_aint_lit(tm, &vals[1])) {
            (Some(i), Some(j)) => Some(pr.lt_lit(i, j)?),
            _ => None,
        },
        _ if env.user(sym).is_ok() => defun_ground(env, sym, vals).ok(),
        _ => None,
    };
    let Some(law) = law else {
        return Ok(None);
    };
    let w = law
        .concl()
        .as_eq()
        .ok_or_else(|| bad("comp_fact: model law is not an equation"))?
        .1
        .clone();
    finish(w, derive_comp_folded(env, k, vals, &law)?)
}

// ============================================================================
// The plan language (design §5.3)
// ============================================================================

/// A rewrite-plan node proving `(EQUAL from to)`.
#[derive(Clone)]
struct Rw {
    from: Term,
    to: Term,
    just: Just,
}

#[derive(Clone)]
enum Just {
    /// `from == to`.
    Refl,
    /// Chained rewrites.
    Trans(Vec<Rw>),
    /// Argument congruence for table row `k` (never `IF`).
    Cong { sym: SmolStr, args: Vec<Rw> },
    /// User-row unfold (`def_inst` at the reduced binds).
    Def {
        sym: SmolStr,
        binds: Vec<(Vec<u8>, Term)>,
    },
    /// `if-true` fired on `from = (IF c y z)` by `guard : c` holds.
    IfTrue { guard: Holds },
    /// `if-false` fired by `gnil : (EQUAL c 'NIL)`.
    IfFalse { gnil: Box<Rw> },
    /// The `i`-th hypothesis `(EQUAL from to)` used L→R (R4 — IH use).
    Hyp(usize),
    /// Computation clause for row `k` at values (R5).
    Comp { k: usize, vals: Vec<Term> },
    /// Oriented axiom rewrite (R6) with discharged side conditions.
    Ax {
        name: SmolStr,
        binds: Vec<(Vec<u8>, Term)>,
        conds: Vec<Holds>,
    },
}

impl Rw {
    fn refl(t: &Term) -> Rw {
        Rw {
            from: t.clone(),
            to: t.clone(),
            just: Just::Refl,
        }
    }
    fn is_refl(&self) -> bool {
        matches!(self.just, Just::Refl)
    }
}

/// Compose a chain (drop identities, flatten, check adjacency).
fn seq(from: &Term, parts: Vec<Rw>) -> SResult<Rw> {
    let mut flat: Vec<Rw> = Vec::new();
    for p in parts {
        match p.just {
            Just::Refl => {}
            Just::Trans(inner) => flat.extend(inner),
            _ => flat.push(p),
        }
    }
    match flat.len() {
        0 => Ok(Rw::refl(from)),
        1 => {
            let only = flat.pop().expect("len 1");
            if only.from != *from {
                return Err(Stuck::Kernel {
                    msg: format!("plan drift: chain starts at {} not {from}", only.from),
                });
            }
            Ok(only)
        }
        _ => {
            if flat[0].from != *from {
                return Err(Stuck::Kernel {
                    msg: format!("plan drift: chain starts at {} not {from}", flat[0].from),
                });
            }
            for w in flat.windows(2) {
                if w[0].to != w[1].from {
                    return Err(Stuck::Kernel {
                        msg: format!("plan drift: {} vs {}", w[0].to, w[1].from),
                    });
                }
            }
            Ok(Rw {
                from: flat[0].from.clone(),
                to: flat.last().expect("nonempty").to.clone(),
                just: Just::Trans(flat),
            })
        }
    }
}

/// A holds-plan node proving `D ⌜phi⌝`.
#[derive(Clone)]
struct Holds {
    phi: Term,
    just: HJust,
}

#[derive(Clone)]
enum HJust {
    /// The `i`-th hypothesis is `phi` verbatim.
    Hyp(usize),
    /// A holds-form axiom instance (`consp-cons`/`truth`/`equal-refl`/
    /// `integerp-plus`/…).
    Ax {
        name: SmolStr,
        binds: Vec<(Vec<u8>, Term)>,
    },
    /// `equal-mp` transport: `chain : (EQUAL phi phi*)`, `inner : phi*`.
    Transport { chain: Box<Rw>, inner: Box<Holds> },
    /// Classical case split on a stuck guard `q` (`cases` row): the two
    /// sub-proofs are hypothesis-free scripts under `[q]` /
    /// `[(EQUAL q 'NIL)]` (the Γ = ∅ variant, design §5.5.5).
    Cases {
        q: Term,
        pos: Box<SubHolds>,
        neg: Box<SubHolds>,
    },
}

/// A sub-proof of `D ⌜(IMPLIES hyp phi)⌝`, planned under context `[hyp]`.
#[derive(Clone)]
struct SubHolds {
    hyp: Term,
    plan: Holds,
}

// ============================================================================
// R6 rule table + holds-axiom table (data, not code — design §5.2/§8)
// ============================================================================

struct RwRule {
    name: SmolStr,
    conds: Vec<Term>,
    lhs: Term,
    rhs: Term,
}

/// The oriented-axiom allowlist: only these env axioms ever fire as
/// rewrite rules (jointly terminating — each strictly reduces `IF`
/// count, term size, or `+`-left-depth; risk register). Missing rows
/// are simply skipped.
const RW_ALLOWLIST: &[&str] = &["car-cons", "cdr-cons", "plus-assoc", "plus-zero-int"];

fn rw_table(env: &Acl2Env) -> Vec<RwRule> {
    let tm = &*env.tm;
    let mut out = Vec::new();
    for name in RW_ALLOWLIST {
        let Ok((_, enc)) = env.axiom(name) else {
            continue;
        };
        let mut conds = Vec::new();
        let mut cur = enc.clone();
        while let Some((p, q)) = strip_implies(tm, &cur) {
            conds.push(p);
            cur = q;
        }
        let Some((lhs, rhs)) = parse_equal(tm, &cur) else {
            continue;
        };
        out.push(RwRule {
            name: SmolStr::new(*name),
            conds,
            lhs,
            rhs,
        });
    }
    out
}

/// Holds-form axioms usable as match rules: any env axiom whose encoding
/// is a plain application form (not `IMPLIES`-shaped, not an `EQUAL`,
/// not a quote) — `consp-cons`, and post-S5c `integerp-plus`/
/// `integerp-neg`. Firing any of them is an `axiom_inst` — sound by
/// construction.
fn holds_table(env: &Acl2Env) -> Vec<(SmolStr, Term)> {
    let tm = &*env.tm;
    env.axioms
        .iter()
        .filter(|r| {
            strip_implies(tm, &r.enc).is_none()
                && parse_equal(tm, &r.enc).is_none()
                && app_parts(tm, &r.enc).is_some()
        })
        .map(|r| (r.name.clone(), r.enc.clone()))
        .collect()
}

// ============================================================================
// The planner (design §5.3–§5.5)
// ============================================================================

struct Planner<'e> {
    env: &'e Acl2Env,
    cache: &'e FactCache,
    hyps: Vec<Term>,
    limits: Limits,
    rw: Vec<RwRule>,
    holds_ax: Vec<(SmolStr, Term)>,
    has_cases: bool,
    has_equal_mp: bool,
    has_truth: bool,
    nodes: Cell<usize>,
    budget_hit: Cell<Option<&'static str>>,
    side: RefCell<Option<(SmolStr, Term)>>,
    stuck_guards: RefCell<Vec<Term>>,
}

impl<'e> Planner<'e> {
    fn new(env: &'e Acl2Env, cache: &'e FactCache, hyps: &[Term], limits: Limits) -> Planner<'e> {
        Planner {
            env,
            cache,
            hyps: hyps.to_vec(),
            limits,
            rw: rw_table(env),
            holds_ax: holds_table(env),
            has_cases: env.axiom("cases").is_ok(),
            has_equal_mp: env.axiom("equal-mp").is_ok(),
            has_truth: env.axiom("truth").is_ok(),
            nodes: Cell::new(0),
            budget_hit: Cell::new(None),
            side: RefCell::new(None),
            stuck_guards: RefCell::new(Vec::new()),
        }
    }

    fn tm(&self) -> &Terms {
        &self.env.tm
    }

    fn tick(&self) -> SResult<()> {
        let n = self.nodes.get() + 1;
        if n > self.limits.plan_nodes {
            return Err(Stuck::Budget { what: "plan nodes" });
        }
        self.nodes.set(n);
        Ok(())
    }

    /// The index of a hypothesis syntactically equal to `phi`.
    fn find_hyp(&self, phi: &Term) -> Option<usize> {
        self.hyps.iter().position(|h| h == phi)
    }

    /// The first `(EQUAL l r)`-shaped hypothesis with `l == cur` (R4).
    fn find_eq_hyp(&self, cur: &Term) -> Option<(usize, Term)> {
        let tm = self.tm();
        self.hyps.iter().enumerate().find_map(|(i, h)| {
            let (l, r) = parse_equal(tm, h)?;
            (l == *cur && l != r).then_some((i, r))
        })
    }

    /// **The normalizer** (design §5.3): innermost-out, one pass with
    /// retry-on-change at each head, budget-bounded.
    fn norm(&self, t: &Term) -> SResult<Rw> {
        self.tick()?;
        let tm = self.tm();
        // Atoms are normal forms.
        if *t == tm.th.nil
            || sym_lit_of(tm, t).is_some()
            || is_aint(tm, t)
            || as_quote(tm, t).is_some()
        {
            return Ok(Rw::refl(t));
        }
        let Some((name, args)) = app_parts(tm, t) else {
            return Err(Stuck::OutOfFragment {
                term: t.clone(),
                why: "not an encoded pseudo-term".into(),
            });
        };
        // R3 — `IF` resolution (no congruence into `IF`).
        if name == b"IF" {
            if args.len() != 3 {
                return Err(Stuck::OutOfFragment {
                    term: t.clone(),
                    why: "IF wants 3 arguments".into(),
                });
            }
            let (c, y, z) = (args[0].clone(), args[1].clone(), args[2].clone());
            let c_rw = self.norm(&c)?;
            let c_star = c_rw.to.clone();
            let qnil = tm.quote(&tm.th.nil).map_err(Stuck::from)?;
            // False?
            let gnil: Option<Rw> = if c_star == qnil {
                Some(c_rw.clone())
            } else {
                let want = tm.mk_equal(&c_star, &qnil).map_err(Stuck::from)?;
                self.find_hyp(&want)
                    .map(|i| {
                        seq(
                            &c,
                            vec![
                                c_rw.clone(),
                                Rw {
                                    from: c_star.clone(),
                                    to: qnil.clone(),
                                    just: Just::Hyp(i),
                                },
                            ],
                        )
                    })
                    .transpose()?
            };
            if let Some(g) = gnil {
                let fire = Rw {
                    from: t.clone(),
                    to: z.clone(),
                    just: Just::IfFalse { gnil: Box::new(g) },
                };
                let rest = self.norm(&z)?;
                return seq(t, vec![fire, rest]);
            }
            // True?
            if let Some(h) = self.guard_holds(&c, &c_rw)? {
                let fire = Rw {
                    from: t.clone(),
                    to: y.clone(),
                    just: Just::IfTrue { guard: h },
                };
                let rest = self.norm(&y)?;
                return seq(t, vec![fire, rest]);
            }
            // Stuck: record the guard, no descent into branches.
            self.stuck_guards.borrow_mut().push(c_star);
            return Ok(Rw::refl(t));
        }
        // Table application.
        let sym = String::from_utf8_lossy(&name).into_owned();
        if self.env.row(&sym).is_err() {
            return Err(Stuck::OutOfFragment {
                term: t.clone(),
                why: format!("unknown head `{sym}`"),
            });
        }
        // R1 — congruence descent into the arguments.
        let arg_rws: Vec<Rw> = args.iter().map(|a| self.norm(a)).collect::<SResult<_>>()?;
        let mut chain: Vec<Rw> = Vec::new();
        let mut cur = t.clone();
        if arg_rws.iter().any(|r| !r.is_refl()) {
            let tos: Vec<Term> = arg_rws.iter().map(|r| r.to.clone()).collect();
            let new_t = tm.app(&name, &tos).map_err(Stuck::from)?;
            chain.push(Rw {
                from: cur.clone(),
                to: new_t.clone(),
                just: Just::Cong {
                    sym: SmolStr::new(&sym),
                    args: arg_rws,
                },
            });
            cur = new_t;
        }
        // The head loop: R4 / R5 / R6 / R2, bounded.
        let mut unfolds_left = self.limits.unfolds_per_position;
        for _ in 0..self.limits.head_steps {
            let Some((cname, cargs)) = app_parts(tm, &cur) else {
                break; // rewritten to an atom — normal form
            };
            if cname == b"IF" {
                break; // an IF at head was already handled by re-norm
            }
            let csym = String::from_utf8_lossy(&cname).into_owned();
            let Ok(ck) = self.env.row(&csym) else {
                return Err(Stuck::OutOfFragment {
                    term: cur.clone(),
                    why: format!("unknown head `{csym}`"),
                });
            };
            // R4 — hypothesis/IH rewrite at this position.
            if let Some((i, r)) = self.find_eq_hyp(&cur) {
                chain.push(Rw {
                    from: cur.clone(),
                    to: r.clone(),
                    just: Just::Hyp(i),
                });
                let rest = self.norm(&r)?;
                cur = rest.to.clone();
                chain.push(rest);
                continue;
            }
            // R5 — computation folding at all-quoted arguments.
            if let Some(vals) = cargs
                .iter()
                .map(|a| as_quote(tm, a))
                .collect::<Option<Vec<Term>>>()
            {
                if let Some(f) = self.cache.comp(self.env, ck, &vals).map_err(Stuck::from)? {
                    let (_, to) = equal_parts(self.env, &f.phi).map_err(Stuck::from)?;
                    chain.push(Rw {
                        from: cur.clone(),
                        to,
                        just: Just::Comp { k: ck, vals },
                    });
                    break; // values are normal forms
                }
            }
            // R6 — oriented axiom rewrite.
            let mut fired = false;
            for rule in &self.rw {
                let mut sigma = Vec::new();
                if !match_enc(tm, &rule.lhs, &cur, &mut sigma) {
                    continue;
                }
                let mut conds_h = Vec::new();
                let mut ok = true;
                for cond_pat in &rule.conds {
                    let cond = subst_pat(tm, cond_pat, &sigma)?;
                    match self.holds(&cond, self.limits.holds_depth) {
                        Ok(h) => conds_h.push(h),
                        Err(_) => {
                            *self.side.borrow_mut() = Some((rule.name.clone(), cond));
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                let to = subst_pat(tm, &rule.rhs, &sigma)?;
                chain.push(Rw {
                    from: cur.clone(),
                    to: to.clone(),
                    just: Just::Ax {
                        name: rule.name.clone(),
                        binds: sigma,
                        conds: conds_h,
                    },
                });
                let rest = self.norm(&to)?;
                cur = rest.to.clone();
                chain.push(rest);
                fired = true;
                break;
            }
            if fired {
                continue;
            }
            // R2 — guard-disciplined Def unfold.
            if let Ok((_, u)) = self.env.user(&csym) {
                if unfolds_left == 0 {
                    self.budget_hit.set(Some("unfolds"));
                    break;
                }
                unfolds_left -= 1;
                let full_binds: Vec<(Vec<u8>, Term)> = u
                    .formals
                    .iter()
                    .zip(&cargs)
                    .map(|(f, a)| (f.as_bytes().to_vec(), a.clone()))
                    .collect();
                let body_inst = subst_pat(tm, &u.body, &full_binds)?;
                let inner = self.norm(&body_inst)?;
                // Commit only if the body's leading IF resolved (the
                // §0.2 discipline: a stuck-guard unfold is rolled back;
                // the guard was recorded by the inner IF handling).
                let if_headed = matches!(app_parts(tm, &body_inst), Some((n, _)) if n == b"IF");
                if if_headed && inner.is_refl() {
                    break; // rollback — plan-only, costs nothing
                }
                let reduced_binds: Vec<(Vec<u8>, Term)> = u
                    .formals
                    .iter()
                    .zip(&cargs)
                    .filter(|(f, a)| match tm.sym(f.as_bytes()) {
                        Ok(fs) => fs != **a,
                        Err(_) => true,
                    })
                    .map(|(f, a)| (f.as_bytes().to_vec(), a.clone()))
                    .collect();
                chain.push(Rw {
                    from: cur.clone(),
                    to: body_inst.clone(),
                    just: Just::Def {
                        sym: u.name.clone(),
                        binds: reduced_binds,
                    },
                });
                cur = inner.to.clone();
                chain.push(inner);
                continue;
            }
            break;
        }
        seq(t, chain)
    }

    /// R3-true guard evidence: the guard *as written* by a hypothesis or
    /// a primitive holds-match; across the simplified form only via
    /// `equal-mp` (pack envs — the design's P0 restriction falls out).
    fn guard_holds(&self, c: &Term, c_rw: &Rw) -> SResult<Option<Holds>> {
        if let Some(i) = self.find_hyp(c) {
            return Ok(Some(Holds {
                phi: c.clone(),
                just: HJust::Hyp(i),
            }));
        }
        if let Some(h) = self.holds_primitive(c)? {
            return Ok(Some(h));
        }
        if !c_rw.is_refl() && self.has_equal_mp {
            let c_star = &c_rw.to;
            let inner = if let Some(i) = self.find_hyp(c_star) {
                Some(Holds {
                    phi: c_star.clone(),
                    just: HJust::Hyp(i),
                })
            } else {
                self.holds_primitive(c_star)?
            };
            if let Some(inner) = inner {
                return Ok(Some(Holds {
                    phi: c.clone(),
                    just: HJust::Transport {
                        chain: Box::new(c_rw.clone()),
                        inner: Box::new(inner),
                    },
                }));
            }
        }
        Ok(None)
    }

    /// Context-free holds primitives: `'T` (`truth`), `(EQUAL a a)`
    /// (`equal-refl`), and the holds-form axiom table.
    fn holds_primitive(&self, phi: &Term) -> SResult<Option<Holds>> {
        let tm = self.tm();
        if self.has_truth && *phi == tm.quote(&tm.pr.t).map_err(Stuck::from)? {
            return Ok(Some(Holds {
                phi: phi.clone(),
                just: HJust::Ax {
                    name: SmolStr::new("truth"),
                    binds: vec![],
                },
            }));
        }
        if let Some((a, b)) = parse_equal(tm, phi)
            && a == b
        {
            return Ok(Some(Holds {
                phi: phi.clone(),
                just: HJust::Ax {
                    name: SmolStr::new("equal-refl"),
                    binds: vec![(b"X".to_vec(), a)],
                },
            }));
        }
        for (name, pat) in &self.holds_ax {
            let mut sigma = Vec::new();
            if match_enc(tm, pat, phi, &mut sigma) {
                return Ok(Some(Holds {
                    phi: phi.clone(),
                    just: HJust::Ax {
                        name: name.clone(),
                        binds: sigma,
                    },
                }));
            }
        }
        Ok(None)
    }

    /// **The holds-prover** (design §5.5): `D ⌜phi⌝`-shaped goals under
    /// the context — hypothesis match, primitives, normalize + transport,
    /// then the classical cases split on a stuck guard.
    fn holds(&self, phi: &Term, depth: usize) -> SResult<Holds> {
        self.tick()?;
        if let Some(i) = self.find_hyp(phi) {
            return Ok(Holds {
                phi: phi.clone(),
                just: HJust::Hyp(i),
            });
        }
        if let Some(h) = self.holds_primitive(phi)? {
            return Ok(h);
        }
        let snap = self.stuck_guards.borrow().len();
        let chain = self.norm(phi)?;
        if !chain.is_refl() && self.has_equal_mp {
            let phi_star = &chain.to;
            let inner = if let Some(i) = self.find_hyp(phi_star) {
                Some(Holds {
                    phi: phi_star.clone(),
                    just: HJust::Hyp(i),
                })
            } else {
                self.holds_primitive(phi_star)?
            };
            if let Some(inner) = inner {
                return Ok(Holds {
                    phi: phi.clone(),
                    just: HJust::Transport {
                        chain: Box::new(chain),
                        inner: Box::new(inner),
                    },
                });
            }
        }
        // Cases split on the leftmost stuck guard (Γ = ∅ variant: the
        // sub-scripts see only their own case hypothesis — cacheable,
        // hypothesis-free facts; the Γ-threading variant of §5.5.5 is
        // deferred, source-local TODO markers).
        let guard = self.stuck_guards.borrow().get(snap).cloned();
        if let (true, Some(q)) = (self.has_cases && depth > 0, guard.clone()) {
            let tm = self.tm();
            let qnil = tm
                .mk_equal(&q, &tm.quote(&tm.th.nil).map_err(Stuck::from)?)
                .map_err(Stuck::from)?;
            let pos = self.subholds(&q, phi, depth - 1)?;
            let neg = self.subholds(&qnil, phi, depth - 1)?;
            return Ok(Holds {
                phi: phi.clone(),
                just: HJust::Cases {
                    q,
                    pos: Box::new(pos),
                    neg: Box::new(neg),
                },
            });
        }
        Err(Stuck::Guard {
            guard: guard.unwrap_or_else(|| chain.to.clone()),
        })
    }

    fn subholds(&self, hyp: &Term, phi: &Term, depth: usize) -> SResult<SubHolds> {
        let sub = Planner::new(self.env, self.cache, std::slice::from_ref(hyp), self.limits);
        let plan = sub.holds(phi, depth)?;
        Ok(SubHolds {
            hyp: hyp.clone(),
            plan,
        })
    }

    /// Goal closure for `(EQUAL l r)` goals (design §5.6): normalize
    /// both sides, demand a syntactic join.
    fn close_equal(&self, phi: &Term) -> SResult<(Rw, Rw)> {
        let tm = self.tm();
        let Some((l, r)) = parse_equal(tm, phi) else {
            return Err(Stuck::OutOfFragment {
                term: phi.clone(),
                why: "not an (EQUAL l r) goal".into(),
            });
        };
        let lc = self.norm(&l)?;
        let rc = self.norm(&r)?;
        if lc.to != rc.to {
            if let Some(what) = self.budget_hit.get() {
                return Err(Stuck::Budget { what });
            }
            if let Some((axiom, cond)) = self.side.borrow_mut().take() {
                return Err(Stuck::SideCondition { axiom, cond });
            }
            return Err(Stuck::Join {
                lhs_nf: lc.to.clone(),
                rhs_nf: rc.to.clone(),
            });
        }
        Ok((lc, rc))
    }
}

// ============================================================================
// The emitter (design §4/§2): plans → Script steps/Facts
// ============================================================================

/// An emitted proof: a hypothesis-free [`Fact`] (untainted subtree) or a
/// script line (touches a `Hyp`). Combining an all-`Fact` node stays in
/// `Fact`-land — the hyp-taint factoring of design decision 4 falls out.
#[derive(Clone)]
enum L {
    F(Fact),
    Ln(usize),
}

fn push_l(sc: &mut Script, l: L) -> usize {
    match l {
        L::Ln(i) => i,
        L::F(f) => sc.fact(f),
    }
}

fn formula_of(sc: &Script, l: &L) -> Term {
    match l {
        L::F(f) => f.phi.clone(),
        L::Ln(i) => sc.phi(*i).clone(),
    }
}

fn cached_eq_refl(env: &Acl2Env, cache: &FactCache, x: &Term) -> Result<Fact> {
    cache.axiom_inst(env, "equal-refl", &[(b"X".to_vec(), x.clone())])
}

fn cached_eq_symm(env: &Acl2Env, cache: &FactCache, ab: &Fact) -> Result<Fact> {
    let (a, b) = equal_parts(env, &ab.phi)?;
    let sy = cache.axiom_inst(env, "equal-symm", &[(b"X".to_vec(), a), (b"Y".to_vec(), b)])?;
    mp(env, &sy, ab)
}

fn cached_eq_trans(env: &Acl2Env, cache: &FactCache, ab: &Fact, bc: &Fact) -> Result<Fact> {
    let (a, b) = equal_parts(env, &ab.phi)?;
    let (b2, c) = equal_parts(env, &bc.phi)?;
    if b != b2 {
        return Err(bad("eq_trans: middle terms differ"));
    }
    let tr = cache.axiom_inst(
        env,
        "equal-trans",
        &[(b"X".to_vec(), a), (b"Y".to_vec(), b), (b"Z".to_vec(), c)],
    )?;
    mp(env, &mp(env, &tr, ab)?, bc)
}

fn l_mp(env: &Acl2Env, sc: &mut Script, imp: L, p: L) -> Result<L> {
    match (imp, p) {
        (L::F(a), L::F(b)) => Ok(L::F(mp(env, &a, &b)?)),
        (a, b) => {
            let ja = push_l(sc, a);
            let jb = push_l(sc, b);
            Ok(L::Ln(sc.mp(ja, jb)?))
        }
    }
}

fn l_trans(env: &Acl2Env, cache: &FactCache, sc: &mut Script, ab: L, bc: L) -> Result<L> {
    match (ab, bc) {
        (L::F(a), L::F(b)) => Ok(L::F(cached_eq_trans(env, cache, &a, &b)?)),
        (a, b) => {
            let ja = push_l(sc, a);
            let jb = push_l(sc, b);
            Ok(L::Ln(sc.trans(ja, jb)?))
        }
    }
}

fn l_symm(env: &Acl2Env, cache: &FactCache, sc: &mut Script, ab: L) -> Result<L> {
    match ab {
        L::F(a) => Ok(L::F(cached_eq_symm(env, cache, &a)?)),
        a => {
            let ja = push_l(sc, a);
            Ok(L::Ln(sc.symm(ja)?))
        }
    }
}

/// Emit a rewrite plan node; the result proves `(EQUAL from to)` —
/// checked against the plan (risk register: planner/emitter drift is a
/// clean error naming the node, never a mis-derivation).
fn emit_rw(env: &Acl2Env, cache: &FactCache, sc: &mut Script, rw: &Rw) -> Result<L> {
    let tm = &*env.tm;
    let out = match &rw.just {
        Just::Refl => L::F(cached_eq_refl(env, cache, &rw.from)?),
        Just::Trans(parts) => {
            let mut acc: Option<L> = None;
            for p in parts {
                let e = emit_rw(env, cache, sc, p)?;
                acc = Some(match acc {
                    None => e,
                    Some(prev) => l_trans(env, cache, sc, prev, e)?,
                });
            }
            acc.ok_or_else(|| bad("empty Trans plan"))?
        }
        Just::Cong { sym, args } => {
            let pairs: Vec<(Term, Term)> = args
                .iter()
                .map(|a| (a.from.clone(), a.to.clone()))
                .collect();
            let ci = cong_impl(env, sym, &pairs)?;
            let mut acc = L::F(ci);
            for a in args {
                let pa = emit_rw(env, cache, sc, a)?;
                acc = l_mp(env, sc, acc, pa)?;
            }
            acc
        }
        Just::Def { sym, binds } => L::F(cache.def_inst(env, sym, binds)?),
        Just::IfTrue { guard } => {
            let (c, y, z) = if_parts(env, &rw.from)?;
            let ax = cache.axiom_inst(
                env,
                "if-true",
                &[(b"X".to_vec(), c), (b"Y".to_vec(), y), (b"Z".to_vec(), z)],
            )?;
            let g = emit_holds(env, cache, sc, guard)?;
            l_mp(env, sc, L::F(ax), g)?
        }
        Just::IfFalse { gnil } => {
            let (c, y, z) = if_parts(env, &rw.from)?;
            let ax = cache.axiom_inst(
                env,
                "if-false",
                &[(b"X".to_vec(), c), (b"Y".to_vec(), y), (b"Z".to_vec(), z)],
            )?;
            let g = emit_rw(env, cache, sc, gnil)?;
            l_mp(env, sc, L::F(ax), g)?
        }
        Just::Hyp(i) => L::Ln(sc.hyp(*i)?),
        Just::Comp { k, vals } => L::F(
            cache
                .comp(env, *k, vals)?
                .ok_or_else(|| bad("Comp plan node without a computation law"))?,
        ),
        Just::Ax { name, binds, conds } => {
            let f = cache.axiom_inst(env, name, binds)?;
            let mut acc = L::F(f);
            for cnd in conds {
                let hc = emit_holds(env, cache, sc, cnd)?;
                acc = l_mp(env, sc, acc, hc)?;
            }
            acc
        }
    };
    let want = tm.mk_equal(&rw.from, &rw.to)?;
    let got = formula_of(sc, &out);
    if got != want {
        return Err(bad(format!(
            "emission drift: derived {got}, planned {want}"
        )));
    }
    Ok(out)
}

/// Parse `⌜(IF c y z)⌝`.
fn if_parts(env: &Acl2Env, t: &Term) -> Result<(Term, Term, Term)> {
    let tm = &*env.tm;
    match app_parts(tm, t) {
        Some((n, args)) if n == b"IF" && args.len() == 3 => {
            Ok((args[0].clone(), args[1].clone(), args[2].clone()))
        }
        _ => Err(bad(format!("not an (IF c y z) encoding: {t}"))),
    }
}

/// Emit a holds plan node; the result proves `D ⌜phi⌝` (checked).
fn emit_holds(env: &Acl2Env, cache: &FactCache, sc: &mut Script, h: &Holds) -> Result<L> {
    let out = match &h.just {
        HJust::Hyp(i) => L::Ln(sc.hyp(*i)?),
        HJust::Ax { name, binds } => L::F(cache.axiom_inst(env, name, binds)?),
        HJust::Transport { chain, inner } => {
            let e = emit_rw(env, cache, sc, chain)?; // (EQUAL φ φ*)
            let se = l_symm(env, cache, sc, e)?; // (EQUAL φ* φ)
            let emp = cache.axiom_inst(
                env,
                "equal-mp",
                &[
                    (b"X".to_vec(), chain.to.clone()),
                    (b"Y".to_vec(), chain.from.clone()),
                ],
            )?;
            let step = l_mp(env, sc, L::F(emp), se)?; // (IMPLIES φ* φ)
            let il = emit_holds(env, cache, sc, inner)?;
            l_mp(env, sc, step, il)?
        }
        HJust::Cases { q, pos, neg } => {
            let pf = emit_subholds(env, cache, pos)?;
            let nf = emit_subholds(env, cache, neg)?;
            let cs = cache.axiom_inst(
                env,
                "cases",
                &[(b"X".to_vec(), q.clone()), (b"Y".to_vec(), h.phi.clone())],
            )?;
            L::F(mp(env, &mp(env, &cs, &pf)?, &nf)?)
        }
    };
    let got = formula_of(sc, &out);
    if got != h.phi {
        return Err(bad(format!(
            "emission drift: derived {got}, planned {}",
            h.phi
        )));
    }
    Ok(out)
}

/// Emit a cases branch as a hypothesis-free `⊢ D ⌜(IMPLIES hyp phi)⌝`
/// [`Fact`] (its own one-hypothesis script, closed by the compiler).
fn emit_subholds(env: &Acl2Env, cache: &FactCache, sub: &SubHolds) -> Result<Fact> {
    let mut sc = Script::new(env, std::slice::from_ref(&sub.hyp));
    let l = emit_holds(env, cache, &mut sc, &sub.plan)?;
    push_l(&mut sc, l);
    let thm = sc.close(&sub.plan.phi, &cache.kc)?;
    let phi = env.tm.mk_implies(&sub.hyp, &sub.plan.phi)?;
    Ok(Fact { phi, thm })
}

// ============================================================================
// Proving under hypotheses (the premise workhorse)
// ============================================================================

/// Prove `⊢ D ⌜(IMPLIES h₁ (… (IMPLIES hₖ goal)))⌝` fully automatically:
/// `(EQUAL l r)` goals through the both-sides normalizer + join
/// (design §5.6), anything else through the holds-prover (§5.5).
/// Failures are structured [`Stuck`] values; nothing is minted on
/// failure.
pub fn prove_under(
    env: &Acl2Env,
    cache: &FactCache,
    hyps: &[Term],
    goal: &Term,
    limits: &Limits,
) -> SResult<Thm> {
    let tm = &*env.tm;
    let p = Planner::new(env, cache, hyps, *limits);
    let mut sc = Script::new(env, hyps);
    let l = if parse_equal(tm, goal).is_some() {
        let (lc, rc) = p.close_equal(goal)?;
        emit_join(env, cache, &mut sc, goal, &lc, &rc).map_err(Stuck::from)?
    } else {
        let h = p.holds(goal, limits.holds_depth)?;
        emit_holds(env, cache, &mut sc, &h).map_err(Stuck::from)?
    };
    let got = formula_of(&sc, &l);
    if got != *goal {
        return Err(Stuck::Kernel {
            msg: format!("emission drift at the goal: {got} vs {goal}"),
        });
    }
    push_l(&mut sc, l);
    sc.close(goal, &cache.kc).map_err(Stuck::from)
}

/// Join the two side chains into the goal line (`trans`/`symm`,
/// degenerate cases included).
fn emit_join(
    env: &Acl2Env,
    cache: &FactCache,
    sc: &mut Script,
    goal: &Term,
    lc: &Rw,
    rc: &Rw,
) -> Result<L> {
    let out = match (lc.is_refl(), rc.is_refl()) {
        (true, true) => {
            // L == R (the planner joined trivially).
            if lc.from != rc.from {
                return Err(bad("join: refl sides differ"));
            }
            L::F(cached_eq_refl(env, cache, &lc.from)?)
        }
        (false, true) => emit_rw(env, cache, sc, lc)?,
        (true, false) => {
            let er = emit_rw(env, cache, sc, rc)?;
            l_symm(env, cache, sc, er)?
        }
        (false, false) => {
            let el = emit_rw(env, cache, sc, lc)?;
            let er = emit_rw(env, cache, sc, rc)?;
            let ser = l_symm(env, cache, sc, er)?;
            l_trans(env, cache, sc, el, ser)?
        }
    };
    let got = formula_of(sc, &out);
    if got != *goal {
        return Err(bad(format!("join drift: {got} vs {goal}")));
    }
    Ok(out)
}

// ============================================================================
// Premise assembly (design §6)
// ============================================================================

/// The automatically built IND premises for `phi` at variable `v`.
pub struct IndPremises {
    /// `(EQUAL (CONSP v) 'NIL)`.
    pub g: Term,
    /// `(CONSP v)`.
    pub c: Term,
    /// `φ[v ↦ (CAR v)]` / `φ[v ↦ (CDR v)]` — **exactly** as
    /// [`derive_ind`] folds them ([`subst_ground`]).
    pub ihcar: Term,
    /// See [`IndPremises::ihcar`].
    pub ihcdr: Term,
    /// `⊢ D ⌜(IMPLIES g φ)⌝`.
    pub base: Thm,
    /// `⊢ D ⌜(IMPLIES c (IMPLIES ihcar (IMPLIES ihcdr φ)))⌝`.
    pub step: Thm,
}

/// The substitution image `φ[v ↦ e]` in [`subst_ground`]'s exact shape.
fn subst_image(tm: &Terms, phi: &Term, v: &[u8], e: &Term) -> Result<Term> {
    let s = finite_sigma(tm, &[(v, e.clone())])?;
    Ok(subst_ground(tm, phi, &s)?
        .concl()
        .as_eq()
        .ok_or(Error::NotAnEquation)?
        .1
        .clone())
}

/// Build the two structural-IND premises for `phi` at `v` (design §6.1)
/// — the literal premise statements [`derive_ind`] expects.
pub fn build_ind_premises(
    env: &Acl2Env,
    cache: &FactCache,
    phi: &Term,
    v: &[u8],
    limits: &Limits,
) -> std::result::Result<IndPremises, (PremiseId, Stuck)> {
    let tm = &*env.tm;
    let shapes = || -> Result<(Term, Term, Term, Term)> {
        let c = tm.app(b"CONSP", &[tm.sym(v)?])?;
        let g = tm.mk_equal(&c, &tm.quote(&tm.th.nil)?)?;
        let ihcar = subst_image(tm, phi, v, &tm.app(b"CAR", &[tm.sym(v)?])?)?;
        let ihcdr = subst_image(tm, phi, v, &tm.app(b"CDR", &[tm.sym(v)?])?)?;
        Ok((c, g, ihcar, ihcdr))
    };
    let (c, g, ihcar, ihcdr) = shapes().map_err(|e| (PremiseId::Base, Stuck::from(e)))?;
    let base = prove_under(env, cache, std::slice::from_ref(&g), phi, limits)
        .map_err(|s| (PremiseId::Base, s))?;
    let step = prove_under(
        env,
        cache,
        &[c.clone(), ihcar.clone(), ihcdr.clone()],
        phi,
        limits,
    )
    .map_err(|s| (PremiseId::Step, s))?;
    Ok(IndPremises {
        g,
        c,
        ihcar,
        ihcdr,
        base,
        step,
    })
}

/// How an IND-ORD obligation is produced (design §6.2): automatically
/// (holds-prover) or supplied by the caller (e.g. the S5d G4 obligation
/// scripts) — a `Given` theorem is statement-checked here and re-checked
/// by [`derive_ind_ord`].
pub enum ObligationSource {
    /// Build it with the holds-prover.
    Auto,
    /// Use this derivation (must state exactly the expected obligation).
    Given(Thm),
}

/// The measured-induction shape: measure `m`, guard `q`, descents `ts`,
/// and the obligation sources.
pub struct IndOrdSpec {
    /// The measure encoding, e.g. `(ACL2-COUNT X)`.
    pub m: Term,
    /// The guard encoding, e.g. `(CONSP X)`.
    pub q: Term,
    /// The descent terms, e.g. `[(CDR X)]`.
    pub ts: Vec<Term>,
    /// Source for `⊢ D ⌜(O-P m)⌝`.
    pub d_op: ObligationSource,
    /// Sources for the guarded decreases (one per descent).
    pub d_decs: Vec<ObligationSource>,
}

/// The built IND-ORD premises (design §6.2).
pub struct IndOrdPremises {
    /// `⊢ D ⌜(O-P m)⌝`.
    pub d_op: Thm,
    /// `⊢ D ⌜(IMPLIES q (O< m[v↦tᵢ] m))⌝`.
    pub d_decs: Vec<Thm>,
    /// `⊢ D ⌜(IMPLIES (EQUAL q 'NIL) φ)⌝`.
    pub base: Thm,
    /// `⊢ D ⌜(IMPLIES q (IMPLIES φ[v↦t₁] (… φ)))⌝`.
    pub step: Thm,
}

/// Build the IND-ORD premises for `phi` at `v` under `spec` — the
/// reduced statements [`derive_ind_ord`] expects.
pub fn build_ind_ord_premises(
    env: &Acl2Env,
    cache: &FactCache,
    phi: &Term,
    v: &[u8],
    spec: &IndOrdSpec,
    limits: &Limits,
) -> std::result::Result<IndOrdPremises, (PremiseId, Stuck)> {
    let tm = &*env.tm;
    if spec.d_decs.len() != spec.ts.len() {
        return Err((
            PremiseId::Obligation(0),
            Stuck::Kernel {
                msg: "one decrease source per descent term required".into(),
            },
        ));
    }
    let check_given = |thm: &Thm, enc: &Term| -> Result<()> {
        if !thm.hyps().is_empty() || thm.concl() != &derivable(env, enc)? {
            return Err(bad(format!("Given obligation does not state ⊢ D ⌜{enc}⌝")));
        }
        Ok(())
    };
    // O-P m.
    let opm = tm
        .app(b"O-P", std::slice::from_ref(&spec.m))
        .map_err(|e| (PremiseId::Obligation(0), Stuck::from(e)))?;
    let d_op = match &spec.d_op {
        ObligationSource::Given(t) => {
            check_given(t, &opm).map_err(|e| (PremiseId::Obligation(0), Stuck::from(e)))?;
            t.clone()
        }
        ObligationSource::Auto => {
            prove_under(env, cache, &[], &opm, limits).map_err(|s| (PremiseId::Obligation(0), s))?
        }
    };
    // Guarded decreases.
    let mut d_decs = Vec::with_capacity(spec.ts.len());
    for (i, (t_i, src)) in spec.ts.iter().zip(&spec.d_decs).enumerate() {
        let oi = PremiseId::Obligation(1 + i);
        let mk = || -> Result<Term> {
            let m_i = subst_image(tm, &spec.m, v, t_i)?;
            tm.app(b"O<", &[m_i, spec.m.clone()])
        };
        let dec_goal = mk().map_err(|e| (oi, Stuck::from(e)))?;
        let dec = match src {
            ObligationSource::Given(t) => {
                let enc = tm
                    .mk_implies(&spec.q, &dec_goal)
                    .map_err(|e| (oi, Stuck::from(e)))?;
                check_given(t, &enc).map_err(|e| (oi, Stuck::from(e)))?;
                t.clone()
            }
            ObligationSource::Auto => {
                prove_under(env, cache, std::slice::from_ref(&spec.q), &dec_goal, limits)
                    .map_err(|s| (oi, s))?
            }
        };
        d_decs.push(dec);
    }
    // Base + step.
    let gq = tm
        .mk_equal(
            &spec.q,
            &tm.quote(&tm.th.nil)
                .map_err(|e| (PremiseId::Base, Stuck::from(e)))?,
        )
        .map_err(|e| (PremiseId::Base, Stuck::from(e)))?;
    let base = prove_under(env, cache, std::slice::from_ref(&gq), phi, limits)
        .map_err(|s| (PremiseId::Base, s))?;
    let mut step_hyps = vec![spec.q.clone()];
    for t_i in &spec.ts {
        step_hyps
            .push(subst_image(tm, phi, v, t_i).map_err(|e| (PremiseId::Step, Stuck::from(e)))?);
    }
    let step =
        prove_under(env, cache, &step_hyps, phi, limits).map_err(|s| (PremiseId::Step, s))?;
    Ok(IndOrdPremises {
        d_op,
        d_decs,
        base,
        step,
    })
}

// ============================================================================
// The driver (design §7)
// ============================================================================

/// Which induction clause the driver uses.
pub enum IndScheme {
    /// The S6 structural clause ([`derive_ind`]).
    Structural,
    /// The S5d measured clause ([`derive_ind_ord`]) at the given shape.
    Measured(IndOrdSpec),
}

/// The driver configuration.
pub struct IndConfig {
    /// Plan budgets.
    pub limits: Limits,
    /// Induction scheme.
    pub scheme: IndScheme,
    /// Force a candidate variable (skip ranking).
    pub var: Option<Vec<u8>>,
}

impl Default for IndConfig {
    fn default() -> Self {
        IndConfig {
            limits: Limits::default(),
            scheme: IndScheme::Structural,
            var: None,
        }
    }
}

/// A successful automatic proof: derivation, projection, and the closed
/// base-HOL transport.
pub struct IndProof {
    /// The winning induction variable (`None` = simplifier-only, no
    /// induction was needed).
    pub var: Option<Vec<u8>>,
    /// `⊢ D ⌜φ⌝`.
    pub derivation: Thm,
    /// `⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil)`.
    pub projected: Thm,
    /// The closed base-HOL model theorem (`transport_equal[_open]`).
    pub transported: Thm,
}

impl fmt::Debug for IndProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "IndProof(var: {:?}, transported: {})",
            self.var
                .as_ref()
                .map(|v| String::from_utf8_lossy(v).into_owned()),
            self.transported
        )
    }
}

/// Candidate induction variables, ranked by **recursion votes**
/// (design §7.1): each application `(F a⃗)` with `F` a user row having
/// `rec_formal = r` and `a_r` a variable casts one vote. Zero-vote
/// variables stay in the list (last).
pub fn candidates(env: &Acl2Env, phi: &Term) -> Result<Vec<Vec<u8>>> {
    let tm = &*env.tm;
    let vars = object_vars(tm, phi)?;
    let mut votes: Vec<(Vec<u8>, usize)> = vars.into_iter().map(|v| (v, 0usize)).collect();
    fn walk(env: &Acl2Env, t: &Term, votes: &mut Vec<(Vec<u8>, usize)>) {
        let tm = &*env.tm;
        if *t == tm.th.nil
            || sym_lit_of(tm, t).is_some()
            || is_aint(tm, t)
            || as_quote(tm, t).is_some()
        {
            return;
        }
        let Some((name, args)) = app_parts(tm, t) else {
            return;
        };
        if name != b"IF" {
            let sym = String::from_utf8_lossy(&name).into_owned();
            if let Ok((_, u)) = env.user(&sym)
                && let Some(r) = u.rec_formal
                && let Some(a) = args.get(r)
                && let Some(vn) = sym_lit_of(tm, a)
                && let Some(entry) = votes.iter_mut().find(|(v, _)| *v == vn)
            {
                entry.1 += 1;
            }
        }
        for a in &args {
            walk(env, a, votes);
        }
    }
    walk(env, phi, &mut votes);
    // Stable sort by votes descending preserves first-occurrence ties.
    votes.sort_by(|a, b| b.1.cmp(&a.1));
    Ok(votes.into_iter().map(|(v, _)| v).collect())
}

/// **The full pipeline** (design §7.2): try the simplifier alone, then
/// per ranked candidate build premises → `derive_ind[_ord]` → project →
/// transport. First success wins; every failure is recorded in the
/// returned [`IndFailure`]. Nothing is stored or minted on failure.
pub fn prove_by_induction(
    sess: &Acl2Session,
    cache: &FactCache,
    phi: &Term,
    cfg: &IndConfig,
) -> std::result::Result<IndProof, IndFailure> {
    let env = sess.env();
    let tm = &*env.tm;
    let mut attempts: Vec<Attempt> = Vec::new();
    let fail1 = |stuck: Stuck| IndFailure {
        attempts: vec![Attempt {
            var: None,
            premise: PremiseId::NoInduction,
            stuck,
        }],
    };
    // Fragment guards.
    let vars = match object_vars(tm, phi) {
        Ok(v) => v,
        Err(e) => {
            return Err(fail1(Stuck::OutOfFragment {
                term: phi.clone(),
                why: e.to_string(),
            }));
        }
    };
    if strip_implies(tm, phi).is_some() {
        return Err(fail1(Stuck::OutOfFragment {
            term: phi.clone(),
            why: "IMPLIES-form goals are deferred (design §6.1, P1)".into(),
        }));
    }
    if parse_equal(tm, phi).is_none() {
        return Err(fail1(Stuck::OutOfFragment {
            term: phi.clone(),
            why: "driver goals must be (EQUAL l r)-shaped (holds-form goals deferred)".into(),
        }));
    }
    // Simplifier-only pass (closes goals needing only unfolding /
    // computation / R6 rules).
    match prove_under(env, cache, &[], phi, &cfg.limits) {
        Ok(der) => match finish(sess, phi, None, der, &vars) {
            Ok(p) => return Ok(p),
            Err(s) => attempts.push(Attempt {
                var: None,
                premise: PremiseId::Transport,
                stuck: s,
            }),
        },
        Err(s) => attempts.push(Attempt {
            var: None,
            premise: PremiseId::NoInduction,
            stuck: s,
        }),
    }
    // Candidate loop.
    let cands: Vec<Vec<u8>> = match &cfg.var {
        Some(v) => vec![v.clone()],
        None => match candidates(env, phi) {
            Ok(c) => c,
            Err(e) => {
                attempts.push(Attempt {
                    var: None,
                    premise: PremiseId::NoInduction,
                    stuck: Stuck::from(e),
                });
                return Err(IndFailure { attempts });
            }
        },
    };
    for v in cands {
        let der: std::result::Result<Thm, (PremiseId, Stuck)> = match &cfg.scheme {
            IndScheme::Structural => {
                build_ind_premises(env, cache, phi, &v, &cfg.limits).and_then(|p| {
                    derive_ind(env, phi, &v, p.base, p.step)
                        .map_err(|e| (PremiseId::Step, Stuck::from(e)))
                })
            }
            IndScheme::Measured(spec) => {
                build_ind_ord_premises(env, cache, phi, &v, spec, &cfg.limits).and_then(|p| {
                    derive_ind_ord(
                        env, phi, &v, &spec.m, &spec.q, &spec.ts, p.d_op, p.d_decs, p.base, p.step,
                    )
                    .map_err(|e| (PremiseId::Step, Stuck::from(e)))
                })
            }
        };
        match der {
            Ok(der) => match finish(sess, phi, Some(v.clone()), der, &vars) {
                Ok(p) => return Ok(p),
                Err(s) => attempts.push(Attempt {
                    var: Some(v),
                    premise: PremiseId::Transport,
                    stuck: s,
                }),
            },
            Err((pid, s)) => attempts.push(Attempt {
                var: Some(v),
                premise: pid,
                stuck: s,
            }),
        }
    }
    Err(IndFailure { attempts })
}

/// Project + transport a successful derivation (closed φ →
/// [`transport_equal`]; open φ → [`transport_equal_open`] at the
/// object variables' ASCII-lowercased HOL names, collision-checked).
fn finish(
    sess: &Acl2Session,
    phi: &Term,
    var: Option<Vec<u8>>,
    der: Thm,
    vars: &[Vec<u8>],
) -> SResult<IndProof> {
    let env = sess.env();
    let projected = sess.project(phi, der.clone()).map_err(Stuck::from)?;
    let transported = if vars.is_empty() {
        transport_equal(env, &projected).map_err(Stuck::from)?
    } else {
        let mut names: Vec<(Vec<u8>, String)> = Vec::with_capacity(vars.len());
        for v in vars {
            let lower =
                String::from_utf8(v.to_ascii_lowercase()).map_err(|_| Stuck::OutOfFragment {
                    term: phi.clone(),
                    why: format!(
                        "object variable `{}` is not UTF-8",
                        String::from_utf8_lossy(v)
                    ),
                })?;
            if names.iter().any(|(_, n)| *n == lower) {
                return Err(Stuck::OutOfFragment {
                    term: phi.clone(),
                    why: format!("object variables collide at lowercase name `{lower}`"),
                });
            }
            names.push((v.clone(), lower));
        }
        let binds: Vec<(&[u8], &str)> = names
            .iter()
            .map(|(v, n)| (v.as_slice(), n.as_str()))
            .collect();
        transport_equal_open(env, &projected, &binds).map_err(Stuck::from)?
    };
    if !transported.hyps().is_empty() {
        return Err(Stuck::Kernel {
            msg: "transport left hypotheses".into(),
        });
    }
    Ok(IndProof {
        var,
        derivation: der,
        projected,
        transported,
    })
}

// ============================================================================
// §8 — the arithmetic env rows (with real model proofs)
// ============================================================================

/// Extend an env by the two premise-builder arithmetic axiom rows
/// (design §8): `plus-assoc` (unconditional, `ModelEq` from S1's
/// **proved** `plus_assoc`) and `plus-zero-int` (`(IMPLIES (INTEGERP A)
/// (EQUAL (BINARY-+ '0 A) A))`, `ModelImplies` from
/// [`plus_zero_int_thm`]). Both discharge theorems are checked here
/// against their `model_*_target` statements (fail-safe, the
/// `axiom_pack` pattern) and again by the soundness build. `plus-comm`
/// is deliberately **not** registered (an unoriented AC rule loops a
/// naive rewriter — design §8).
pub fn with_arith_rules(env: &Acl2Env) -> Result<Acl2Env> {
    let tm = &*env.tm;
    let pr = tm.pr;
    if env.axiom("plus-assoc").is_ok() || env.axiom("plus-zero-int").is_ok() {
        return Err(bad("with_arith_rules: rows already installed"));
    }
    let va = tm.sym(b"A")?;
    let vb = tm.sym(b"B")?;
    let vc = tm.sym(b"C")?;
    let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64))?)?;
    let plus = |x: &Term, y: &Term| tm.app(b"BINARY-+", &[x.clone(), y.clone()]);
    let checked = |name: &str, enc: Term, discharge: Discharge| -> Result<AxiomRow> {
        let (target, thm) = match &discharge {
            Discharge::ModelEq(t) => (model_eq_target(env, &enc)?, t),
            Discharge::ModelImplies(t) => (model_implies_target(env, &enc)?, t),
            _ => return Err(bad("with_arith_rules: rows are model-discharged")),
        };
        if !thm.hyps().is_empty() || *thm.concl() != target {
            return Err(bad(format!(
                "`{name}` model theorem does not state its target"
            )));
        }
        Ok(AxiomRow {
            name: SmolStr::new(name),
            enc,
            discharge,
        })
    };
    let enc_assoc = tm.mk_equal(&plus(&plus(&va, &vb)?, &vc)?, &plus(&va, &plus(&vb, &vc)?)?)?;
    let enc_zero = tm.mk_implies(
        &tm.app(b"INTEGERP", std::slice::from_ref(&va))?,
        &tm.mk_equal(&plus(&q0, &va)?, &va)?,
    )?;
    let mut env2 = env.clone();
    env2.axioms.push(checked(
        "plus-assoc",
        enc_assoc,
        Discharge::ModelEq(pr.plus_assoc()?),
    )?);
    env2.axioms.push(checked(
        "plus-zero-int",
        enc_zero,
        Discharge::ModelImplies(plus_zero_int_thm()?),
    )?);
    Ok(env2)
}

/// `⊢ ∀A. ¬(aintp A = anil) ⟹ aplus (aint 0) A = A` — the
/// `plus-zero-int` model theorem, **proved** by carrier case analysis:
/// the integer-atom case lands through `plus_unfold` + `intval_int` +
/// the proved `int` ring (`0 + w = w`); every other case refutes the
/// `INTEGERP` hypothesis via the `intp_*` completion laws.
pub fn plus_zero_int_thm() -> Result<Thm> {
    let pr = prims()?;
    let o = ordinals()?;
    let th = pr.th;
    let a = th.ty.clone();
    let anil = th.nil.clone();
    let x = Term::free("A", a.clone());
    let a0 = th.aint_at(&mk_int(0i64))?;
    let hyp = pr
        .intp
        .clone()
        .apply(x.clone())?
        .equals(anil.clone())?
        .not()?;
    let hne = Thm::assume(hyp.clone())?;
    let goal = pr
        .plus
        .clone()
        .apply(a0.clone())?
        .apply(x.clone())?
        .equals(x.clone())?;
    let refute =
        |chain: Thm| -> Result<Thm> { hne.clone().not_elim(chain)?.false_elim(goal.clone()) };
    let bad_shape = || bad("plus_zero_int_thm: bad coprod cases");
    let proved = o.by_cases(
        &x,
        &goal,
        "pz",
        &|b, e| {
            // Payload split: b = inl w (integer) | inr s (symbol).
            let disj = coprod_cases(&Type::int(), &Type::bytes(), b)?;
            let (or_l, dr) = disj.concl().as_app().ok_or_else(bad_shape)?;
            let (_, dl) = or_l.as_app().ok_or_else(bad_shape)?;
            let (dl, dr) = (dl.clone(), dr.clone());
            let br_l = {
                let pred = dl.as_app().ok_or_else(bad_shape)?.1.clone();
                let w = Term::free("__pw", Type::int());
                let hyp0 = Term::app(pred, w.clone());
                let e2 = beta_reduce(Thm::assume(hyp0.clone())?)?; // b = inl w
                let xe = e
                    .clone()
                    .trans(e2.cong_arg(th.atom.clone())?)?
                    .trans(th.int_unfold(&w)?.sym()?)?; // A = aint w
                let aw = th.aint_at(&w)?;
                // aplus (aint 0) (aint w) = aint (0 + w) = aint w.
                let unf = pr
                    .plus_unfold(&a0, &aw)?
                    .rewrite(&pr.intval_int()?.all_elim(mk_int(0i64))?)?
                    .rewrite(&pr.intval_int()?.all_elim(w.clone())?)?;
                let zadd = int::add_comm()
                    .all_elim(mk_int(0i64))?
                    .all_elim(w.clone())?
                    .trans(int::add_zero().all_elim(w.clone())?)?; // 0 + w = w
                let eq_at = unf.rewrite(&zadd)?; // aplus (aint 0) (aint w) = aint w
                let g = goal.rw_all(&xe)?.sym()?.eq_mp(eq_at)?;
                let step = g.imp_intro(&hyp0)?.all_intro("__pw", Type::int())?;
                exists_elim(Thm::assume(dl.clone())?, goal.clone(), step)?.imp_intro(&dl)?
            };
            let br_r = {
                let pred = dr.as_app().ok_or_else(bad_shape)?.1.clone();
                let s = Term::free("__ps", Type::bytes());
                let hyp0 = Term::app(pred, s.clone());
                let e2 = beta_reduce(Thm::assume(hyp0.clone())?)?; // b = inr s
                let xe = e
                    .clone()
                    .trans(e2.cong_arg(th.atom.clone())?)?
                    .trans(th.sym_unfold(&s)?.sym()?)?; // A = asym s
                let chain = xe
                    .cong_arg(pr.intp.clone())?
                    .trans(pr.intp_sym()?.all_elim(s.clone())?)?; // aintp A = anil
                let g = refute(chain)?;
                let step = g.imp_intro(&hyp0)?.all_intro("__ps", Type::bytes())?;
                exists_elim(Thm::assume(dr.clone())?, goal.clone(), step)?.imp_intro(&dr)?
            };
            disj.or_elim(br_l, br_r)
        },
        &|e| refute(e.clone().cong_arg(pr.intp.clone())?.trans(pr.intp_nil()?)?),
        &|h, t, e| {
            refute(
                e.clone()
                    .cong_arg(pr.intp.clone())?
                    .trans(pr.intp_cons()?.all_elim(h.clone())?.all_elim(t.clone())?)?,
            )
        },
    )?;
    proved.imp_intro(&hyp)?.all_intro("A", a)
}

// ============================================================================
// The gates (design §11 — P0 №1–4, P1-kernel №5–6, P2 №10)
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::acl2::defun::DefunSpec;
    use crate::init::acl2::derivable::s6_env;
    use crate::init::acl2::gate_s5d::{count_terms, g4_session, obligations};
    use crate::init::acl2::hilbert::derive_under;
    use crate::init::acl2::hilbert::scripts::{
        B, app_assoc_terms, app_spec, app_unfold_at, s6_app_session,
    };
    use crate::init::acl2::ordinal::with_ordinals;
    use std::sync::LazyLock;

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    /// **P0 gate №1:** the planner/emitter reproduces the committed
    /// `app_unfold_at` moves — same statements, fully automatic — for
    /// both the base-shape (`if-false`) and step-shape (`if-true`)
    /// unfolds.
    #[test]
    fn t_simplify_reproduces_unfold() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        let t = app_assoc_terms(env);
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let app_xy = tm.app(b"APP", &[x.clone(), y.clone()]).unwrap();

        // Base shape: under [g], (EQUAL (APP X Y) Y).
        let goal_b = tm.mk_equal(&app_xy, &y).unwrap();
        let auto_b = prove_under(
            env,
            &cache,
            std::slice::from_ref(&t.g),
            &goal_b,
            &Limits::default(),
        )
        .unwrap();
        check(
            &auto_b,
            &derivable(env, &tm.mk_implies(&t.g, &goal_b).unwrap()).unwrap(),
        );
        // Cross-check: the committed hand script derives the same line.
        let hand_b = {
            let mut b = B::new(env);
            let l_g = b.hyp(0, &t.g);
            let l = app_unfold_at(&mut b, l_g, &y, true);
            assert_eq!(b.phis[l], goal_b);
            derive_under(env, std::slice::from_ref(&t.g), &b.st, &goal_b).unwrap()
        };
        assert_eq!(auto_b.concl(), hand_b.concl());

        // Step shape: under [c], (EQUAL (APP X Y) step_Y).
        let step_y = tm
            .app(
                b"CONS",
                &[
                    tm.app(b"CAR", &[x.clone()]).unwrap(),
                    tm.app(b"APP", &[tm.app(b"CDR", &[x.clone()]).unwrap(), y.clone()])
                        .unwrap(),
                ],
            )
            .unwrap();
        let goal_s = tm.mk_equal(&app_xy, &step_y).unwrap();
        let auto_s = prove_under(
            env,
            &cache,
            std::slice::from_ref(&t.c),
            &goal_s,
            &Limits::default(),
        )
        .unwrap();
        check(
            &auto_s,
            &derivable(env, &tm.mk_implies(&t.c, &goal_s).unwrap()).unwrap(),
        );
        let hand_s = {
            let mut b = B::new(env);
            let l_c = b.hyp(0, &t.c);
            let l = app_unfold_at(&mut b, l_c, &y, false);
            assert_eq!(b.phis[l], goal_s);
            derive_under(env, std::slice::from_ref(&t.c), &b.st, &goal_s).unwrap()
        };
        assert_eq!(auto_s.concl(), hand_s.concl());
    }

    /// **P0 gate №2:** `build_ind_premises` returns exactly the
    /// committed `t_app_assoc_premises` statements — shapes and
    /// `Derivable` conclusions — with zero hand-built steps.
    #[test]
    fn t_auto_app_assoc_premises() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        let t = app_assoc_terms(env);

        let p = build_ind_premises(env, &cache, &t.phi, b"X", &Limits::default()).unwrap();
        assert_eq!(p.g, t.g);
        assert_eq!(p.c, t.c);
        assert_eq!(p.ihcar, t.ihcar);
        assert_eq!(p.ihcdr, t.ihcdr);
        check(
            &p.base,
            &derivable(env, &tm.mk_implies(&t.g, &t.phi).unwrap()).unwrap(),
        );
        let step_phi = tm
            .mk_implies(
                &t.c,
                &tm.mk_implies(&t.ihcar, &tm.mk_implies(&t.ihcdr, &t.phi).unwrap())
                    .unwrap(),
            )
            .unwrap();
        check(&p.step, &derivable(env, &step_phi).unwrap());
    }

    /// **THE P0 GATE (№3):** app-assoc derived **fully automatically**
    /// from goal + auto-ranked induction variable — zero hand-built
    /// steps, zero dependence on the hand scripts — landing the exact
    /// committed S6 gate statement. Plus the №4 negative controls: a
    /// false goal / wrong variable / zero budget / unknown head all
    /// report structured `IndFailure`s naming the failing premise, and
    /// mint nothing.
    #[test]
    fn t_auto_app_assoc_gate() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        let t = app_assoc_terms(env);

        let proof = prove_by_induction(sess, &cache, &t.phi, &IndConfig::default()).unwrap();
        assert_eq!(proof.var.as_deref(), Some(b"X".as_slice()));
        check(&proof.derivation, &derivable(env, &t.phi).unwrap());

        // The exact committed S6 gate statement.
        let (_, u) = env.user("APP").unwrap();
        let a = tm.th.ty.clone();
        let (x, y, z) = (
            Term::free("x", a.clone()),
            Term::free("y", a.clone()),
            Term::free("z", a.clone()),
        );
        let ap = |p: &Term, q: &Term| {
            u.model
                .clone()
                .apply(p.clone())
                .unwrap()
                .apply(q.clone())
                .unwrap()
        };
        let expected = ap(&ap(&x, &y), &z)
            .equals(ap(&x, &ap(&y, &z)))
            .unwrap()
            .forall("z", a.clone())
            .unwrap()
            .forall("y", a.clone())
            .unwrap()
            .forall("x", a.clone())
            .unwrap();
        check(&proof.transported, &expected);

        // №4 (a): a FALSE goal reports Join on the simplifier pass and
        // every candidate; nothing minted.
        let xv = tm.sym(b"X").unwrap();
        let yv = tm.sym(b"Y").unwrap();
        let app_xy = tm.app(b"APP", &[xv.clone(), yv.clone()]).unwrap();
        let false_phi = tm.mk_equal(&app_xy, &xv).unwrap();
        let err = prove_by_induction(sess, &cache, &false_phi, &IndConfig::default()).unwrap_err();
        assert!(err.attempts.len() >= 3, "{err}");
        for a in &err.attempts {
            assert!(matches!(a.stuck, Stuck::Join { .. }), "{a}");
        }

        // №4 (b): forced wrong variable Z fails on a premise.
        let cfg_z = IndConfig {
            var: Some(b"Z".to_vec()),
            ..Default::default()
        };
        let err = prove_by_induction(sess, &cache, &t.phi, &cfg_z).unwrap_err();
        let last = err.attempts.last().unwrap();
        assert_eq!(last.var.as_deref(), Some(b"Z".as_slice()));
        assert!(matches!(last.premise, PremiseId::Base | PremiseId::Step));
        assert!(matches!(last.stuck, Stuck::Join { .. }), "{last}");

        // №4 (c): zero unfold budget reports Budget everywhere.
        let cfg_b = IndConfig {
            limits: Limits {
                unfolds_per_position: 0,
                ..Limits::default()
            },
            ..Default::default()
        };
        let err = prove_by_induction(sess, &cache, &t.phi, &cfg_b).unwrap_err();
        assert!(
            err.attempts
                .iter()
                .all(|a| matches!(a.stuck, Stuck::Budget { .. })),
            "{err}"
        );

        // №4 (d): an unknown head is OutOfFragment.
        let foo = tm.app(b"FOO", &[xv.clone()]).unwrap();
        let bad_phi = tm.mk_equal(&foo, &xv).unwrap();
        let err = prove_by_induction(sess, &cache, &bad_phi, &IndConfig::default()).unwrap_err();
        assert!(
            err.attempts
                .iter()
                .all(|a| matches!(a.stuck, Stuck::OutOfFragment { .. })),
            "{err}"
        );
    }

    // ------------------------------------------------------------------
    // The len2-app slice (design §11.2 — needs the S5 pack + §8 rows)
    // ------------------------------------------------------------------

    /// `(defun len2 (x) (if (consp x) (binary-+ '1 (len2 (cdr x))) '0))`.
    fn len2_spec(tm: &Terms) -> DefunSpec {
        let x = tm.sym(b"X").unwrap();
        let q0 = tm.quote(&tm.th.aint_at(&mk_int(0i64)).unwrap()).unwrap();
        let q1 = tm.quote(&tm.th.aint_at(&mk_int(1i64)).unwrap()).unwrap();
        let step = tm
            .app(
                b"BINARY-+",
                &[
                    q1,
                    tm.app(b"LEN2", &[tm.app(b"CDR", &[x.clone()]).unwrap()])
                        .unwrap(),
                ],
            )
            .unwrap();
        let body = tm
            .mk_if(&tm.app(b"CONSP", &[x.clone()]).unwrap(), &step, &q0)
            .unwrap();
        DefunSpec {
            name: SmolStr::new("LEN2"),
            formals: vec![SmolStr::new("X")],
            body,
            rec_formal: Some(0),
        }
    }

    /// `(EQUAL (LEN2 (APP X Y)) (BINARY-+ (LEN2 X) (LEN2 Y)))`.
    fn len_app_phi(tm: &Terms) -> Term {
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let len = |t: &Term| tm.app(b"LEN2", std::slice::from_ref(t)).unwrap();
        let app_xy = tm.app(b"APP", &[x.clone(), y.clone()]).unwrap();
        tm.mk_equal(
            &len(&app_xy),
            &tm.app(b"BINARY-+", &[len(&x), len(&y)]).unwrap(),
        )
        .unwrap()
    }

    /// The len2 gate session: ordinal env (S5 pack) + the §8 arithmetic
    /// rows + `LEN2` + `APP`; soundness proved once.
    fn len2_session() -> &'static Acl2Session {
        static S: LazyLock<std::result::Result<Acl2Session, String>> = LazyLock::new(|| {
            let e6 = s6_env().map_err(|e| e.to_string())?;
            let eo = with_ordinals(&e6).map_err(|e| e.to_string())?;
            let ea = with_arith_rules(&eo).map_err(|e| e.to_string())?;
            let sess = Acl2Session::new(ea);
            let lspec = len2_spec(&sess.env().tm);
            let sess = sess.admit_defun(&lspec).map_err(|e| e.to_string())?;
            let aspec = app_spec(&sess.env().tm);
            sess.admit_defun(&aspec).map_err(|e| e.to_string())
        });
        S.as_ref().unwrap()
    }

    /// **Gate №5:** the holds-prover closes `D ⌜(INTEGERP (LEN2 Y))⌝`
    /// hypothesis-free via the classical `cases` split on the stuck
    /// `(CONSP Y)` guard (the §12.2 trace) — exact statement.
    #[test]
    fn t_integerp_len_cases() {
        let sess = len2_session();
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        let y = tm.sym(b"Y").unwrap();
        let phi = tm
            .app(b"INTEGERP", &[tm.app(b"LEN2", &[y]).unwrap()])
            .unwrap();
        let thm = prove_under(env, &cache, &[], &phi, &Limits::default()).unwrap();
        check(&thm, &derivable(env, &phi).unwrap());
    }

    /// **Gate №6:** len2-app derived fully automatically — the §8 rows
    /// (`plus-assoc`/`plus-zero-int`) are load-bearing: with them the
    /// goal transports to the exact model statement; without them the
    /// same call fails structurally, minting nothing.
    #[test]
    fn t_auto_len_app_gate() {
        let sess = len2_session();
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        // The rows are installed (eager target checks passed at build).
        assert!(env.axiom("plus-assoc").is_ok());
        assert!(env.axiom("plus-zero-int").is_ok());
        // Double-install is rejected.
        assert!(with_arith_rules(env).is_err());

        let phi = len_app_phi(tm);
        let proof = prove_by_induction(sess, &cache, &phi, &IndConfig::default()).unwrap();
        assert_eq!(proof.var.as_deref(), Some(b"X".as_slice()));
        check(&proof.derivation, &derivable(env, &phi).unwrap());

        // ⊢ ∀x y. len2 (app x y) = aplus (len2 x) (len2 y).
        let (_, ua) = env.user("APP").unwrap();
        let (_, ul) = env.user("LEN2").unwrap();
        let a = tm.th.ty.clone();
        let (x, y) = (Term::free("x", a.clone()), Term::free("y", a.clone()));
        let len = |t: &Term| ul.model.clone().apply(t.clone()).unwrap();
        let app2 = ua
            .model
            .clone()
            .apply(x.clone())
            .unwrap()
            .apply(y.clone())
            .unwrap();
        let expected = len(&app2)
            .equals(
                tm.pr
                    .plus
                    .clone()
                    .apply(len(&x))
                    .unwrap()
                    .apply(len(&y))
                    .unwrap(),
            )
            .unwrap()
            .forall("y", a.clone())
            .unwrap()
            .forall("x", a.clone())
            .unwrap();
        check(&proof.transported, &expected);

        // Negative control: WITHOUT the §8 rows the same goal walls
        // (structured failure, nothing minted) — the rows are
        // load-bearing.
        let no_rows = {
            let e6 = s6_env().unwrap();
            let eo = with_ordinals(&e6).unwrap();
            let sess = Acl2Session::new(eo);
            let lspec = len2_spec(&sess.env().tm);
            let sess = sess.admit_defun(&lspec).unwrap();
            let aspec = app_spec(&sess.env().tm);
            sess.admit_defun(&aspec).unwrap()
        };
        let cache2 = FactCache::default();
        let phi2 = len_app_phi(&no_rows.env().tm);
        let err = prove_by_induction(&no_rows, &cache2, &phi2, &IndConfig::default()).unwrap_err();
        assert!(
            err.attempts
                .iter()
                .all(|a| matches!(a.stuck, Stuck::Join { .. } | Stuck::SideCondition { .. })),
            "{err}"
        );
    }

    /// **Gate №10 (P2, design §11.4):** app-assoc through the measured
    /// scheme (`IndScheme::Measured` at the S5 §11 №16 parameters —
    /// measure `(ACL2-COUNT X)`, guard `(CONSP X)`, descent `(CDR X)`),
    /// base/step premises built by the planner, the `O-P`/`O<`
    /// obligations `Given` from the committed S5d G4 derivations (the
    /// auto route for them is deferred — recorded in the design note).
    /// Lands the exact gate statement on the G4 env.
    #[test]
    fn t_auto_app_assoc_by_measure() {
        let sess = g4_session();
        let env = sess.env();
        let tm = &*env.tm;
        let cache = FactCache::default();
        let ct = count_terms(env);
        let obl = obligations();
        let t = app_assoc_terms(env);
        let cdr_x = tm.app(b"CDR", &[tm.sym(b"X").unwrap()]).unwrap();

        let cfg = IndConfig {
            limits: Limits::default(),
            scheme: IndScheme::Measured(IndOrdSpec {
                m: ct.cx.clone(),
                q: ct.c.clone(),
                ts: vec![cdr_x],
                d_op: ObligationSource::Given(obl.d_opm.thm.clone()),
                d_decs: vec![ObligationSource::Given(obl.d_dec.thm.clone())],
            }),
            var: Some(b"X".to_vec()),
        };
        let proof = prove_by_induction(sess, &cache, &t.phi, &cfg).unwrap();
        assert_eq!(proof.var.as_deref(), Some(b"X".as_slice()));
        check(&proof.derivation, &derivable(env, &t.phi).unwrap());

        // The same closed statement as the committed measured gate.
        let (_, u) = env.user("APP").unwrap();
        let a = tm.th.ty.clone();
        let (x, y, z) = (
            Term::free("x", a.clone()),
            Term::free("y", a.clone()),
            Term::free("z", a.clone()),
        );
        let ap = |p: &Term, q: &Term| {
            u.model
                .clone()
                .apply(p.clone())
                .unwrap()
                .apply(q.clone())
                .unwrap()
        };
        let expected = ap(&ap(&x, &y), &z)
            .equals(ap(&x, &ap(&y, &z)))
            .unwrap()
            .forall("z", a.clone())
            .unwrap()
            .forall("y", a.clone())
            .unwrap()
            .forall("x", a.clone())
            .unwrap();
        check(&proof.transported, &expected);

        // Negative: a Given obligation of the wrong statement is
        // rejected at the statement check (nothing runs).
        let bad_cfg = IndConfig {
            limits: Limits::default(),
            scheme: IndScheme::Measured(IndOrdSpec {
                m: ct.cx.clone(),
                q: ct.c.clone(),
                ts: vec![tm.app(b"CDR", &[tm.sym(b"X").unwrap()]).unwrap()],
                d_op: ObligationSource::Given(obl.d_dec.thm.clone()), // wrong slot
                d_decs: vec![ObligationSource::Given(obl.d_dec.thm.clone())],
            }),
            var: Some(b"X".to_vec()),
        };
        let err = prove_by_induction(sess, &cache, &t.phi, &bad_cfg).unwrap_err();
        let last = err.attempts.last().unwrap();
        assert!(matches!(last.premise, PremiseId::Obligation(0)), "{last}");
    }
}
