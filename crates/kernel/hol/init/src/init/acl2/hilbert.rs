//! **S6 — the deduction compiler** (design
//! `notes/vibes/lisp/acl2-s4-s6-design.md` §11): an untrusted derivation
//! *builder* compiling hypothesis-style object proofs into K/S/MP chains
//! over the S6 env's `prop-k`/`prop-s` axioms, so users of the IND
//! clause can state its base/step premises.
//!
//! Everything here produces genuine `⊢ Derivable_ACL2 ⌜…⌝` theorems via
//! the [`super::derivable`] constructors — every output is
//! kernel-checked; a wrong step list errors, it never fabricates a
//! derivation. The compilation is the standard deduction theorem
//! (per hypothesis, innermost-out: `I = S·K·K` for the discharged
//! hypothesis, `K`-weakening for facts and outer hypotheses, `S`
//! distribution for MP) — quadratic blowup in proof length, fine at
//! gate scale (design risk register).

use std::cell::RefCell;

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;

use crate::init::acl2::derivable::{
    Acl2Env, cong_impl_enc, derivable, derive_axiom, derive_cong_impl, derive_def, derive_inst,
    derive_mp, finite_sigma, subst_ground, sym_lit_of, uncons,
};
use crate::init::ext::ThmExt;

fn bad(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("acl2 hilbert: {}", msg.into()))
}

// ============================================================================
// Hypothesis-free facts + combinators
// ============================================================================

/// A hypothesis-free derived fact: the encoded formula `⌜ψ⌝` together
/// with its derivation `⊢ Derivable_ACL2 ⌜ψ⌝`. Carrying the formula
/// beside the theorem is what lets the compiler *instantiate* the S/K
/// schemas without parsing HOL binders (the pair is re-checked against
/// `derivable(env, ψ)` wherever it enters a step list).
#[derive(Clone)]
pub struct Fact {
    /// The encoded object formula `⌜ψ⌝ : A`.
    pub phi: Term,
    /// `⊢ Derivable_ACL2 ⌜ψ⌝`.
    pub thm: Thm,
}

/// Split `⌜(IMPLIES p q)⌝` (the `IF` macro shape) into `(p, q)`.
pub(crate) fn implies_parts(env: &Acl2Env, imp: &Term) -> Result<(Term, Term)> {
    let tm = &*env.tm;
    let e = || bad(format!("not an (IMPLIES p q) encoding: {imp}"));
    let (h, tail) = uncons(tm, imp).ok_or_else(e)?;
    if sym_lit_of(tm, &h).as_deref() != Some(b"IF") {
        return Err(e());
    }
    let (p, rest) = uncons(tm, &tail).ok_or_else(e)?;
    let (mid, rest) = uncons(tm, &rest).ok_or_else(e)?;
    let (qt, rest) = uncons(tm, &rest).ok_or_else(e)?;
    if rest != tm.th.nil || qt != tm.quote(&tm.pr.t)? {
        return Err(e());
    }
    let (h2, tail2) = uncons(tm, &mid).ok_or_else(e)?;
    if sym_lit_of(tm, &h2).as_deref() != Some(b"IF") {
        return Err(e());
    }
    let (q, rest2) = uncons(tm, &tail2).ok_or_else(e)?;
    let (qt2, rest2) = uncons(tm, &rest2).ok_or_else(e)?;
    let (qnil, rest2) = uncons(tm, &rest2).ok_or_else(e)?;
    if rest2 != tm.th.nil || qt2 != tm.quote(&tm.pr.t)? || qnil != tm.quote(&tm.th.nil)? {
        return Err(e());
    }
    Ok((p, q))
}

/// Split `⌜(EQUAL a b)⌝` into `(a, b)`.
pub(crate) fn equal_parts(env: &Acl2Env, eq: &Term) -> Result<(Term, Term)> {
    let tm = &*env.tm;
    let e = || bad(format!("not an (EQUAL a b) encoding: {eq}"));
    let (h, tail) = uncons(tm, eq).ok_or_else(e)?;
    if sym_lit_of(tm, &h).as_deref() != Some(b"EQUAL") {
        return Err(e());
    }
    let (a, rest) = uncons(tm, &tail).ok_or_else(e)?;
    let (b, rest) = uncons(tm, &rest).ok_or_else(e)?;
    if rest != tm.th.nil {
        return Err(e());
    }
    Ok((a, b))
}

/// An env axiom instantiated at a finite substitution (INST through
/// S2's `subst`, folded by [`subst_ground`]): the schema-instance
/// workhorse of the compiler.
pub fn axiom_inst(env: &Acl2Env, name: &str, binds: &[(&[u8], Term)]) -> Result<Fact> {
    let (_, ax) = env.axiom(name)?;
    let ax = ax.clone();
    let d = derive_axiom(env, name)?;
    if binds.is_empty() {
        return Ok(Fact { phi: ax, thm: d });
    }
    let s = finite_sigma(&env.tm, binds)?;
    let raw = derive_inst(env, &ax, &s, d)?;
    let fold = subst_ground(&env.tm, &ax, &s)?;
    let phi = fold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    Ok(Fact {
        phi,
        thm: raw.rewrite(&fold)?,
    })
}

/// A user row's defining equation, instantiated (`Def(j)` + INST).
pub fn def_inst(env: &Acl2Env, sym: &str, binds: &[(&[u8], Term)]) -> Result<Fact> {
    let (j, u) = env.user(sym)?;
    let enc = u.def_enc.clone();
    let d = derive_def(env, j)?;
    if binds.is_empty() {
        return Ok(Fact { phi: enc, thm: d });
    }
    let s = finite_sigma(&env.tm, binds)?;
    let raw = derive_inst(env, &enc, &s, d)?;
    let fold = subst_ground(&env.tm, &enc, &s)?;
    let phi = fold.concl().as_eq().ok_or(Error::NotAnEquation)?.1.clone();
    Ok(Fact {
        phi,
        thm: raw.rewrite(&fold)?,
    })
}

/// The implication-form congruence fact for the row named `sym`.
pub fn cong_impl(env: &Acl2Env, sym: &str, pairs: &[(Term, Term)]) -> Result<Fact> {
    let k = env.row(sym)?;
    let xs: Vec<Term> = pairs.iter().map(|(x, _)| x.clone()).collect();
    let ys: Vec<Term> = pairs.iter().map(|(_, y)| y.clone()).collect();
    Ok(Fact {
        phi: cong_impl_enc(&env.tm, &env.rows[k], &xs, &ys)?,
        thm: derive_cong_impl(env, k, pairs)?,
    })
}

/// Object-level modus ponens on facts: `imp = ⌜(IMPLIES p q)⌝`,
/// `p_fact = ⌜p⌝` → `⌜q⌝`.
pub fn mp(env: &Acl2Env, imp: &Fact, p_fact: &Fact) -> Result<Fact> {
    let (p, q) = implies_parts(env, &imp.phi)?;
    if p != p_fact.phi {
        return Err(bad(format!(
            "mp: antecedent mismatch ({p} vs {})",
            p_fact.phi
        )));
    }
    Ok(Fact {
        thm: derive_mp(env, &p, &q, imp.thm.clone(), p_fact.thm.clone())?,
        phi: q,
    })
}

/// `⌜(EQUAL x x)⌝` — `equal-refl` instantiated.
pub fn eq_refl(env: &Acl2Env, x: &Term) -> Result<Fact> {
    axiom_inst(env, "equal-refl", &[(b"X", x.clone())])
}

/// From `⌜(EQUAL a b)⌝` conclude `⌜(EQUAL b a)⌝` (`equal-symm` + MP).
pub fn eq_symm(env: &Acl2Env, ab: &Fact) -> Result<Fact> {
    let (a, b) = equal_parts(env, &ab.phi)?;
    let symm = axiom_inst(env, "equal-symm", &[(b"X", a), (b"Y", b)])?;
    mp(env, &symm, ab)
}

/// From `⌜(EQUAL a b)⌝` and `⌜(EQUAL b c)⌝` conclude `⌜(EQUAL a c)⌝`
/// (`equal-trans` + MP twice).
pub fn eq_trans(env: &Acl2Env, ab: &Fact, bc: &Fact) -> Result<Fact> {
    let (a, b) = equal_parts(env, &ab.phi)?;
    let (b2, c) = equal_parts(env, &bc.phi)?;
    if b != b2 {
        return Err(bad("eq_trans: middle terms differ"));
    }
    let tr = axiom_inst(env, "equal-trans", &[(b"X", a), (b"Y", b), (b"Z", c)])?;
    mp(env, &mp(env, &tr, ab)?, bc)
}

/// `⌜(IMPLIES h h)⌝` — the identity combinator `I = S·K·K`.
pub fn imp_identity(env: &Acl2Env, h: &Term) -> Result<Fact> {
    let tm = &*env.tm;
    let hh = tm.mk_implies(h, h)?;
    let s = axiom_inst(
        env,
        "prop-s",
        &[(b"X", h.clone()), (b"Y", hh.clone()), (b"Z", h.clone())],
    )?;
    let k1 = axiom_inst(env, "prop-k", &[(b"X", h.clone()), (b"Y", hh)])?;
    let m1 = mp(env, &s, &k1)?;
    let k2 = axiom_inst(env, "prop-k", &[(b"X", h.clone()), (b"Y", h.clone())])?;
    mp(env, &m1, &k2)
}

// ============================================================================
// The discharge-instance cache (premise-builder design §10.1)
// ============================================================================

/// A cache for the schema instances the deduction-theorem compiler mints
/// over and over across discharge passes (`prop-k`/`prop-s`/the
/// `I = S·K·K` identity). Purely a cost lever: every cached value is a
/// re-checked [`Fact`] built by the committed constructors, and cache
/// hits are keyed by the exact instance terms — a stale entry for a
/// *different* env would fail the `Step::Fact` re-check downstream, so
/// nothing can mis-derive. Per-env-generation by construction (hold it
/// beside the session).
#[derive(Default)]
pub struct KCache {
    k: RefCell<Vec<((Term, Term), Fact)>>,
    s: RefCell<Vec<((Term, Term, Term), Fact)>>,
    i: RefCell<Vec<(Term, Fact)>>,
}

impl KCache {
    fn prop_k(&self, env: &Acl2Env, x: &Term, y: &Term) -> Result<Fact> {
        if let Some((_, f)) = self.k.borrow().iter().find(|((a, b), _)| a == x && b == y) {
            return Ok(f.clone());
        }
        let f = axiom_inst(env, "prop-k", &[(b"X", x.clone()), (b"Y", y.clone())])?;
        self.k
            .borrow_mut()
            .push(((x.clone(), y.clone()), f.clone()));
        Ok(f)
    }

    fn prop_s(&self, env: &Acl2Env, x: &Term, y: &Term, z: &Term) -> Result<Fact> {
        if let Some((_, f)) = self
            .s
            .borrow()
            .iter()
            .find(|((a, b, c), _)| a == x && b == y && c == z)
        {
            return Ok(f.clone());
        }
        let f = axiom_inst(
            env,
            "prop-s",
            &[(b"X", x.clone()), (b"Y", y.clone()), (b"Z", z.clone())],
        )?;
        self.s
            .borrow_mut()
            .push(((x.clone(), y.clone(), z.clone()), f.clone()));
        Ok(f)
    }

    fn imp_id(&self, env: &Acl2Env, h: &Term) -> Result<Fact> {
        if let Some((_, f)) = self.i.borrow().iter().find(|(a, _)| a == h) {
            return Ok(f.clone());
        }
        let f = imp_identity(env, h)?;
        self.i.borrow_mut().push((h.clone(), f.clone()));
        Ok(f)
    }
}

// ============================================================================
// The step language + the deduction-theorem compiler (design §11)
// ============================================================================

/// One line of a hypothesis-style object proof.
pub enum Step {
    /// The `i`-th hypothesis of the [`derive_under`] call.
    Hyp(usize),
    /// A hypothesis-free derived fact `⊢ D ⌜ψ⌝` (K-weakened in by the
    /// compiler). The formula travels with the theorem (deviation from
    /// the design's `Fact(Thm)` — it saves parsing HOL binders) and is
    /// **re-checked** against `derivable(env, ψ)` up front.
    Fact(Term, Thm),
    /// Step `j` (an `(IMPLIES p q)` line) applied to step `k` (`⌜p⌝`).
    Mp(usize, usize),
}

/// A validated line: its object formula + how to (re)build it.
struct Line {
    phi: Term,
    j: LineJ,
}

enum LineJ {
    Fact(Thm),
    Hyp(usize),
    Mp(usize, usize),
}

/// **Compile a hypothesis-style proof** into
/// `⊢ Derivable_ACL2 ⌜(IMPLIES h₁ (… (IMPLIES hₖ goal)))⌝` by the
/// deduction theorem over `prop-k`/`prop-s` (S6 envs). The last step
/// must prove `goal`; hypotheses are discharged innermost-out (`hₖ`
/// first). Every emitted line is a genuine derivation — the kernel
/// re-checks each MP.
pub fn derive_under(env: &Acl2Env, hyps: &[Term], steps: &[Step], goal: &Term) -> Result<Thm> {
    derive_under_cached(env, hyps, steps, goal, &KCache::default())
}

/// [`derive_under`] with a shared [`KCache`] for the discharge-pass
/// schema instances (the premise-builder cost lever, design §10.1).
pub fn derive_under_cached(
    env: &Acl2Env,
    hyps: &[Term],
    steps: &[Step],
    goal: &Term,
    kc: &KCache,
) -> Result<Thm> {
    // Validate + annotate the step list.
    let mut lines: Vec<Line> = Vec::with_capacity(steps.len());
    for (n, s) in steps.iter().enumerate() {
        let line = match s {
            Step::Hyp(i) => {
                let phi = hyps
                    .get(*i)
                    .ok_or_else(|| bad(format!("step {n}: no hypothesis {i}")))?
                    .clone();
                Line {
                    phi,
                    j: LineJ::Hyp(*i),
                }
            }
            Step::Fact(phi, thm) => {
                if !thm.hyps().is_empty() || thm.concl() != &derivable(env, phi)? {
                    return Err(bad(format!(
                        "step {n}: fact theorem does not prove ⊢ Derivable ⌜{phi}⌝"
                    )));
                }
                Line {
                    phi: phi.clone(),
                    j: LineJ::Fact(thm.clone()),
                }
            }
            Step::Mp(j, k) => {
                if *j >= n || *k >= n {
                    return Err(bad(format!("step {n}: forward reference in Mp")));
                }
                let (p, q) = implies_parts(env, &lines[*j].phi)?;
                if p != lines[*k].phi {
                    return Err(bad(format!("step {n}: Mp antecedent mismatch")));
                }
                Line {
                    phi: q,
                    j: LineJ::Mp(*j, *k),
                }
            }
        };
        lines.push(line);
    }
    match lines.last() {
        Some(last) if &last.phi == goal => {}
        _ => return Err(bad("the last step must prove the goal")),
    }

    // Discharge hypotheses innermost-out.
    let mut open: Vec<Term> = hyps.to_vec();
    while !open.is_empty() {
        lines = discharge_last(env, &open, lines, kc)?;
        open.pop();
    }

    // Execute the hypothesis-free line list.
    let mut thms: Vec<Thm> = Vec::with_capacity(lines.len());
    for line in &lines {
        let thm = match &line.j {
            LineJ::Fact(t) => t.clone(),
            LineJ::Hyp(_) => return Err(bad("internal: undischarged hypothesis")),
            LineJ::Mp(j, k) => {
                let (p, q) = implies_parts(env, &lines[*j].phi)?;
                derive_mp(env, &p, &q, thms[*j].clone(), thms[*k].clone())?
            }
        };
        thms.push(thm);
    }
    thms.pop().ok_or_else(|| bad("empty step list"))
}

// ============================================================================
// Script — the step-list builder (the promoted `B`, premise-builder §4)
// ============================================================================

/// A step-list builder tracking line formulas (the object-proof tape):
/// the promotion of the S6 test-local `B` into the public surface the
/// generic premise builder ([`super::simplify`]) emits into. Hypotheses
/// are fixed at construction (they are the premise shape);
/// `hyp`/`mp` re-check shapes eagerly so plan bugs surface at emission
/// with line context, not inside [`derive_under`]. Everything remains
/// untrusted: [`close`](Script::close) runs the whole tape back through
/// the deduction compiler, which re-checks every line.
pub struct Script<'e> {
    env: &'e Acl2Env,
    hyps: Vec<Term>,
    steps: Vec<Step>,
    phis: Vec<Term>,
}

impl<'e> Script<'e> {
    /// A fresh script under the fixed hypothesis list `hyps`.
    pub fn new(env: &'e Acl2Env, hyps: &[Term]) -> Self {
        Script {
            env,
            hyps: hyps.to_vec(),
            steps: Vec::new(),
            phis: Vec::new(),
        }
    }

    /// The environment this script derives in.
    pub fn env(&self) -> &'e Acl2Env {
        self.env
    }

    /// The formula of line `l`.
    pub fn phi(&self, l: usize) -> &Term {
        &self.phis[l]
    }

    /// Push the `i`-th hypothesis as a line.
    pub fn hyp(&mut self, i: usize) -> Result<usize> {
        let phi = self
            .hyps
            .get(i)
            .ok_or_else(|| bad(format!("script: no hypothesis {i}")))?
            .clone();
        self.steps.push(Step::Hyp(i));
        self.phis.push(phi);
        Ok(self.phis.len() - 1)
    }

    /// Push a hypothesis-free fact as a line.
    pub fn fact(&mut self, f: Fact) -> usize {
        self.steps.push(Step::Fact(f.phi.clone(), f.thm));
        self.phis.push(f.phi);
        self.phis.len() - 1
    }

    /// Object-level MP: line `j` (`(IMPLIES p q)`) applied to line `k`
    /// (`p`) — shape-checked eagerly.
    pub fn mp(&mut self, j: usize, k: usize) -> Result<usize> {
        let (p, q) = implies_parts(self.env, &self.phis[j])?;
        if p != self.phis[k] {
            return Err(bad(format!(
                "script mp: line {k} is not the antecedent of line {j}"
            )));
        }
        self.steps.push(Step::Mp(j, k));
        self.phis.push(q);
        Ok(self.phis.len() - 1)
    }

    /// `(EQUAL a b)` at line `jab`, `(EQUAL b c)` at `jbc` →
    /// `(EQUAL a c)` (`equal-trans` + two MPs).
    pub fn trans(&mut self, jab: usize, jbc: usize) -> Result<usize> {
        let (a, b) = equal_parts(self.env, &self.phis[jab])?;
        let (b2, c) = equal_parts(self.env, &self.phis[jbc])?;
        if b != b2 {
            return Err(bad("script trans: middle terms differ"));
        }
        let tr = axiom_inst(self.env, "equal-trans", &[(b"X", a), (b"Y", b), (b"Z", c)])?;
        let lt = self.fact(tr);
        let m1 = self.mp(lt, jab)?;
        self.mp(m1, jbc)
    }

    /// `(EQUAL a b)` at `jab` → `(EQUAL b a)` (`equal-symm` + MP).
    pub fn symm(&mut self, jab: usize) -> Result<usize> {
        let (a, b) = equal_parts(self.env, &self.phis[jab])?;
        let sy = axiom_inst(self.env, "equal-symm", &[(b"X", a), (b"Y", b)])?;
        let ls = self.fact(sy);
        self.mp(ls, jab)
    }

    /// Compile: `⊢ D ⌜(IMPLIES h₁ (… (IMPLIES hₖ goal)))⌝` — the last
    /// line must prove `goal` (checked here and re-checked by the
    /// compiler).
    pub fn close(self, goal: &Term, kc: &KCache) -> Result<Thm> {
        match self.phis.last() {
            Some(last) if last == goal => {}
            _ => return Err(bad("script close: the last line must prove the goal")),
        }
        derive_under_cached(self.env, &self.hyps, &self.steps, goal, kc)
    }
}

/// **Test-only shared object-proof scaffolding**: the step-list builder
/// `B` and the app-assoc scripts of the S6 gate, reused by the S5d G4
/// gate ([`super::gate_s5d`]) — which re-derives app-assoc through the
/// IND-ORD clause with the same base script and the car-IH-free step
/// script (`app_assoc_step(env, t, false)`).
#[cfg(test)]
pub(crate) mod scripts {
    use super::*;
    use crate::init::acl2::defun::{Acl2Session, DefunSpec};
    use crate::init::acl2::derivable::{Acl2Env, finite_sigma, s6_env, subst_ground};
    use crate::init::acl2::term::Terms;
    use smol_str::SmolStr;
    use std::sync::LazyLock;

    /// The S6+APP session (the S6 gate env), shared across the hilbert
    /// and simplify test suites — its 50-clause soundness (incl. the IND
    /// discharge) is proved once per test process.
    pub(crate) fn s6_app_session() -> &'static Acl2Session {
        static S6: LazyLock<std::result::Result<Acl2Session, String>> = LazyLock::new(|| {
            let e6 = s6_env().map_err(|e| e.to_string())?;
            let spec = app_spec(&e6.tm);
            Acl2Session::new(e6)
                .admit_defun(&spec)
                .map_err(|e| e.to_string())
        });
        S6.as_ref().unwrap()
    }

    /// `(defun app (x y) (if (consp x) (cons (car x) (app (cdr x) y)) y))`.
    pub(crate) fn app_spec(tm: &Terms) -> DefunSpec {
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let step = tm
            .app(
                b"CONS",
                &[
                    tm.app(b"CAR", &[x.clone()]).unwrap(),
                    tm.app(b"APP", &[tm.app(b"CDR", &[x.clone()]).unwrap(), y.clone()])
                        .unwrap(),
                ],
            )
            .unwrap();
        let body = tm
            .mk_if(&tm.app(b"CONSP", &[x.clone()]).unwrap(), &step, &y)
            .unwrap();
        DefunSpec {
            name: SmolStr::new("APP"),
            formals: vec![SmolStr::new("X"), SmolStr::new("Y")],
            body,
            rec_formal: Some(0),
        }
    }

    /// A step-list builder tracking line formulas (so the trans/symm
    /// axiom instances can be computed as it goes).
    pub(crate) struct B<'e> {
        pub(crate) env: &'e Acl2Env,
        pub(crate) st: Vec<Step>,
        pub(crate) phis: Vec<Term>,
    }

    impl<'e> B<'e> {
        pub(crate) fn new(env: &'e Acl2Env) -> Self {
            B {
                env,
                st: vec![],
                phis: vec![],
            }
        }
        pub(crate) fn hyp(&mut self, i: usize, phi: &Term) -> usize {
            self.st.push(Step::Hyp(i));
            self.phis.push(phi.clone());
            self.phis.len() - 1
        }
        pub(crate) fn fact(&mut self, f: Fact) -> usize {
            self.st.push(Step::Fact(f.phi.clone(), f.thm));
            self.phis.push(f.phi);
            self.phis.len() - 1
        }
        pub(crate) fn mp(&mut self, j: usize, k: usize) -> usize {
            let (_, q) = implies_parts(self.env, &self.phis[j]).unwrap();
            self.st.push(Step::Mp(j, k));
            self.phis.push(q);
            self.phis.len() - 1
        }
        /// `(EQUAL a b)` at line `jab`, `(EQUAL b c)` at `jbc` →
        /// `(EQUAL a c)` (equal-trans + two MPs).
        pub(crate) fn trans_u(&mut self, jab: usize, jbc: usize) -> usize {
            let (a, b) = equal_parts(self.env, &self.phis[jab]).unwrap();
            let (_, c) = equal_parts(self.env, &self.phis[jbc]).unwrap();
            let tr =
                axiom_inst(self.env, "equal-trans", &[(b"X", a), (b"Y", b), (b"Z", c)]).unwrap();
            let lt = self.fact(tr);
            let m1 = self.mp(lt, jab);
            self.mp(m1, jbc)
        }
        /// `(EQUAL a b)` at `jab` → `(EQUAL b a)` (equal-symm + MP).
        pub(crate) fn symm_u(&mut self, jab: usize) -> usize {
            let (a, b) = equal_parts(self.env, &self.phis[jab]).unwrap();
            let sy = axiom_inst(self.env, "equal-symm", &[(b"X", a), (b"Y", b)]).unwrap();
            let ls = self.fact(sy);
            self.mp(ls, jab)
        }
    }

    /// The shared app-assoc terms over a gate env (any env with `APP`).
    pub(crate) struct AppAssoc {
        /// `(EQUAL (APP (APP X Y) Z) (APP X (APP Y Z)))`.
        pub(crate) phi: Term,
        /// `(EQUAL (CONSP X) 'NIL)`.
        pub(crate) g: Term,
        /// `(CONSP X)`.
        pub(crate) c: Term,
        /// `φ[X ↦ (CAR X)]`.
        pub(crate) ihcar: Term,
        /// `φ[X ↦ (CDR X)]`.
        pub(crate) ihcdr: Term,
    }

    pub(crate) fn app_assoc_terms(env: &Acl2Env) -> AppAssoc {
        let tm = &*env.tm;
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let z = tm.sym(b"Z").unwrap();
        let app2 = |a: &Term, b: &Term| tm.app(b"APP", &[a.clone(), b.clone()]).unwrap();
        let phi = tm
            .mk_equal(&app2(&app2(&x, &y), &z), &app2(&x, &app2(&y, &z)))
            .unwrap();
        let consp_x = tm.app(b"CONSP", &[x.clone()]).unwrap();
        let g = tm
            .mk_equal(&consp_x, &tm.quote(&tm.th.nil).unwrap())
            .unwrap();
        // The IH formulas exactly as `derive_ind` folds them.
        let ih_at = |proj: &[u8]| {
            let e = tm.app(proj, &[x.clone()]).unwrap();
            let s = finite_sigma(tm, &[(b"X", e)]).unwrap();
            subst_ground(tm, &phi, &s)
                .unwrap()
                .concl()
                .as_eq()
                .unwrap()
                .1
                .clone()
        };
        let ihcar = ih_at(b"CAR");
        let ihcdr = ih_at(b"CDR");
        AppAssoc {
            phi,
            g,
            c: consp_x,
            ihcar,
            ihcdr,
        }
    }

    /// `e1_w := (EQUAL (APP X w) (IF (CONSP X) step_w w))`'s Def
    /// instance and companions, shared by both premises: pushes the
    /// `(EQUAL (APP X w) <rhs>)` line where `<rhs>` is `w` under `g`
    /// (base, via if-false) or `step_w` under `c` (step, via if-true).
    pub(crate) fn app_unfold_at(b: &mut B, l_hyp: usize, w: &Term, base: bool) -> usize {
        let env = b.env;
        let tm = &*env.tm;
        let x = tm.sym(b"X").unwrap();
        let consp_x = tm.app(b"CONSP", &[x.clone()]).unwrap();
        let step_w = tm
            .app(
                b"CONS",
                &[
                    tm.app(b"CAR", &[x.clone()]).unwrap(),
                    tm.app(b"APP", &[tm.app(b"CDR", &[x.clone()]).unwrap(), w.clone()])
                        .unwrap(),
                ],
            )
            .unwrap();
        let def_w = def_inst(env, "APP", &[(b"Y", w.clone())]).unwrap();
        let l_def = b.fact(def_w);
        let fire = if base {
            // if-false: (IMPLIES (EQUAL (CONSP X) 'NIL) (EQUAL (IF …) w)).
            axiom_inst(
                env,
                "if-false",
                &[
                    (b"X", consp_x.clone()),
                    (b"Y", step_w.clone()),
                    (b"Z", w.clone()),
                ],
            )
            .unwrap()
        } else {
            // if-true: (IMPLIES (CONSP X) (EQUAL (IF …) step_w)).
            axiom_inst(
                env,
                "if-true",
                &[
                    (b"X", consp_x.clone()),
                    (b"Y", step_w.clone()),
                    (b"Z", w.clone()),
                ],
            )
            .unwrap()
        };
        let l_fire = b.fact(fire);
        let l_if = b.mp(l_fire, l_hyp); // (EQUAL (IF (CONSP X) step_w w) <rhs>)
        b.trans_u(l_def, l_if) // (EQUAL (APP X w) <rhs>)
    }

    /// Hyp-free composite: `⌜(EQUAL (APP (CONS a d) z) (CONS a (APP d z)))⌝`
    /// (Def + consp-cons + if-true + car-cons/cdr-cons + CongImpl).
    pub(crate) fn app_cons_lemma(env: &Acl2Env, a: &Term, d: &Term, z: &Term) -> Fact {
        let tm = &*env.tm;
        let cons_ad = tm.app(b"CONS", &[a.clone(), d.clone()]).unwrap();
        let car_ad = tm.app(b"CAR", &[cons_ad.clone()]).unwrap();
        let cdr_ad = tm.app(b"CDR", &[cons_ad.clone()]).unwrap();
        let app_cdr_z = tm.app(b"APP", &[cdr_ad.clone(), z.clone()]).unwrap();
        let inner0 = tm
            .app(b"CONS", &[car_ad.clone(), app_cdr_z.clone()])
            .unwrap();
        let consp_ad = tm.app(b"CONSP", &[cons_ad.clone()]).unwrap();

        let def = def_inst(env, "APP", &[(b"X", cons_ad.clone()), (b"Y", z.clone())]).unwrap();
        let cc = axiom_inst(env, "consp-cons", &[(b"X", a.clone()), (b"Y", d.clone())]).unwrap();
        let it = axiom_inst(
            env,
            "if-true",
            &[
                (b"X", consp_ad.clone()),
                (b"Y", inner0.clone()),
                (b"Z", z.clone()),
            ],
        )
        .unwrap();
        let it2 = mp(env, &it, &cc).unwrap(); // (EQUAL (IF (CONSP (CONS a d)) inner0 z) inner0)
        let t1 = eq_trans(env, &def, &it2).unwrap(); // (EQUAL (APP (CONS a d) z) inner0)
        let carc = axiom_inst(env, "car-cons", &[(b"X", a.clone()), (b"Y", d.clone())]).unwrap();
        let cdrc = axiom_inst(env, "cdr-cons", &[(b"X", a.clone()), (b"Y", d.clone())]).unwrap();
        let app_d_z = tm.app(b"APP", &[d.clone(), z.clone()]).unwrap();
        let ci1 = mp(
            env,
            &mp(
                env,
                &cong_impl(env, "APP", &[(cdr_ad, d.clone()), (z.clone(), z.clone())]).unwrap(),
                &cdrc,
            )
            .unwrap(),
            &eq_refl(env, z).unwrap(),
        )
        .unwrap(); // (EQUAL (APP (CDR (CONS a d)) z) (APP d z))
        let ci2 = mp(
            env,
            &mp(
                env,
                &cong_impl(env, "CONS", &[(car_ad, a.clone()), (app_cdr_z, app_d_z)]).unwrap(),
                &carc,
            )
            .unwrap(),
            &ci1,
        )
        .unwrap(); // (EQUAL inner0 (CONS a (APP d z)))
        eq_trans(env, &t1, &ci2).unwrap()
    }

    /// The base premise: `⊢ D ⌜(IMPLIES (EQUAL (CONSP X) 'NIL) φ)⌝`.
    pub(crate) fn app_assoc_base(env: &Acl2Env, t: &AppAssoc) -> Thm {
        let tm = &*env.tm;
        let y = tm.sym(b"Y").unwrap();
        let z = tm.sym(b"Z").unwrap();
        let yz = tm.app(b"APP", &[y.clone(), z.clone()]).unwrap();
        let app_xy = tm.app(b"APP", &[tm.sym(b"X").unwrap(), y.clone()]).unwrap();

        let mut b = B::new(env);
        let l_g = b.hyp(0, &t.g);
        let l_e1 = app_unfold_at(&mut b, l_g, &y, true); // (EQUAL (APP X Y) Y)
        let l_e2 = app_unfold_at(&mut b, l_g, &yz, true); // (EQUAL (APP X (APP Y Z)) (APP Y Z))
        // (EQUAL (APP (APP X Y) Z) (APP Y Z)) via CongImpl(APP).
        let ci = cong_impl(env, "APP", &[(app_xy, y.clone()), (z.clone(), z.clone())]).unwrap();
        let l_ci = b.fact(ci);
        let l_m = b.mp(l_ci, l_e1);
        let l_rz = b.fact(eq_refl(env, &z).unwrap());
        let l_c1 = b.mp(l_m, l_rz);
        // symm + trans close φ.
        let l_s = b.symm_u(l_e2); // (EQUAL (APP Y Z) (APP X (APP Y Z)))
        let l_phi = b.trans_u(l_c1, l_s);
        assert_eq!(b.phis[l_phi], t.phi);
        derive_under(env, std::slice::from_ref(&t.g), &b.st, &t.phi).unwrap()
    }

    /// The step premise. With `car_ih` (the S6 IND shape):
    /// `⊢ D ⌜(IMPLIES (CONSP X) (IMPLIES ihcar (IMPLIES ihcdr φ)))⌝`
    /// (the car IH is unused — list induction as the degenerate use of
    /// the tree-induction clause). Without (the S5d IND-ORD shape at
    /// `t₁ = (CDR X)`): `⊢ D ⌜(IMPLIES (CONSP X) (IMPLIES ihcdr φ))⌝` —
    /// the same script with the unused hypothesis dropped.
    pub(crate) fn app_assoc_step(env: &Acl2Env, t: &AppAssoc, car_ih: bool) -> Thm {
        let tm = &*env.tm;
        let x = tm.sym(b"X").unwrap();
        let y = tm.sym(b"Y").unwrap();
        let z = tm.sym(b"Z").unwrap();
        let yz = tm.app(b"APP", &[y.clone(), z.clone()]).unwrap();
        let car_x = tm.app(b"CAR", &[x.clone()]).unwrap();
        let cdr_x = tm.app(b"CDR", &[x.clone()]).unwrap();
        let app_cdr_y = tm.app(b"APP", &[cdr_x.clone(), y.clone()]).unwrap();
        let step_y = tm
            .app(b"CONS", &[car_x.clone(), app_cdr_y.clone()])
            .unwrap();
        let app_xy = tm.app(b"APP", &[x.clone(), y.clone()]).unwrap();

        let hyps: Vec<Term> = if car_ih {
            vec![t.c.clone(), t.ihcar.clone(), t.ihcdr.clone()]
        } else {
            vec![t.c.clone(), t.ihcdr.clone()]
        };
        let mut b = B::new(env);
        let l_c = b.hyp(0, &t.c);
        let l_e1y = app_unfold_at(&mut b, l_c, &y, false); // (EQUAL (APP X Y) step_Y)
        let l_e1yz = app_unfold_at(&mut b, l_c, &yz, false); // (EQUAL (APP X (APP Y Z)) step_YZ)
        // LHS chain: (APP (APP X Y) Z) = (APP step_Y Z).
        let ci = cong_impl(
            env,
            "APP",
            &[(app_xy, step_y.clone()), (z.clone(), z.clone())],
        )
        .unwrap();
        let l_ci = b.fact(ci);
        let l_m = b.mp(l_ci, l_e1y);
        let l_rz = b.fact(eq_refl(env, &z).unwrap());
        let l_lhs1 = b.mp(l_m, l_rz);
        // = (CONS (CAR X) (APP (APP (CDR X) Y) Z)) via the hyp-free lemma.
        let l_lem = b.fact(app_cons_lemma(env, &car_x, &app_cdr_y, &z));
        let l_lhs2 = b.trans_u(l_lhs1, l_lem);
        // The cdr IH rewrites the tail through CongImpl(CONS).
        let l_ih = b.hyp(if car_ih { 2 } else { 1 }, &t.ihcdr);
        let (ih_l, ih_r) = equal_parts(env, &t.ihcdr).unwrap();
        let cic = cong_impl(env, "CONS", &[(car_x.clone(), car_x.clone()), (ih_l, ih_r)]).unwrap();
        let l_cic = b.fact(cic);
        let l_rcar = b.fact(eq_refl(env, &car_x).unwrap());
        let l_mc = b.mp(l_cic, l_rcar);
        let l_tail = b.mp(l_mc, l_ih);
        let l_lhs3 = b.trans_u(l_lhs2, l_tail);
        // RHS: symm the step unfold at (APP Y Z), trans closes φ.
        let l_s = b.symm_u(l_e1yz);
        let l_phi = b.trans_u(l_lhs3, l_s);
        assert_eq!(b.phis[l_phi], t.phi);
        derive_under(env, &hyps, &b.st, &t.phi).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::scripts::*;
    use super::*;
    use crate::init::acl2::derivable::{derive_ind, transport_equal_open};
    use crate::init::ext::TermExt;
    use covalence_hol_eval::derived::DerivedRules;
    use covalence_hol_eval::mk_int;

    /// Assert a closed theorem with an exact conclusion.
    fn check(thm: &Thm, expected: &Term) {
        assert!(thm.hyps().is_empty(), "must be closed: {thm}");
        assert_eq!(thm.concl(), expected);
    }

    /// **S6 gate (soundness):** the metatheorem for the s6+APP env —
    /// 50 clauses including IND (the §9 carrier-induction discharge
    /// routed through `subst_sema`) and the CongImpl family — is closed
    /// with the exact designed ∀A statement.
    #[test]
    fn t_ind_soundness_s6() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        assert_eq!(env.n_clauses(), 50);
        let s = sess.soundness().unwrap();

        let a = tm.th.ty.clone();
        let av = Term::free("A", a.clone());
        let sg = Term::free("sg", tm.val_ty.clone());
        let body = tm
            .eval
            .clone()
            .apply(av.clone())
            .unwrap()
            .apply(sg)
            .unwrap()
            .equals(tm.th.nil.clone())
            .unwrap()
            .not()
            .unwrap()
            .forall("sg", tm.val_ty.clone())
            .unwrap();
        let expected = derivable(env, &av)
            .unwrap()
            .imp(body)
            .unwrap()
            .forall("A", a)
            .unwrap();
        check(&s, &expected);
    }

    /// **S6 gate (deduction compiler):** `⊢ D ⌜(IMPLIES p p)⌝` from a
    /// bare `Hyp`, an unused-hypothesis weakening, and a 2-hypothesis
    /// MP chain — exact statements.
    #[test]
    fn t_deduction_compiler() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let q1 = tm.quote(&tm.th.aint_at(&mk_int(1)).unwrap()).unwrap();
        let q2 = tm.quote(&tm.th.aint_at(&mk_int(2)).unwrap()).unwrap();
        let p = tm.mk_equal(&q1, &q1).unwrap();
        let r = tm.mk_equal(&q2, &q2).unwrap();

        // ⊢ D ⌜(IMPLIES p p)⌝.
        let d = derive_under(env, &[p.clone()], &[Step::Hyp(0)], &p).unwrap();
        check(
            &d,
            &derivable(env, &tm.mk_implies(&p, &p).unwrap()).unwrap(),
        );

        // Unused hypothesis: a fact weakened under r.
        let refl = eq_refl(env, &q1).unwrap();
        let d = derive_under(
            env,
            &[r.clone()],
            &[Step::Fact(refl.phi.clone(), refl.thm)],
            &p,
        )
        .unwrap();
        check(
            &d,
            &derivable(env, &tm.mk_implies(&r, &p).unwrap()).unwrap(),
        );

        // A 2-hypothesis MP chain: from hyps [(IMPLIES p r), p] derive r.
        let imp_pr = tm.mk_implies(&p, &r).unwrap();
        let d = derive_under(
            env,
            &[imp_pr.clone(), p.clone()],
            &[Step::Hyp(0), Step::Hyp(1), Step::Mp(0, 1)],
            &r,
        )
        .unwrap();
        check(
            &d,
            &derivable(
                env,
                &tm.mk_implies(&imp_pr, &tm.mk_implies(&p, &r).unwrap())
                    .unwrap(),
            )
            .unwrap(),
        );

        // Negative controls: bad goal / forward Mp reference / wrong fact.
        assert!(derive_under(env, &[p.clone()], &[Step::Hyp(0)], &r).is_err());
        assert!(derive_under(env, &[], &[Step::Mp(0, 0)], &p).is_err());
        let refl2 = eq_refl(env, &q1).unwrap();
        assert!(derive_under(env, &[], &[Step::Fact(r.clone(), refl2.thm)], &r).is_err());
    }

    // ------------------------------------------------------------------
    // The app-assoc object proofs (design §11, shared via `scripts`) +
    // THE S6 GATE (§12)
    // ------------------------------------------------------------------

    /// **S6 gate (premises):** the base and step premise derivations,
    /// with the exact `Derivable` statements the IND clause consumes.
    #[test]
    fn t_app_assoc_premises() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let t = app_assoc_terms(env);

        let base = app_assoc_base(env, &t);
        check(
            &base,
            &derivable(env, &tm.mk_implies(&t.g, &t.phi).unwrap()).unwrap(),
        );

        let step = app_assoc_step(env, &t, true);
        let step_phi = tm
            .mk_implies(
                &t.c,
                &tm.mk_implies(&t.ihcar, &tm.mk_implies(&t.ihcdr, &t.phi).unwrap())
                    .unwrap(),
            )
            .unwrap();
        check(&step, &derivable(env, &step_phi).unwrap());
    }

    /// **THE S6 GATE (design §12):**
    /// `(defthm app-assoc (equal (app (app x y) z) (app x (app y z))))`
    /// — premises compiled by the deduction compiler, `derive_ind`
    /// through the IND clause, projection through the (cached) 50-clause
    /// soundness, open transport to the **closed base-HOL model
    /// equation `⊢ ∀x y z. app (app x y) z = app x (app y z)`**; every
    /// intermediate asserted exactly. Plus the direct-vs-transported
    /// cross-check control and ill-founded-premise negative controls.
    #[test]
    fn t_app_assoc_gate() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let t = app_assoc_terms(env);

        // 1–2. The premises (assertions in t_app_assoc_premises).
        let base = app_assoc_base(env, &t);
        let step = app_assoc_step(env, &t, true);

        // 3. IND: ⊢ Derivable ⌜φ⌝.
        let der = derive_ind(env, &t.phi, b"X", base.clone(), step.clone()).unwrap();
        check(&der, &derivable(env, &t.phi).unwrap());

        // 4. Projection: ⊢ ∀σ. ¬(eval ⌜φ⌝ σ = anil).
        let projected = sess.project(&t.phi, der).unwrap();
        let sg = Term::free("sg", tm.val_ty.clone());
        let expected_proj = tm
            .eval
            .clone()
            .apply(t.phi.clone())
            .unwrap()
            .apply(sg)
            .unwrap()
            .equals(tm.th.nil.clone())
            .unwrap()
            .not()
            .unwrap()
            .forall("sg", tm.val_ty.clone())
            .unwrap();
        check(&projected, &expected_proj);

        // 5. Open transport: THE closed base-HOL model equation.
        let final_thm =
            transport_equal_open(env, &projected, &[(b"X", "x"), (b"Y", "y"), (b"Z", "z")])
                .unwrap();
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
        check(&final_thm, &expected);

        // 6. Cross-check control: the DIRECT model-side proof (carrier
        // induction over the promoted defun_law equations — the
        // carrier.rs t_induct_instance route, run against THIS env's
        // model constant) agrees with the transported theorem on
        // instantiated, β-reduced conclusions.
        let direct = direct_app_assoc(env);
        let (x0, y0, z0) = (
            Term::free("x0", a.clone()),
            Term::free("y0", a.clone()),
            Term::free("z0", a.clone()),
        );
        let ti = final_thm
            .all_elim(x0.clone())
            .unwrap()
            .all_elim(y0.clone())
            .unwrap()
            .all_elim(z0.clone())
            .unwrap();
        let di = crate::init::eq::beta_reduce(
            direct
                .all_elim(y0.clone())
                .unwrap()
                .all_elim(z0.clone())
                .unwrap()
                .all_elim(x0.clone())
                .unwrap(),
        )
        .unwrap();
        assert!(ti.hyps().is_empty() && di.hyps().is_empty());
        assert_eq!(ti.concl(), di.concl());
        assert_eq!(
            ti.concl(),
            &ap(&ap(&x0, &y0), &z0)
                .equals(ap(&x0, &ap(&y0, &z0)))
                .unwrap()
        );

        // 7. Negative controls: ill-founded premise shapes are rejected.
        // (a) Swapped premises: the kernel's imp_elim refuses.
        assert!(derive_ind(env, &t.phi, b"X", step.clone(), base.clone()).is_err());
        // (b) Induction on the wrong variable: the premises don't match
        //     the clause instance at v = "Y".
        assert!(derive_ind(env, &t.phi, b"Y", base.clone(), step.clone()).is_err());
        // (c) A step premise missing its IHs — derivable, but NOT the
        //     IND step shape.
        let weak = {
            let mut b = B::new(env);
            let l_c = b.hyp(0, &t.c);
            let _ = l_c;
            // (IMPLIES (CONSP X) (EQUAL Z Z)) — a real theorem of the
            // wrong shape.
            let zq = tm.sym(b"Z").unwrap();
            let goal = tm.mk_equal(&zq, &zq).unwrap();
            let lf = b.fact(eq_refl(env, &zq).unwrap());
            let _ = lf;
            derive_under(env, std::slice::from_ref(&t.c), &b.st, &goal).unwrap()
        };
        assert!(derive_ind(env, &t.phi, b"X", base, weak).is_err());
    }

    /// The direct (§12 cross-check) proof: app-associativity by carrier
    /// induction over `defun_law` equations, against the gate env's own
    /// `APP` model constant — the `carrier.rs::t_induct_instance` route.
    fn direct_app_assoc(env: &crate::init::acl2::derivable::Acl2Env) -> Thm {
        use crate::init::acl2::carrier::{acl2, acl2_payload};
        use crate::init::acl2::defun::defun_law;
        use crate::init::eq::{beta_expand, beta_reduce};
        use crate::init::ext::ThmExt;
        use covalence_core::subst;

        let (_, u) = env.user("APP").unwrap();
        let th = acl2().unwrap();
        let tau = th.ty.clone();
        let y = Term::free("y", tau.clone());
        let z = Term::free("z", tau.clone());
        let ap = |a: &Term, b: &Term| {
            u.model
                .clone()
                .apply(a.clone())
                .unwrap()
                .apply(b.clone())
                .unwrap()
        };
        let yz = ap(&y, &z);
        let motive = {
            let x = Term::free("x", tau.clone());
            let goal = ap(&ap(&x, &y), &z).equals(ap(&x, &yz)).unwrap();
            Term::abs(tau.clone(), subst::close(&goal, "x"))
        };
        let law = |v: &Term, w: &Term| defun_law(env, u, &[v.clone(), w.clone()]).unwrap();

        let leaf_case = |leaf_c: Term| -> Thm {
            let inner = law(&leaf_c, &y);
            let lhs_eq = inner
                .cong_arg(u.model.clone())
                .unwrap()
                .cong_fn(z.clone())
                .unwrap();
            let rhs_eq = law(&leaf_c, &yz);
            let raw = lhs_eq.trans(rhs_eq.sym().unwrap()).unwrap();
            beta_expand(&motive, leaf_c, raw).unwrap()
        };
        let b = Term::free("b", acl2_payload());
        let case_atom = leaf_case(th.atom.clone().apply(b).unwrap());
        let case_nil = leaf_case(th.nil.clone());

        let case_cons = {
            let h = Term::free("h", tau.clone());
            let t = Term::free("t", tau.clone());
            let ph = motive.clone().apply(h.clone()).unwrap();
            let pt = motive.clone().apply(t.clone()).unwrap();
            let ih = beta_reduce(Thm::assume(pt.clone()).unwrap()).unwrap();
            let acons_ht = th
                .cons
                .clone()
                .apply(h.clone())
                .unwrap()
                .apply(t.clone())
                .unwrap();
            let s1 = law(&acons_ht, &y);
            let lhs1 = s1
                .cong_arg(u.model.clone())
                .unwrap()
                .cong_fn(z.clone())
                .unwrap();
            let t_y = ap(&t, &y);
            let s2 = law(
                &th.cons
                    .clone()
                    .apply(h.clone())
                    .unwrap()
                    .apply(t_y.clone())
                    .unwrap(),
                &z,
            );
            let lhs = lhs1.trans(s2).unwrap();
            let acons_h = th.cons.clone().apply(h.clone()).unwrap();
            let mid = ih.cong_arg(acons_h).unwrap();
            let s3 = law(&acons_ht, &yz);
            let raw = lhs.trans(mid).unwrap().trans(s3.sym().unwrap()).unwrap();
            beta_expand(&motive, acons_ht, raw)
                .unwrap()
                .imp_intro(&pt)
                .unwrap()
                .imp_intro(&ph)
                .unwrap()
        };

        th.induct(&motive, vec![case_atom, case_nil, case_cons])
            .unwrap()
            .all_intro("z", tau.clone())
            .unwrap()
            .all_intro("y", tau)
            .unwrap()
    }

    /// **S6 gate (open transport, known-answer control):** the
    /// `car-cons` axiom derived → projected → `transport_equal_open` at
    /// `[X, Y]` instantiates to the same conclusion as S1's `car_cons`.
    #[test]
    fn t_transport_open_car_cons() {
        let sess = s6_app_session();
        let env = sess.env();
        let tm = &*env.tm;
        let (_, enc) = env.axiom("car-cons").unwrap();
        let enc = enc.clone();
        let der = derive_axiom(env, "car-cons").unwrap();
        let projected = sess.project(&enc, der).unwrap();
        let open = transport_equal_open(env, &projected, &[(b"X", "x"), (b"Y", "y")]).unwrap();

        // Exact statement: ⊢ ∀x y. car (acons x y) = x.
        let a = tm.th.ty.clone();
        let (x, y) = (Term::free("x", a.clone()), Term::free("y", a.clone()));
        let expected = tm
            .th
            .car
            .clone()
            .apply(
                tm.th
                    .cons
                    .clone()
                    .apply(x.clone())
                    .unwrap()
                    .apply(y.clone())
                    .unwrap(),
            )
            .unwrap()
            .equals(x.clone())
            .unwrap()
            .forall("y", a.clone())
            .unwrap()
            .forall("x", a.clone())
            .unwrap();
        check(&open, &expected);
        // …which is literally S1's car_cons statement (binderless names).
        assert_eq!(open.concl(), tm.pr.car_cons().unwrap().concl());
    }

    /// **S6 gate (coverage):** uncovered object variables and duplicate
    /// bind names error — nothing minted.
    #[test]
    fn t_transport_open_coverage() {
        let sess = s6_app_session();
        let env = sess.env();
        let (_, enc) = env.axiom("car-cons").unwrap();
        let enc = enc.clone();
        let der = derive_axiom(env, "car-cons").unwrap();
        let projected = sess.project(&enc, der).unwrap();
        // Y uncovered.
        assert!(transport_equal_open(env, &projected, &[(b"X", "x")]).is_err());
        // Duplicate bind.
        assert!(
            transport_equal_open(env, &projected, &[(b"X", "x"), (b"X", "x2"), (b"Y", "y")])
                .is_err()
        );
        // Non-EQUAL conclusion (consp-cons is a holds form).
        let (_, hc) = env.axiom("consp-cons").unwrap();
        let hc = hc.clone();
        let dh = derive_axiom(env, "consp-cons").unwrap();
        let ph = sess.project(&hc, dh).unwrap();
        assert!(transport_equal_open(env, &ph, &[(b"X", "x"), (b"Y", "y")]).is_err());
    }
}

/// One deduction-theorem pass: discharge the innermost open hypothesis
/// `h`, transforming each line `⌜ψ⌝` into `⌜(IMPLIES h ψ)⌝` (I / K /
/// S per the classic recipe). Outer hypotheses stay `Hyp` references.
fn discharge_last(
    env: &Acl2Env,
    open: &[Term],
    lines: Vec<Line>,
    kc: &KCache,
) -> Result<Vec<Line>> {
    let tm = &*env.tm;
    let h = open.last().expect("discharge_last: no open hypothesis");
    let hidx = open.len() - 1;
    let old_phis: Vec<Term> = lines.iter().map(|l| l.phi.clone()).collect();
    let mut out: Vec<Line> = Vec::new();
    let mut map: Vec<usize> = Vec::with_capacity(lines.len());
    for line in lines {
        let new_phi = tm.mk_implies(h, &line.phi)?;
        let ni = match line.j {
            LineJ::Hyp(i) if i == hidx => {
                // The discharged hypothesis itself: I = S·K·K.
                let f = kc.imp_id(env, h)?;
                out.push(Line {
                    phi: f.phi,
                    j: LineJ::Fact(f.thm),
                });
                out.len() - 1
            }
            LineJ::Hyp(i) => {
                // An outer hypothesis: K-weaken its Hyp line.
                out.push(Line {
                    phi: open[i].clone(),
                    j: LineJ::Hyp(i),
                });
                let li = out.len() - 1;
                let k = kc.prop_k(env, &open[i], h)?;
                out.push(Line {
                    phi: k.phi,
                    j: LineJ::Fact(k.thm),
                });
                let lk = out.len() - 1;
                out.push(Line {
                    phi: new_phi,
                    j: LineJ::Mp(lk, li),
                });
                out.len() - 1
            }
            LineJ::Fact(t) => {
                out.push(Line {
                    phi: line.phi.clone(),
                    j: LineJ::Fact(t),
                });
                let lf = out.len() - 1;
                let k = kc.prop_k(env, &line.phi, h)?;
                out.push(Line {
                    phi: k.phi,
                    j: LineJ::Fact(k.thm),
                });
                let lk = out.len() - 1;
                out.push(Line {
                    phi: new_phi,
                    j: LineJ::Mp(lk, lf),
                });
                out.len() - 1
            }
            LineJ::Mp(j0, k0) => {
                // From (IMP h (IMP p q)) and (IMP h p), S distributes.
                let p = old_phis[k0].clone();
                let q = line.phi.clone();
                let s = kc.prop_s(env, h, &p, &q)?;
                out.push(Line {
                    phi: s.phi,
                    j: LineJ::Fact(s.thm),
                });
                let ls = out.len() - 1;
                let m1_phi = tm.mk_implies(&tm.mk_implies(h, &p)?, &tm.mk_implies(h, &q)?)?;
                out.push(Line {
                    phi: m1_phi,
                    j: LineJ::Mp(ls, map[j0]),
                });
                let lm1 = out.len() - 1;
                out.push(Line {
                    phi: new_phi,
                    j: LineJ::Mp(lm1, map[k0]),
                });
                out.len() - 1
            }
        };
        map.push(ni);
    }
    Ok(out)
}
