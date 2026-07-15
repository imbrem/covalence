//! **Mid-level — a term-rewrite relation on the binary engine.** The *reduction*
//! analogue of [`super::interp::DerivationSystem`]: where that packages
//! *derivability* on the unary engine, this packages *rewriting* on the binary
//! engine ([`super::binary`]). A [`RewriteRelation`] is a set of encoded rewrite
//! rules over the **`app`-combinator free term algebra**, and it builds:
//!
//! - `Step : Φ → Φ → bool` — one **base** clause per rewrite rule
//!   (`∀x…. d ⌜LHS⌝ ⌜RHS⌝`) plus **two generic congruence clauses** over the
//!   `app` combinator, so a redex *anywhere* in a term can step:
//!   ```text
//!     ∀f x f'. d f f' ⟹ d (app f x) (app f' x)     // step the head spine
//!     ∀f x x'. d x x' ⟹ d (app f x) (app f  x')    // step an argument
//!   ```
//!   Because every node encodes as `app(app(con(sym), a), b)`, these two clauses
//!   are a *finite* congruence for an **open** constructor set.
//! - `Reduces = Step*` — the reflexive-transitive closure (`refl` + `step`).
//!
//! Plus the machinery to actually reduce: a swappable [`Matcher`] (first-order
//! match — find which rule fires where + the substitution) and a fuel-bounded
//! [`RewriteRelation::normalize`] driver that mints `⊢ Reduces cfg nf`. The
//! matcher/driver are the *untrusted* construct-don't-trust layer: they only
//! propose steps; every `Step`/`Reduces` theorem is kernel-rechecked.
//!
//! This is the **reusable** layer the K frontend (`crate::k`) and the SpecTec
//! WASM reduction relation instantiate (`notes/vibes/k/reduction-demo-scope.md`):
//! a high-level, language-shaped API delegates to *this*, which delegates to
//! [`super::binary`], which bottoms out at HOL-omega.

use std::collections::BTreeSet;

use covalence_core::{Error, Result, Term, Type, Var, subst};
use covalence_hol_eval::EvalThm as Thm;

use super::binary::{Premise, RuleSet2, derivable2, derive_mixed};
use crate::init::ext::TermExt;

fn rw_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("metalogic::rewrite: {}", msg.into()))
}

/// One encoded rewrite rule: its metavariable names (the free leaves of `lhs`
/// that also scope `rhs`, in `∀`/instantiation order) and its encoded endpoints.
#[derive(Debug, Clone)]
pub struct Rule {
    pub metavars: Vec<String>,
    pub lhs: Term,
    pub rhs: Term,
}

/// A term-rewrite relation over the `app`-combinator free term algebra with
/// carrier `Φ` — the mid-level rewrite system (see the module docs).
pub struct RewriteRelation {
    phi: Type,
    app: Term,
    rules: Vec<Rule>,
}

/// At an `app(a, b)` node: descend into the head `a` or the argument `b`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dir {
    Head,
    Arg,
}

/// A found redex: which rule fires, the matched substitution (metavar → encoded
/// subterm), and the path of `app`-directions from the whole config to the redex.
#[derive(Debug, Clone)]
pub struct Redex {
    pub rule_idx: usize,
    pub subst: Vec<(String, Term)>,
    pub path: Vec<Dir>,
}

/// A single certified step: `⊢ Step from to` plus its endpoints (encoded).
pub struct StepThm {
    pub from: Term,
    pub to: Term,
    pub thm: Thm,
}

impl RewriteRelation {
    /// Build a rewrite relation from the carrier `phi`, its binary `app`
    /// combinator (`Φ→Φ→Φ`), and the encoded rules.
    pub fn new(phi: Type, app: Term, rules: Vec<Rule>) -> Self {
        RewriteRelation { phi, app, rules }
    }

    /// The number of *base* (rewrite-rule) clauses; the two congruence clauses
    /// occupy indices `n_base()` (head) and `n_base()+1` (arg).
    pub fn n_base(&self) -> usize {
        self.rules.len()
    }

    fn head_cong_idx(&self) -> usize {
        self.rules.len()
    }
    fn arg_cong_idx(&self) -> usize {
        self.rules.len() + 1
    }

    /// The total `Step` clause count (base rules + 2 congruence clauses).
    pub fn step_n_clauses(&self) -> usize {
        self.rules.len() + 2
    }

    fn mkapp(&self, a: Term, b: Term) -> Result<Term> {
        self.app.clone().apply(a)?.apply(b)
    }

    /// Decompose `app(a, b) = App(App(app, a), b)` into `(a, b)` if `t` is a node
    /// of *this* relation's `app` combinator.
    fn as_node<'t>(&self, t: &'t Term) -> Option<(&'t Term, &'t Term)> {
        let (f1, b) = t.as_app()?;
        let (f0, a) = f1.as_app()?;
        (f0 == &self.app).then_some((a, b))
    }

    // -- the two rule sets --------------------------------------------------

    /// `Step`: base clauses (one per rule) then the two congruence clauses.
    pub fn step_rule_set(&self) -> RuleSet2<'_> {
        RuleSet2::new(self.phi.clone(), self.phi.clone(), move |d| {
            let mut clauses = Vec::with_capacity(self.rules.len() + 2);
            // base clauses: ∀mv. d ⌜LHS⌝ ⌜RHS⌝
            for r in &self.rules {
                let mut body = d(&r.lhs, &r.rhs)?;
                for mv in r.metavars.iter().rev() {
                    body = body.forall(mv, self.phi.clone())?;
                }
                clauses.push(body);
            }
            // congruence: head, then arg (order fixes head_cong_idx/arg_cong_idx).
            let f = Term::free("cf", self.phi.clone());
            let x = Term::free("cx", self.phi.clone());
            let f2 = Term::free("cf2", self.phi.clone());
            let x2 = Term::free("cx2", self.phi.clone());
            // ∀f x f'. d f f' ⟹ d (app f x) (app f' x)
            let head = d(&f, &f2)?
                .imp(d(
                    &self.mkapp(f.clone(), x.clone())?,
                    &self.mkapp(f2.clone(), x.clone())?,
                )?)?
                .forall("cf2", self.phi.clone())?
                .forall("cx", self.phi.clone())?
                .forall("cf", self.phi.clone())?;
            // ∀f x x'. d x x' ⟹ d (app f x) (app f x')
            let arg = d(&x, &x2)?
                .imp(d(
                    &self.mkapp(f.clone(), x.clone())?,
                    &self.mkapp(f.clone(), x2.clone())?,
                )?)?
                .forall("cx2", self.phi.clone())?
                .forall("cx", self.phi.clone())?
                .forall("cf", self.phi.clone())?;
            clauses.push(head);
            clauses.push(arg);
            Ok(clauses)
        })
    }

    /// `Reduces = Step*`: `refl` (clause 0) + `step` (clause 1).
    pub fn reduces_rule_set(&self) -> RuleSet2<'_> {
        let step_rs = self.step_rule_set();
        RuleSet2::new(self.phi.clone(), self.phi.clone(), move |d| {
            let tau = self.phi.clone();
            let t = Term::free("t", tau.clone());
            let refl = d(&t, &t)?.forall("t", tau.clone())?;
            let a = Term::free("a", tau.clone());
            let b = Term::free("b", tau.clone());
            let c = Term::free("c", tau.clone());
            let step = derivable2(&step_rs, &a, &b)?
                .imp(d(&b, &c)?.imp(d(&a, &c)?)?)?
                .forall("c", tau.clone())?
                .forall("b", tau.clone())?
                .forall("a", tau.clone())?;
            Ok(vec![refl, step])
        })
    }

    /// `Step from to` / `Reduces from to` propositions.
    pub fn step_prop(&self, from: &Term, to: &Term) -> Result<Term> {
        derivable2(&self.step_rule_set(), from, to)
    }
    pub fn reduces_prop(&self, from: &Term, to: &Term) -> Result<Term> {
        derivable2(&self.reduces_rule_set(), from, to)
    }

    // -- proving steps ------------------------------------------------------

    /// Substitute a metavar assignment into an encoded term (the term-level
    /// analogue of instantiating a rule clause).
    fn instantiate(&self, t: &Term, subst: &[(String, Term)]) -> Term {
        let mut t = t.clone();
        for (name, val) in subst {
            let var = Var::new(name.clone(), self.phi.clone());
            t = subst::subst_free(&t, &var, val);
        }
        t
    }

    /// Fire rule `rule_idx` at the ROOT with the given substitution:
    /// `⊢ Step ⌜LHS[σ]⌝ ⌜RHS[σ]⌝`.
    fn prove_root(&self, rule_idx: usize, subst: &[(String, Term)]) -> Result<StepThm> {
        let rule = self
            .rules
            .get(rule_idx)
            .ok_or_else(|| rw_err("rule index out of range"))?;
        // word_args = metavar witnesses in the rule's ∀ order.
        let mut args = Vec::with_capacity(rule.metavars.len());
        for mv in &rule.metavars {
            let val = subst
                .iter()
                .find(|(n, _)| n == mv)
                .map(|(_, v)| v.clone())
                .ok_or_else(|| rw_err(format!("substitution missing metavar `{mv}`")))?;
            args.push(val);
        }
        let thm = derive_mixed(
            &self.step_rule_set(),
            rule_idx,
            self.step_n_clauses(),
            &args,
            vec![],
        )?;
        Ok(StepThm {
            from: self.instantiate(&rule.lhs, subst),
            to: self.instantiate(&rule.rhs, subst),
            thm,
        })
    }

    /// Lift a step `inner : ⊢ Step a a'` through one congruence frame — the node
    /// `app(·)` whose child (`dir`) is `a`, with the unchanged `sibling`.
    fn lift_one(&self, inner: StepThm, dir: Dir, sibling: &Term) -> Result<StepThm> {
        let (from, to, idx, args) = match dir {
            // head-congruence clause: ∀f x f'. word_args = [f, x, f'] = [a, sib, a'].
            Dir::Head => (
                self.mkapp(inner.from.clone(), sibling.clone())?,
                self.mkapp(inner.to.clone(), sibling.clone())?,
                self.head_cong_idx(),
                vec![inner.from.clone(), sibling.clone(), inner.to.clone()],
            ),
            // arg-congruence clause: ∀f x x'. word_args = [f, x, x'] = [sib, a, a'].
            Dir::Arg => (
                self.mkapp(sibling.clone(), inner.from.clone())?,
                self.mkapp(sibling.clone(), inner.to.clone())?,
                self.arg_cong_idx(),
                vec![sibling.clone(), inner.from.clone(), inner.to.clone()],
            ),
        };
        let thm = derive_mixed(
            &self.step_rule_set(),
            idx,
            self.step_n_clauses(),
            &args,
            vec![Premise::Derivation(inner.thm)],
        )?;
        Ok(StepThm { from, to, thm })
    }

    /// Collect the context frames `(dir, sibling)` from the config root down to
    /// the redex named by `path` (root-first).
    fn frames(&self, config: &Term, path: &[Dir]) -> Result<Vec<(Dir, Term)>> {
        let mut frames = Vec::with_capacity(path.len());
        let mut cur = config.clone();
        for &dir in path {
            let (a, b) = self
                .as_node(&cur)
                .ok_or_else(|| rw_err("redex path does not follow app nodes"))?;
            let (a, b) = (a.clone(), b.clone());
            match dir {
                Dir::Head => {
                    frames.push((Dir::Head, b));
                    cur = a;
                }
                Dir::Arg => {
                    frames.push((Dir::Arg, a));
                    cur = b;
                }
            }
        }
        Ok(frames)
    }

    /// Prove one whole-config step from a [`Redex`]: fire the rule at the redex,
    /// then lift it back to the root through the congruence clauses.
    pub fn prove_step(&self, config: &Term, redex: &Redex) -> Result<StepThm> {
        let frames = self.frames(config, &redex.path)?;
        let mut cur = self.prove_root(redex.rule_idx, &redex.subst)?;
        // lift outward: innermost frame first (reverse of root-first).
        for (dir, sibling) in frames.into_iter().rev() {
            cur = self.lift_one(cur, dir, &sibling)?;
        }
        Ok(cur)
    }

    // -- Reduces (closure) --------------------------------------------------

    /// `⊢ Reduces t t`.
    pub fn reduces_refl(&self, t: &Term) -> Result<Thm> {
        derive_mixed(
            &self.reduces_rule_set(),
            0,
            2,
            std::slice::from_ref(t),
            vec![],
        )
    }

    /// `⊢ Reduces a c` from `⊢ Step a b` and `⊢ Reduces b c`.
    fn reduces_step(&self, a: &Term, b: &Term, c: &Term, step: Thm, rest: Thm) -> Result<Thm> {
        derive_mixed(
            &self.reduces_rule_set(),
            1,
            2,
            &[a.clone(), b.clone(), c.clone()],
            vec![Premise::Side(step), Premise::Derivation(rest)],
        )
    }

    /// Fold a chain of whole-config steps into `⊢ Reduces start end`. `start` is
    /// the reflexive endpoint used when the chain is empty.
    pub fn prove_reduces(&self, steps: Vec<StepThm>, start: &Term) -> Result<Thm> {
        let Some(last) = steps.last() else {
            return self.reduces_refl(start);
        };
        let target = last.to.clone();
        let mut rest = self.reduces_refl(&target)?;
        for s in steps.into_iter().rev() {
            rest = self.reduces_step(&s.from, &s.to, &target, s.thm, rest)?;
        }
        Ok(rest)
    }

    // -- the driver ---------------------------------------------------------

    /// **Normalize** `config` under `matcher`, up to `fuel` steps: repeatedly
    /// find a redex, prove the whole-config step, and chain into a `Reduces`
    /// theorem. Returns `(normal_form, ⊢ Reduces config normal_form)`. Stops at a
    /// normal form (no redex) or when fuel runs out (a partial reduction is still
    /// a valid `Reduces` theorem). A `Reduces` of a closed config is
    /// hypothesis-free.
    pub fn normalize(
        &self,
        matcher: &dyn Matcher,
        config: &Term,
        fuel: usize,
    ) -> Result<(Term, Thm)> {
        let mut cur = config.clone();
        let mut steps: Vec<StepThm> = Vec::new();
        for _ in 0..fuel {
            let Some(redex) = matcher.find(self, &cur) else {
                break;
            };
            let step = self.prove_step(&cur, &redex)?;
            cur = step.to.clone();
            steps.push(step);
        }
        let thm = self.prove_reduces(steps, config)?;
        Ok((cur, thm))
    }

    /// The metavar names of a rule (for matchers).
    pub fn rule_metavars(&self, rule_idx: usize) -> Option<&[String]> {
        self.rules.get(rule_idx).map(|r| r.metavars.as_slice())
    }
    /// A rule's LHS pattern (for matchers).
    pub fn rule_lhs(&self, rule_idx: usize) -> Option<&Term> {
        self.rules.get(rule_idx).map(|r| &r.lhs)
    }
    pub fn n_rules(&self) -> usize {
        self.rules.len()
    }
    pub fn phi(&self) -> &Type {
        &self.phi
    }
}

// ---------------------------------------------------------------------------
// Matching (the untrusted "find the redex" layer)
// ---------------------------------------------------------------------------

/// Find a redex in a config — the swappable strategy for *where* and *which*
/// rule fires. The driver re-checks every step, so a buggy matcher can only fail
/// to reduce, never forge a reduction.
pub trait Matcher {
    fn find(&self, rel: &RewriteRelation, config: &Term) -> Option<Redex>;
}

/// The leftmost-innermost strategy: post-order (children before parent, head
/// before arg), first matching rule wins. Faithful to K function-rule
/// evaluation and correct for confluent, deterministic first-order systems.
#[derive(Debug, Clone, Copy, Default)]
pub struct Innermost;

impl Matcher for Innermost {
    fn find(&self, rel: &RewriteRelation, config: &Term) -> Option<Redex> {
        let mut path = Vec::new();
        find_innermost(rel, config, &mut path)
    }
}

fn find_innermost(rel: &RewriteRelation, subject: &Term, path: &mut Vec<Dir>) -> Option<Redex> {
    // Recurse into children first (innermost), head then arg.
    if let Some((a, b)) = rel.as_node(subject) {
        path.push(Dir::Head);
        if let Some(r) = find_innermost(rel, a, path) {
            return Some(r);
        }
        path.pop();
        path.push(Dir::Arg);
        if let Some(r) = find_innermost(rel, b, path) {
            return Some(r);
        }
        path.pop();
    }
    // Then try to fire a rule at this node.
    for rule_idx in 0..rel.n_rules() {
        let lhs = rel.rule_lhs(rule_idx)?;
        let mvs: BTreeSet<&str> = rel
            .rule_metavars(rule_idx)?
            .iter()
            .map(|s| s.as_str())
            .collect();
        let mut subst = Vec::new();
        if match_term(rel, &mvs, lhs, subject, &mut subst) {
            return Some(Redex {
                rule_idx,
                subst,
                path: path.clone(),
            });
        }
    }
    None
}

/// First-order match of `lhs` (with metavar leaves) against `subject`,
/// accumulating a consistent substitution.
fn match_term(
    rel: &RewriteRelation,
    metavars: &BTreeSet<&str>,
    lhs: &Term,
    subject: &Term,
    subst: &mut Vec<(String, Term)>,
) -> bool {
    // A metavariable leaf binds (consistently).
    if let Some(v) = lhs.as_free()
        && metavars.contains(v.name())
    {
        if let Some((_, bound)) = subst.iter().find(|(n, _)| n == v.name()) {
            return bound == subject;
        }
        subst.push((v.name().to_string(), subject.clone()));
        return true;
    }
    // An app node matches structurally.
    if let (Some((la, lb)), Some((sa, sb))) = (rel.as_node(lhs), rel.as_node(subject)) {
        return match_term(rel, metavars, la, sa, subst)
            && match_term(rel, metavars, lb, sb, subst);
    }
    // Otherwise a constant/leaf must match exactly (and must not itself be an
    // app-node that failed above).
    rel.as_node(lhs).is_none() && rel.as_node(subject).is_none() && lhs == subject
}

#[cfg(test)]
mod tests {
    use super::*;

    fn phi() -> Type {
        Type::nat()
    }
    fn app_fn() -> Term {
        Term::free("t$app", Type::fun(phi(), Type::fun(phi(), phi())))
    }
    fn con(name: &str) -> Term {
        Term::free(format!("t$c${name}"), phi())
    }
    fn mv(name: &str) -> Term {
        Term::free(name, phi())
    }
    fn mkapp(a: Term, b: Term) -> Term {
        app_fn().apply(a).unwrap().apply(b).unwrap()
    }
    /// Encode `sym(args…)` as `app(app(con(sym), a1)…, an)`.
    fn node(sym: &str, args: &[Term]) -> Term {
        let mut acc = con(sym);
        for a in args {
            acc = mkapp(acc, a.clone());
        }
        acc
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "reduction must be hypothesis-free");
    }

    /// PEANO: plus(z,N)=>N ; plus(s(M),N)=>s(plus(M,N)) — exercises recursion,
    /// congruence (redex buried under `s`), and multi-step reduction.
    fn peano() -> RewriteRelation {
        let z = || con("z");
        let s = |t: Term| node("s", &[t]);
        let plus = |a: Term, b: Term| node("plus", &[a, b]);
        let m = || mv("M");
        let n = || mv("N");
        let rules = vec![
            // plus(z, N) => N
            Rule {
                metavars: vec!["N".into()],
                lhs: plus(z(), n()),
                rhs: n(),
            },
            // plus(s(M), N) => s(plus(M, N))
            Rule {
                metavars: vec!["M".into(), "N".into()],
                lhs: plus(s(m()), n()),
                rhs: s(plus(m(), n())),
            },
        ];
        RewriteRelation::new(phi(), app_fn(), rules)
    }

    #[test]
    fn step_rule_set_shape() {
        let rel = peano();
        assert_eq!(rel.n_base(), 2);
        assert_eq!(rel.step_rule_set().n_clauses().unwrap(), 4); // 2 base + 2 congruence
    }

    #[test]
    fn root_step_plus_zero() {
        let rel = peano();
        let n = con("z"); // plus(z, z) => z
        let cfg = node("plus", &[con("z"), n.clone()]);
        let redex = Innermost.find(&rel, &cfg).expect("redex");
        assert_eq!(redex.rule_idx, 0);
        assert!(redex.path.is_empty(), "root redex");
        let s = rel.prove_step(&cfg, &redex).unwrap();
        assert_genuine(&s.thm);
        assert_eq!(s.thm.concl(), &rel.step_prop(&s.from, &s.to).unwrap());
        assert_eq!(s.to, con("z"));
    }

    #[test]
    fn congruence_steps_a_buried_redex() {
        let rel = peano();
        // s(plus(z, z)) — the redex is UNDER `s`, reachable only via congruence.
        let cfg = node("s", &[node("plus", &[con("z"), con("z")])]);
        let redex = Innermost.find(&rel, &cfg).expect("redex");
        assert!(!redex.path.is_empty(), "redex is not at the root");
        let s = rel.prove_step(&cfg, &redex).unwrap();
        assert_genuine(&s.thm);
        assert_eq!(s.to, node("s", &[con("z")])); // s(z)
        assert_eq!(s.thm.concl(), &rel.step_prop(&s.from, &s.to).unwrap());
    }

    #[test]
    fn normalize_plus_two_one() {
        let rel = peano();
        let s = |t: Term| node("s", &[t]);
        // plus(s(s(z)), s(z)) →* s(s(s(z)))
        let start = node("plus", &[s(s(con("z"))), s(con("z"))]);
        let (nf, thm) = rel.normalize(&Innermost, &start, 100).unwrap();
        assert_genuine(&thm);
        let want = s(s(s(con("z"))));
        assert_eq!(nf, want);
        assert_eq!(thm.concl(), &rel.reduces_prop(&start, &want).unwrap());
    }

    #[test]
    fn normal_form_reduces_reflexively() {
        let rel = peano();
        let val = node("s", &[con("z")]);
        let (nf, thm) = rel.normalize(&Innermost, &val, 100).unwrap();
        assert_eq!(nf, val);
        assert_genuine(&thm);
        assert_eq!(thm.concl(), &rel.reduces_prop(&val, &val).unwrap());
    }

    /// A function-rule style demo (K Lesson 1.2 shape): colorOf(Banana())=>Yellow().
    #[test]
    fn function_rule_colorof() {
        let rules = vec![
            Rule {
                metavars: vec![],
                lhs: node("colorOf", &[node("Banana", &[])]),
                rhs: node("Yellow", &[]),
            },
            Rule {
                metavars: vec!["F".into()],
                lhs: node("contentsOfJar", &[node("Jar", &[mv("F")])]),
                rhs: mv("F"),
            },
        ];
        let rel = RewriteRelation::new(phi(), app_fn(), rules);
        // colorOf(Banana()) →* Yellow()
        let start = node("colorOf", &[node("Banana", &[])]);
        let (nf, thm) = rel.normalize(&Innermost, &start, 10).unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, node("Yellow", &[]));
        // contentsOfJar(Jar(Apple())) →* Apple() (variable binding).
        let start2 = node("contentsOfJar", &[node("Jar", &[node("Apple", &[])])]);
        let (nf2, thm2) = rel.normalize(&Innermost, &start2, 10).unwrap();
        assert_genuine(&thm2);
        assert_eq!(nf2, node("Apple", &[]));
    }

    // ==================================================================
    // ADVERSARIAL SOUNDNESS TESTS (audit)
    // ==================================================================

    /// A relation with the non-linear rule `eq(X, X) => tt`.
    fn nonlinear_eq() -> RewriteRelation {
        let eq = |a: Term, b: Term| node("eq", &[a, b]);
        let rules = vec![Rule {
            metavars: vec!["X".into()],
            lhs: eq(mv("X"), mv("X")),
            rhs: con("tt"),
        }];
        RewriteRelation::new(phi(), app_fn(), rules)
    }

    /// Non-linear LHS `eq(X,X)` must NOT match `eq(a,b)` with a≠b: the matcher
    /// enforces metavar consistency, so `eq(a,b)` is a normal form (reflexive
    /// Reduces only), never `⊢ Reduces eq(a,b) tt`.
    #[test]
    fn nonlinear_pattern_does_not_match_distinct_args() {
        let rel = nonlinear_eq();
        let cfg = node("eq", &[con("a"), con("b")]);
        assert!(
            Innermost.find(&rel, &cfg).is_none(),
            "eq(a,b) must not match eq(X,X)"
        );
        let (nf, thm) = rel.normalize(&Innermost, &cfg, 10).unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, cfg, "no reduction: eq(a,b) is a normal form");
        // The theorem is exactly reflexive Reduces, never `Reduces eq(a,b) tt`.
        assert_eq!(thm.concl(), &rel.reduces_prop(&cfg, &cfg).unwrap());
        assert_ne!(
            thm.concl(),
            &rel.reduces_prop(&cfg, &con("tt")).unwrap(),
            "must NOT have forged Reduces eq(a,b) tt"
        );
    }

    /// Non-linear LHS DOES fire on genuinely-equal args: `eq(a,a) => tt`.
    #[test]
    fn nonlinear_pattern_matches_equal_args() {
        let rel = nonlinear_eq();
        let cfg = node("eq", &[con("a"), con("a")]);
        let (nf, thm) = rel.normalize(&Innermost, &cfg, 10).unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, con("tt"));
        assert_eq!(thm.concl(), &rel.reduces_prop(&cfg, &con("tt")).unwrap());
    }

    /// A rule whose RHS introduces a variable `Y` absent from the LHS. The
    /// matcher never binds `Y`, so `prove_root` cannot supply a witness for the
    /// `∀Y` binder — it must ERROR, not forge a step with an arbitrary Y.
    #[test]
    fn rhs_fresh_variable_cannot_be_proved() {
        // f(X) => g(Y)  — Y is fresh on the RHS (a non-left-linear "creative" rule).
        let rules = vec![Rule {
            metavars: vec!["X".into(), "Y".into()],
            lhs: node("f", &[mv("X")]),
            rhs: node("g", &[mv("Y")]),
        }];
        let rel = RewriteRelation::new(phi(), app_fn(), rules);
        let cfg = node("f", &[con("a")]);
        // The matcher binds only X (from the LHS), leaving Y unbound.
        let redex = Innermost.find(&rel, &cfg).expect("f(a) matches f(X)");
        assert!(
            !redex.subst.iter().any(|(n, _)| n == "Y"),
            "matcher must not invent a binding for the fresh RHS var Y"
        );
        // prove_root demands a witness for every metavar (X and Y): Y is missing.
        let err = rel.prove_root(redex.rule_idx, &redex.subst);
        assert!(
            err.is_err(),
            "a fresh RHS variable must make prove_root fail, not forge a step"
        );
        // And the driver surfaces that as an error, never a bogus theorem.
        assert!(rel.normalize(&Innermost, &cfg, 10).is_err());
    }

    /// The kernel re-check is the sole trust anchor: `StepThm.from`/`to` are
    /// UNTRUSTED metadata. We confirm the kernel-computed `thm.concl()` always
    /// equals the independently-built `step_prop(from, to)` — so even if the
    /// driver mislabelled endpoints, a consumer verifying `concl()` is safe.
    #[test]
    fn step_concl_is_independently_reconstructible() {
        let rel = peano();
        let cfg = node("s", &[node("plus", &[con("z"), con("z")])]);
        let redex = Innermost.find(&rel, &cfg).expect("redex");
        let s = rel.prove_step(&cfg, &redex).unwrap();
        // The kernel conclusion matches the claimed endpoints exactly.
        assert_eq!(s.thm.concl(), &rel.step_prop(&s.from, &s.to).unwrap());
        // And crucially: it is NOT a step to some unrelated term.
        assert_ne!(
            s.thm.concl(),
            &rel.step_prop(&cfg, &con("z")).unwrap(),
            "kernel concl must reflect the real rewrite, not an arbitrary claim"
        );
    }

    /// Feeding `lift_one` the WRONG congruence clause index must be rejected by
    /// the kernel (the inner step's shape won't discharge the other clause's
    /// antecedent / instantiate its binders coherently) — a wrong index can only
    /// FAIL to build, never forge. We simulate by calling derive_mixed directly
    /// with a swapped clause index and confirm the resulting concl (if any) is
    /// never a false step.
    #[test]
    fn wrong_clause_index_cannot_forge() {
        let rel = peano();
        // Prove a genuine root step ⊢ Step plus(z,z) z.
        let cfg = node("plus", &[con("z"), con("z")]);
        let redex = Innermost.find(&rel, &cfg).expect("redex");
        let inner = rel.prove_root(redex.rule_idx, &redex.subst).unwrap();
        let sibling = con("z");
        // Correct: head-congruence with word_args [from, sib, to].
        let good = derive_mixed(
            &rel.step_rule_set(),
            rel.head_cong_idx(),
            rel.step_n_clauses(),
            &[inner.from.clone(), sibling.clone(), inner.to.clone()],
            vec![Premise::Derivation(inner.thm.clone())],
        );
        assert!(good.is_ok());
        // Adversarial: same premise, but the ARG-congruence clause with the SAME
        // arg order. If it builds at all, its concl is whatever the kernel
        // actually derives — assert it is never the false head-lifted step.
        let arg_head = rel.mkapp(inner.from.clone(), sibling.clone()).unwrap();
        let arg_tail = rel.mkapp(inner.to.clone(), sibling.clone()).unwrap();
        let false_target = rel.step_prop(&arg_head, &arg_tail).unwrap();
        match derive_mixed(
            &rel.step_rule_set(),
            rel.arg_cong_idx(),
            rel.step_n_clauses(),
            &[inner.from.clone(), sibling.clone(), inner.to.clone()],
            vec![Premise::Derivation(inner.thm.clone())],
        ) {
            Err(_) => {} // fine: refused to build
            Ok(t) => assert_ne!(
                t.concl(),
                &false_target,
                "arg clause must not mint the head-congruence conclusion"
            ),
        }
    }

    /// Overlapping rules: two rules whose LHSs both match. The engine picks one
    /// (first-match) and mints a genuine step for THAT rule; it never mints a
    /// step justified by neither.
    #[test]
    fn overlapping_rules_stay_sound() {
        // r0: f(X) => a ;  r1: f(g(Y)) => b  (both match f(g(z)))
        let rules = vec![
            Rule {
                metavars: vec!["X".into()],
                lhs: node("f", &[mv("X")]),
                rhs: con("a"),
            },
            Rule {
                metavars: vec!["Y".into()],
                lhs: node("f", &[node("g", &[mv("Y")])]),
                rhs: con("b"),
            },
        ];
        let rel = RewriteRelation::new(phi(), app_fn(), rules);
        let cfg = node("f", &[node("g", &[con("z")])]);
        let (nf, thm) = rel.normalize(&Innermost, &cfg, 10).unwrap();
        assert_genuine(&thm);
        // Whichever fired, the concl equals step/reduces to the REAL result.
        assert!(nf == con("a") || nf == con("b"));
        assert_eq!(thm.concl(), &rel.reduces_prop(&cfg, &nf).unwrap());
    }

    /// A metavar bound to a compound (non-leaf) subterm must substitute exactly:
    /// `id(X) => X` on `id(f(a,b))` yields `f(a,b)`, and the kernel concl proves
    /// exactly that — a mis-decomposition in `as_node` would surface as a concl
    /// mismatch, which we assert against the independent prop.
    #[test]
    fn compound_metavar_binding_is_exact() {
        let rules = vec![Rule {
            metavars: vec!["X".into()],
            lhs: node("id", &[mv("X")]),
            rhs: mv("X"),
        }];
        let rel = RewriteRelation::new(phi(), app_fn(), rules);
        let inner = node("f", &[con("a"), con("b")]);
        let cfg = node("id", &[inner.clone()]);
        let (nf, thm) = rel.normalize(&Innermost, &cfg, 10).unwrap();
        assert_genuine(&thm);
        assert_eq!(nf, inner);
        assert_eq!(thm.concl(), &rel.reduces_prop(&cfg, &inner).unwrap());
    }
}
