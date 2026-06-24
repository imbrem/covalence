//! Internalising Dedukti syntax into the covalence-hol kernel.
//!
//! This module is the consumer-side bridge — the analogue, for Dedukti, of
//! `covalence-hol`'s `metalogic::mm_*` modules for Metamath. It lives here only
//! temporarily (the `hol` feature); it will be factored into `covalence-hol`
//! once it matures (see the crate `SKELETONS.md`).
//!
//! ## What it does
//!
//! Two things, mirroring the Metamath integration:
//!
//! 1. **Deep-embeds Dedukti terms** ([`Encoder`]) into HOL kernel terms over the
//!    carrier `Φ = nat`. Every syntactic former becomes an *uninterpreted* free
//!    constant (`dk$app`, `dk$lam`, `dk$pi`, `dk$Type`, `dk$c$<name>` for
//!    declared constants), and every rewrite-rule **pattern variable** becomes a
//!    HOL free variable `dk$v$<name>`. This is the same trick `metalogic::mm_database`
//!    uses: because formers are uninterpreted and pattern variables are genuine
//!    HOL variables, the kernel's capture-avoiding substitution (`Thm::all_elim`)
//!    *is* Dedukti's first-order substitution on the encoded terms, on the nose.
//!
//! 2. **Realises a signature's rewrite relation** ([`SigRuleSet`]) as a
//!    [`metalogic::RuleSet`]. The judgement is `red a b` ("`a` reduces to `b`"),
//!    encoded as `dk$red a b : nat`; the generators are reflexivity, transitivity,
//!    application congruence, and one clause per `lhs --> rhs` rule. From these
//!    one builds genuine kernel theorems `⊢ Derivable_Σ ⌜red a b⌝` via the shared
//!    [`metalogic::derive_via_closed`] spine.
//!
//! ## Scope & honesty
//!
//! The relation defined here is exactly the inductive closure of the listed
//! generators over the *encoded* syntax — a real HOL object, sound by
//! construction (the kernel re-checks every step). It is **not** claimed to equal
//! Dedukti's conversion: binders are encoded structurally with *named* bound
//! variables (no α-equivalence, no β-rule, no higher-order/Miller matching), and
//! congruence is provided for application only. Capturing the full λΠ-modulo
//! conversion (and then *typing* derivations, and then cross-theory transport)
//! is the north star tracked in `SKELETONS.md`. What is here is the working spine:
//! a faithful encoder plus genuine, kernel-checked reduction derivations.

use std::collections::HashSet;

use covalence_core::{Result, Term as HTerm, Thm, Type as HType};
use covalence_hol::init::ext::TermExt;
use covalence_hol::metalogic::{self, RuleSet};

use crate::entry::{RewriteRule, Signature};
use crate::term::{Ref, Symbol, Term};

// ============================================================================
// The carrier and the uninterpreted formers
// ============================================================================

/// The reified-syntax carrier `Φ`. As in `metalogic::mm_database`, `nat` is used
/// purely as an inhabited base type to host uninterpreted constructors; its
/// arithmetic is never invoked.
fn phi() -> HType {
    HType::nat()
}

/// A nullary former `name : Φ`.
fn former0(name: &str) -> HTerm {
    HTerm::free(name, phi())
}

/// A binary former `name : Φ → Φ → Φ`.
fn former2(name: &str) -> HTerm {
    HTerm::free(name, HType::fun(phi(), HType::fun(phi(), phi())))
}

/// `dk$app a b` — application.
fn app_fn() -> HTerm {
    former2("dk$app")
}

/// `dk$lam ann body` — λ-abstraction (`ann` is the encoded domain annotation or
/// the `dk$none` marker when absent).
fn lam_fn() -> HTerm {
    former2("dk$lam")
}

/// `dk$pi dom cod` — (dependent) product.
fn pi_fn() -> HTerm {
    former2("dk$pi")
}

/// `dk$red a b` — the reduction judgement "`a` reduces to `b`", as an element of
/// `Φ` (so `d : Φ → bool` tests it).
fn red_fn() -> HTerm {
    former2("dk$red")
}

/// `dk$red a b`.
fn red(a: HTerm, b: HTerm) -> Result<HTerm> {
    red_fn().apply(a)?.apply(b)
}

/// Encode a declared constant reference's key (`module.name` or `name`) as the
/// uninterpreted nullary former `dk$c$<key>`.
fn const_former(key: &str) -> HTerm {
    former0(&format!("dk$c${key}"))
}

/// Encode a rewrite-rule pattern variable `name` as the HOL free variable
/// `dk$v$<name>` (universally bound in the rule's clause; substitutable by
/// `all_elim`).
fn patvar_former(name: &str) -> HTerm {
    former0(&patvar_name(name))
}

/// The HOL variable name used for pattern variable `name`.
fn patvar_name(name: &str) -> String {
    format!("dk$v${name}")
}

/// Encode an object-level bound variable `name` (introduced by a λ/Π binder) as
/// the uninterpreted nullary former `dk$b$<name>`. Named, not nameless — see the
/// module docs.
fn bound_former(name: &str) -> HTerm {
    former0(&format!("dk$b${name}"))
}

// ============================================================================
// The encoder
// ============================================================================

/// Deep-embeds Dedukti [`Term`]s into HOL kernel terms over `Φ = nat`.
///
/// A reference resolves, in order, to: an object-bound variable if a surrounding
/// λ/Π binder introduced its name; a **pattern variable** (a HOL free variable
/// `dk$v$<name>`) if its (unqualified) name is in this encoder's pattern-variable
/// set; otherwise a declared **constant** `dk$c$<name>`.
#[derive(Debug, Clone, Default)]
pub struct Encoder {
    patvars: HashSet<Symbol>,
}

impl Encoder {
    /// An encoder with no pattern variables — every unbound reference is a
    /// constant (suitable for closed terms).
    pub fn new() -> Self {
        Self::default()
    }

    /// An encoder whose pattern-variable set is `names` (typically a rewrite
    /// rule's context variables).
    pub fn with_patvars(names: impl IntoIterator<Item = Symbol>) -> Self {
        Encoder { patvars: names.into_iter().collect() }
    }

    /// Encode a Dedukti term into its `Φ`-typed HOL representation.
    pub fn encode(&self, t: &Term) -> Result<HTerm> {
        self.enc(t, &mut Vec::new())
    }

    fn enc(&self, t: &Term, bound: &mut Vec<Symbol>) -> Result<HTerm> {
        match t {
            Term::Type => Ok(former0("dk$Type")),
            Term::Ref(r) => Ok(self.enc_ref(r, bound)),
            Term::App(f, a) => {
                let f = self.enc(f, bound)?;
                let a = self.enc(a, bound)?;
                app_fn().apply(f)?.apply(a)
            }
            Term::Abs { binder, ty, body } => {
                let ann = match ty {
                    Some(t) => self.enc(t, bound)?,
                    None => former0("dk$none"),
                };
                let b = self.enc_under(binder, body, bound)?;
                lam_fn().apply(ann)?.apply(b)
            }
            Term::Pi { binder, domain, codomain } => {
                let dom = self.enc(domain, bound)?;
                let cod = self.enc_under(binder, codomain, bound)?;
                pi_fn().apply(dom)?.apply(cod)
            }
            // Dot/guard patterns: encode the inner term (its convertibility-guard
            // semantics are not modelled here — see module docs).
            Term::Bracket(t) => self.enc(t, bound),
        }
    }

    /// Encode `body` with `binder` (if named) pushed onto the bound-variable
    /// stack, then popped.
    fn enc_under(
        &self,
        binder: &Option<Symbol>,
        body: &Term,
        bound: &mut Vec<Symbol>,
    ) -> Result<HTerm> {
        match binder {
            Some(name) => {
                bound.push(name.clone());
                let r = self.enc(body, bound);
                bound.pop();
                r
            }
            None => self.enc(body, bound),
        }
    }

    fn enc_ref(&self, r: &Ref, bound: &[Symbol]) -> HTerm {
        if r.module.is_none() {
            if bound.iter().any(|b| b == &r.name) {
                return bound_former(&r.name);
            }
            if self.patvars.contains(&r.name) {
                return patvar_former(&r.name);
            }
        }
        const_former(&r.to_string())
    }
}

// ============================================================================
// The signature rule set
// ============================================================================

/// The fixed structural generators precede the per-rule clauses.
const REFL: usize = 0;
const TRANS: usize = 1;
const CONG_APP_L: usize = 2;
const CONG_APP_R: usize = 3;
/// Number of structural generator clauses.
const N_STRUCTURAL: usize = 4;

/// A single clause of the rule set, in a uniform shape:
/// `∀binders. (⋀ d premiseᵢ) ⟹ d conclusion`.
#[derive(Clone)]
struct ClauseSpec {
    /// HOL free-variable names bound (outermost first), each of type `Φ`.
    binders: Vec<String>,
    /// Encoded `Φ` premises (each wrapped by `d`); empty for axiom-shaped clauses.
    premises: Vec<HTerm>,
    /// The encoded `Φ` conclusion (wrapped by `d`).
    conclusion: HTerm,
}

impl ClauseSpec {
    fn build(&self, d_apply: &dyn Fn(&HTerm) -> Result<HTerm>) -> Result<HTerm> {
        let concl = d_apply(&self.conclusion)?;
        let mut body = if self.premises.is_empty() {
            concl
        } else {
            let prems: Vec<HTerm> =
                self.premises.iter().map(|p| d_apply(p)).collect::<Result<_>>()?;
            metalogic::conj(prems)?.imp(concl)?
        };
        // Bind binders[0] outermost: fold from the inside out.
        for name in self.binders.iter().rev() {
            body = body.forall(name, phi())?;
        }
        Ok(body)
    }
}

/// A structural metavariable `dk$s$<name> : Φ` (the variables of the refl/trans/
/// congruence generators), kept disjoint from pattern variables (`dk$v$…`) and
/// the impredicative predicate `d`.
fn svar(name: &str) -> HTerm {
    former0(&format!("dk$s${name}"))
}

fn svar_name(name: &str) -> String {
    format!("dk$s${name}")
}

/// A Dedukti signature realised as a [`metalogic::RuleSet`] for its rewrite
/// relation, together with the per-rule clause layout needed to drive the
/// derivation constructors.
pub struct SigRuleSet {
    rs: RuleSet<'static>,
    n: usize,
    /// For each included rewrite rule: its clause index and its pattern-variable
    /// names (in context order).
    rules: Vec<RuleClause>,
}

/// The clause layout for one included rewrite rule.
struct RuleClause {
    clause: usize,
    patvars: Vec<Symbol>,
}

impl SigRuleSet {
    /// Build the rule set for `sig`'s rewrite rules. Every rule is included as a
    /// generator (binders, if any, encoded structurally — see the module docs).
    pub fn build(sig: &Signature) -> Result<SigRuleSet> {
        let mut specs: Vec<ClauseSpec> = Vec::with_capacity(N_STRUCTURAL);
        specs.push(refl_spec()?);
        specs.push(trans_spec()?);
        specs.push(cong_app_l_spec()?);
        specs.push(cong_app_r_spec()?);

        let mut rules = Vec::new();
        for rule in sig.rules() {
            let clause = specs.len();
            let patvars: Vec<Symbol> = rule.context.iter().map(|c| c.name.clone()).collect();
            specs.push(rule_spec(rule)?);
            rules.push(RuleClause { clause, patvars });
        }

        let n = specs.len();
        let rs = RuleSet::new(phi(), move |d_apply| {
            specs.iter().map(|s| s.build(d_apply)).collect()
        });
        Ok(SigRuleSet { rs, n, rules })
    }

    /// The underlying rule set.
    pub fn rule_set(&self) -> &RuleSet<'static> {
        &self.rs
    }

    /// The number of rewrite-rule generators (excluding the structural ones).
    pub fn n_rules(&self) -> usize {
        self.rules.len()
    }

    /// Encode the statement `Derivable_Σ ⌜red a b⌝` for two encoded `Φ` terms.
    pub fn derivable_red(&self, a: HTerm, b: HTerm) -> Result<HTerm> {
        let formula = red(a, b)?;
        metalogic::derivable(&self.rs, &formula)
    }

    // --- derivation constructors (each yields `⊢ Derivable_Σ ⌜red a b⌝`) ---

    /// `⊢ Derivable_Σ ⌜red a a⌝` (reflexivity), for an encoded term `a`.
    pub fn derive_refl(&self, a: HTerm) -> Result<Thm> {
        self.derive(REFL, vec![a], vec![])
    }

    /// Apply rewrite rule `rule_idx` (0-based, in signature order) at the given
    /// substitution `args` (the pattern variables in context order, as Dedukti
    /// terms), yielding `⊢ Derivable_Σ ⌜red lhs[σ] rhs[σ]⌝`.
    pub fn derive_rule(&self, rule_idx: usize, args: &[Term]) -> Result<Thm> {
        let rule = self
            .rules
            .get(rule_idx)
            .ok_or_else(|| err(format!("dedukti::hol: no rule #{rule_idx}")))?;
        if args.len() != rule.patvars.len() {
            return Err(err(format!(
                "dedukti::hol: rule #{rule_idx} expects {} argument(s), got {}",
                rule.patvars.len(),
                args.len()
            )));
        }
        let enc = Encoder::new();
        let encoded: Vec<HTerm> = args.iter().map(|a| enc.encode(a)).collect::<Result<_>>()?;
        self.derive(rule.clause, encoded, vec![])
    }

    /// Transitivity: from `ab : ⊢ Derivable_Σ ⌜red a b⌝` and
    /// `bc : ⊢ Derivable_Σ ⌜red b c⌝`, build `⊢ Derivable_Σ ⌜red a c⌝`. The
    /// encoded `a`, `b`, `c` must match what `ab`/`bc` prove (the kernel checks).
    pub fn derive_trans(
        &self,
        a: HTerm,
        b: HTerm,
        c: HTerm,
        ab: &Thm,
        bc: &Thm,
    ) -> Result<Thm> {
        self.derive(TRANS, vec![a, b, c], vec![ab.clone(), bc.clone()])
    }

    /// Left application congruence: from `fg : ⊢ Derivable_Σ ⌜red f g⌝`, build
    /// `⊢ Derivable_Σ ⌜red (app f x) (app g x)⌝`.
    pub fn derive_cong_app_l(&self, f: HTerm, g: HTerm, x: HTerm, fg: &Thm) -> Result<Thm> {
        self.derive(CONG_APP_L, vec![f, g, x], vec![fg.clone()])
    }

    /// Right application congruence: from `xy : ⊢ Derivable_Σ ⌜red x y⌝`, build
    /// `⊢ Derivable_Σ ⌜red (app f x) (app f y)⌝`.
    pub fn derive_cong_app_r(&self, f: HTerm, x: HTerm, y: HTerm, xy: &Thm) -> Result<Thm> {
        self.derive(CONG_APP_R, vec![f, x, y], vec![xy.clone()])
    }

    /// The shared derivation spine: open the impredicative definition, instantiate
    /// clause `k`'s binders with `args`, discharge its premises with the opened
    /// sub-derivations `prems`, and re-package as `⊢ Derivable_Σ ⌜·⌝`.
    fn derive(&self, k: usize, args: Vec<HTerm>, prems: Vec<Thm>) -> Result<Thm> {
        let n = self.n;
        let d = self.rs.d_var();
        metalogic::derive_via_closed(&self.rs, move |assumed, _d_apply| {
            // `{Closed d} ⊢ clause_k[d]` = `∀binders. (prem) ⟹ d concl`.
            let mut clause = metalogic::nth_conjunct(assumed.clone(), k, n)?;
            for a in args {
                clause = clause.all_elim(a)?; // strip binders in order (outermost first)
            }
            if prems.is_empty() {
                return Ok(clause); // `{Closed d} ⊢ d concl`
            }
            // Open each `⊢ Derivable_Σ ⌜X⌝` to `{Closed d} ⊢ d X`, conjoin, discharge.
            let opened: Vec<Thm> = prems
                .iter()
                .map(|p| p.clone().all_elim(d.clone())?.imp_elim(assumed.clone()))
                .collect::<Result<_>>()?;
            clause.imp_elim(metalogic::conj_thms(opened)?)
        })
    }
}

/// Build a generic kernel error with a message.
fn err(msg: String) -> covalence_core::Error {
    covalence_core::Error::ConnectiveRule(msg)
}

// --- the structural generator specs ---

fn refl_spec() -> Result<ClauseSpec> {
    // ∀a. d (red a a)
    let a = svar("a");
    Ok(ClauseSpec {
        binders: vec![svar_name("a")],
        premises: vec![],
        conclusion: red(a.clone(), a)?,
    })
}

fn trans_spec() -> Result<ClauseSpec> {
    // ∀a b c. (d (red a b) ∧ d (red b c)) ⟹ d (red a c)
    let (a, b, c) = (svar("a"), svar("b"), svar("c"));
    Ok(ClauseSpec {
        binders: vec![svar_name("a"), svar_name("b"), svar_name("c")],
        premises: vec![red(a.clone(), b.clone())?, red(b, c.clone())?],
        conclusion: red(a, c)?,
    })
}

fn cong_app_l_spec() -> Result<ClauseSpec> {
    // ∀f g x. d (red f g) ⟹ d (red (app f x) (app g x))
    let (f, g, x) = (svar("f"), svar("g"), svar("x"));
    let lhs = app_fn().apply(f.clone())?.apply(x.clone())?;
    let rhs = app_fn().apply(g.clone())?.apply(x)?;
    Ok(ClauseSpec {
        binders: vec![svar_name("f"), svar_name("g"), svar_name("x")],
        premises: vec![red(f, g)?],
        conclusion: red(lhs, rhs)?,
    })
}

fn cong_app_r_spec() -> Result<ClauseSpec> {
    // ∀f x y. d (red x y) ⟹ d (red (app f x) (app f y))
    let (f, x, y) = (svar("f"), svar("x"), svar("y"));
    let lhs = app_fn().apply(f.clone())?.apply(x.clone())?;
    let rhs = app_fn().apply(f)?.apply(y.clone())?;
    Ok(ClauseSpec {
        binders: vec![svar_name("f"), svar_name("x"), svar_name("y")],
        premises: vec![red(x, y)?],
        conclusion: red(lhs, rhs)?,
    })
}

/// One generator per rewrite rule: `∀patvars. d (red ⌜lhs⌝ ⌜rhs⌝)`.
fn rule_spec(rule: &RewriteRule) -> Result<ClauseSpec> {
    let patvars: Vec<Symbol> = rule.context.iter().map(|c| c.name.clone()).collect();
    let enc = Encoder::with_patvars(patvars.iter().cloned());
    let lhs = enc.encode(&rule.lhs)?;
    let rhs = enc.encode(&rule.rhs)?;
    Ok(ClauseSpec {
        binders: patvars.iter().map(|p| patvar_name(p)).collect(),
        premises: vec![],
        conclusion: red(lhs, rhs)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;

    /// Encode a closed term from its `.dk` source (via a `def t := ….` wrapper).
    fn enc(src: &str) -> HTerm {
        let sig = parse(&format!("def t := {src}.")).unwrap();
        let body = match &sig.entries[0] {
            crate::Entry::Definition(d) => d.body.clone().unwrap(),
            _ => unreachable!(),
        };
        Encoder::new().encode(&body).unwrap()
    }

    #[test]
    fn encoder_round_trips_structure() {
        // `f a b` ⇒ dk$app (dk$app (dk$c$f) (dk$c$a)) (dk$c$b)
        let t = enc("f a b");
        let s = t.to_string();
        assert!(s.contains("dk$app"), "got {s}");
        assert!(s.contains("dk$c$f"), "got {s}");
    }

    #[test]
    fn derivable_statement_is_bool() {
        let sig = parse("Nat : Type. plus : Nat -> Nat -> Nat.").unwrap();
        let rs = SigRuleSet::build(&sig).unwrap();
        let stmt = rs.derivable_red(enc("plus"), enc("plus")).unwrap();
        // `Derivable_Σ ⌜…⌝` is a bool-typed term.
        assert_eq!(stmt.ty().unwrap(), &HType::bool());
    }

    /// The headline test: replay a genuine multi-step reduction through the
    /// kernel. With the Peano addition rules, derive
    /// `plus (succ zero) zero  ▷*  succ zero`, kernel-checked end to end.
    #[test]
    fn derives_a_peano_reduction() {
        let sig = parse(
            "Nat : Type. zero : Nat. succ : Nat -> Nat. \
             def plus : Nat -> Nat -> Nat. \
             [m] plus zero m --> m \
             [n,m] plus (succ n) m --> succ (plus n m).",
        )
        .unwrap();
        let rs = SigRuleSet::build(&sig).unwrap();
        assert_eq!(rs.n_rules(), 2); // rule 0: plus zero m; rule 1: plus (succ n) m

        // Step 1 — rule 1 with {n := zero, m := zero}:
        //   red (plus (succ zero) zero) (succ (plus zero zero))
        let nat_zero = Term::r("zero");
        let t1 = rs
            .derive_rule(1, &[nat_zero.clone(), nat_zero.clone()])
            .unwrap();

        // Step 2 — rule 0 with {m := zero}:  red (plus zero zero) zero
        let t2 = rs.derive_rule(0, &[nat_zero.clone()]).unwrap();

        // Lift step 2 under `succ` (an application):
        //   red (succ (plus zero zero)) (succ zero)
        let succ = enc("succ");
        let plus_zz = enc("plus zero zero");
        let zero_e = enc("zero");
        let t2_under_succ = rs
            .derive_cong_app_r(succ.clone(), plus_zz.clone(), zero_e.clone(), &t2)
            .unwrap();

        // Transitively compose:  red (plus (succ zero) zero) (succ zero)
        let a = enc("plus (succ zero) zero");
        let b = enc("succ (plus zero zero)");
        let c = enc("succ zero");
        let full = rs.derive_trans(a.clone(), b, c.clone(), &t1, &t2_under_succ).unwrap();

        // The conclusion is exactly `Derivable_Σ ⌜red a c⌝`, kernel-checked.
        let expected = rs.derivable_red(a, c).unwrap();
        assert_eq!(full.concl(), &expected);
        // And it is a genuine theorem with no outstanding hypotheses or observers.
        assert!(full.hyps().is_empty());
        assert!(full.has_no_obs());
    }
}
