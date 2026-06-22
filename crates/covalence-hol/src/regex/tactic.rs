//! The **matching tactic**: search for a `Matches ⌜r⌝ w` derivation and
//! assemble it from [`crate::init::regex`]'s seven rule constructors.
//!
//! Two entry points:
//!
//! - [`prove_matches`] takes a regex and a **concrete** bytestring and returns
//!   `⊢ Matches ⌜r⌝ w` (or `None` if the bytes are not in the language). The
//!   word `w` is built rule-shaped: byte literals, `cat`, single-byte `cons`,
//!   and `nil`.
//! - [`prove_word`] takes a [`Word`] — an expression of byte literals,
//!   concatenation, and **variables** carrying a "parses as this category"
//!   assumption — and returns `{Matches ⌜cᵢ⌝ Xᵢ}ᵢ ⊢ Matches ⌜r⌝ w`. A variable
//!   token is opaque: it is consumed only by matching the regex sub-goal that
//!   equals its category, discharged against the assumption `Matches ⌜cᵢ⌝ Xᵢ`.
//!   This is the seed for grammar *composition* — "a section is a header then a
//!   payload that parses as `Vec(func)`" — and for sharing one derivation
//!   across Metamath / WASM / S-expression grammars.
//!
//! # Two phases: recognise, then prove
//!
//! Matching is split into a fast **recognizer** and a separate **builder**, so
//! the kernel only ever sees the *winning* derivation:
//!
//! 1. **Recognizer** ([`Recognizer`]) — a pure-Rust search (no kernel calls)
//!    that decides whether the input matches and, if so, returns a [`Plan`]: the
//!    shape of the derivation (which `alt` branch, where each `seq`/`star`
//!    splits). It memoises on `(node, span)`, so it is polynomial rather than
//!    exponential, and it only checks *simple* properties — does this byte match
//!    this literal, does this prefix match — so it is the natural place to drop
//!    in a WASM/builtin accelerator later.
//! 2. **Builder** ([`build`]) — walks the `Plan` once and assembles the `Thm`
//!    from [`crate::init::regex`]'s rules, with **no search and no failed kernel
//!    calls**. Kernel work is exactly the size of the final derivation.
//!
//! This is the key performance property: a single-phase matcher that built the
//! `Thm` as it searched would build (and discard) kernel objects for branches
//! that ultimately fail; separating the phases removes that waste entirely. It
//! is still untrusted — the kernel re-checks every rule the builder applies, so
//! a buggy recognizer can only fail to find a proof, never forge one.

use std::collections::HashMap;
use std::rc::Rc;

use covalence_core::{Result, Term, Thm, Type};
use covalence_grammar::regex::Regex;

use super::{Core, core_to_term, desugar};
use crate::init::ext::TermExt;
use crate::init::regex as ir;

// ============================================================================
// Word terms (the rule-shaped `list u8` the derivations talk about).
// ============================================================================

fn u8ty() -> Type {
    ir::u8_alphabet()
}

fn word_ty() -> Type {
    crate::init::list::list(u8ty())
}

fn nil_w() -> Term {
    crate::init::list::nil(u8ty())
}

fn cons_w(b: u8, rest: Term) -> Result<Term> {
    crate::init::list::cons(u8ty())
        .apply(Term::u8_lit(b))?
        .apply(rest)
}

fn singleton_w(b: u8) -> Result<Term> {
    cons_w(b, nil_w())
}

fn cat_w(w1: Term, w2: Term) -> Result<Term> {
    crate::init::list::list_cat(u8ty()).apply(w1)?.apply(w2)
}

// ============================================================================
// The atom sequence the matcher runs over.
// ============================================================================

/// A variable occurring in a [`Word`]: a free `list u8` term `X` assumed to
/// parse as `category`.
struct VarInfo {
    name: String,
    term: Term,
    category: Core,
}

/// One position of the flattened input: a concrete byte, or a variable token
/// (index into the var table).
#[derive(Clone, Copy)]
enum Atom {
    Byte(u8),
    Var(usize),
}

// ============================================================================
// Phase 1: the recognizer (pure Rust, no kernel calls).
//
// Decides "do `atoms[lo..hi]` match `c`, and how" and returns a `Plan` — the
// derivation skeleton — which phase 2 turns into a `Thm`. Memoised on
// `(node, lo, hi)`, so the search is polynomial, not exponential. This is the
// part to accelerate with WASM/builtins later: it only checks simple
// properties (does a byte match a literal, does a prefix match).
// ============================================================================

/// The shape of a `Matches` derivation found by the recognizer. Carries exactly
/// what [`build`] needs and nothing about the kernel.
///
/// Sub-plans are held behind [`Rc`] so memo hits and plan composition are cheap
/// reference-count bumps rather than deep copies.
enum Plan {
    /// `eps` matched the empty word.
    Eps,
    /// `lit` matched a single byte (the byte is read from the `Core`).
    Lit,
    /// `alt`: the left branch matched.
    AltL(Rc<Plan>),
    /// `alt`: the right branch matched.
    AltR(Rc<Plan>),
    /// `seq`: left then right.
    Seq(Rc<Plan>, Rc<Plan>),
    /// `star` matched the empty word.
    StarNil,
    /// `star`: one `x`-iteration then the rest.
    StarStep(Rc<Plan>, Rc<Plan>),
    /// variable token `i`, consumed by its `parses-as` assumption.
    Var(usize),
}

/// Recognizer state: the fixed atom array, the var table, and a memo over
/// `(core node, lo, hi)` so each sub-problem is solved once.
struct Recognizer<'a> {
    atoms: &'a [Atom],
    vars: &'a [VarInfo],
    memo: HashMap<(usize, usize, usize), Option<Rc<Plan>>>,
}

impl Recognizer<'_> {
    fn rec(&mut self, c: &Core, lo: usize, hi: usize) -> Option<Rc<Plan>> {
        // Core nodes are owned in a stable, immutable tree for the run, so the
        // node pointer is a sound memo key.
        let key = (c as *const Core as usize, lo, hi);
        if let Some(cached) = self.memo.get(&key) {
            return cached.clone();
        }
        let result = self.rec_uncached(c, lo, hi);
        self.memo.insert(key, result.clone());
        result
    }

    fn rec_uncached(&mut self, c: &Core, lo: usize, hi: usize) -> Option<Rc<Plan>> {
        // Variable rule: a lone variable token (a one-atom span) is consumed
        // only by the regex goal that *is* its category.
        if hi - lo == 1 {
            if let Atom::Var(i) = self.atoms[lo] {
                if *c == self.vars[i].category {
                    return Some(Rc::new(Plan::Var(i)));
                }
                // Otherwise fall through: a structural goal (alt/seq/star) may
                // still recurse and bottom out here with a matching sub-core.
            }
        }

        match c {
            Core::Empty => None,
            Core::Eps => (lo == hi).then(|| Rc::new(Plan::Eps)),
            Core::Lit(b) => match (hi - lo == 1).then(|| self.atoms[lo]) {
                Some(Atom::Byte(x)) if x == *b => Some(Rc::new(Plan::Lit)),
                _ => None,
            },
            Core::Alt(x, y) => {
                if let Some(p) = self.rec(x, lo, hi) {
                    return Some(Rc::new(Plan::AltL(p)));
                }
                self.rec(y, lo, hi).map(|p| Rc::new(Plan::AltR(p)))
            }
            Core::Seq(x, y) => {
                for k in lo..=hi {
                    if let Some(px) = self.rec(x, lo, k) {
                        if let Some(py) = self.rec(y, k, hi) {
                            return Some(Rc::new(Plan::Seq(px, py)));
                        }
                    }
                }
                None
            }
            Core::Star(x) => {
                if lo == hi {
                    return Some(Rc::new(Plan::StarNil));
                }
                // Non-empty prefix (k > lo) keeps the recursion strictly
                // decreasing and avoids looping on a nullable `x`.
                for k in (lo + 1)..=hi {
                    if let Some(px) = self.rec(x, lo, k) {
                        if let Some(ps) = self.rec(c, k, hi) {
                            return Some(Rc::new(Plan::StarStep(px, ps)));
                        }
                    }
                }
                None
            }
        }
    }
}

// ============================================================================
// Compiled matcher — phase 2: the builder (one forward pass, no search).
//
// Every rule here is one the recognizer already certified fits, so the kernel
// work is exactly the size of the final derivation — no failed calls.
// ============================================================================

/// Build `⊢ Matches ⌜c⌝ w` from the recognizer's `plan`.
fn build(c: &Core, plan: &Plan, vars: &[VarInfo]) -> Result<(Thm, Term)> {
    let a = u8ty();
    match (c, plan) {
        (_, Plan::Var(i)) => {
            let vi = &vars[*i];
            let prop = ir::matches(&a, &core_to_term(c), &vi.term)?;
            Ok((Thm::assume(prop)?, vi.term.clone()))
        }
        (Core::Eps, Plan::Eps) => Ok((ir::match_eps(&a)?, nil_w())),
        (Core::Lit(b), Plan::Lit) => {
            let th = ir::match_lit(&a)?.all_elim(Term::u8_lit(*b))?;
            Ok((th, singleton_w(*b)?))
        }
        (Core::Alt(x, y), Plan::AltL(p)) => {
            let (thx, w) = build(x, p, vars)?;
            let th = ir::match_alt_l(&a, &core_to_term(x), &core_to_term(y), &w)?.imp_elim(thx)?;
            Ok((th, w))
        }
        (Core::Alt(x, y), Plan::AltR(p)) => {
            let (thy, w) = build(y, p, vars)?;
            let th = ir::match_alt_r(&a, &core_to_term(x), &core_to_term(y), &w)?.imp_elim(thy)?;
            Ok((th, w))
        }
        (Core::Seq(x, y), Plan::Seq(px, py)) => {
            let (thx, w1) = build(x, px, vars)?;
            let (thy, w2) = build(y, py, vars)?;
            let th = ir::match_seq(&a, &core_to_term(x), &core_to_term(y), &w1, &w2)?
                .imp_elim(thx)?
                .imp_elim(thy)?;
            Ok((th, cat_w(w1, w2)?))
        }
        (Core::Star(x), Plan::StarNil) => Ok((ir::match_star_nil(&a, &core_to_term(x))?, nil_w())),
        (Core::Star(x), Plan::StarStep(px, ps)) => {
            let (thx, w1) = build(x, px, vars)?;
            let (thstar, w2) = build(c, ps, vars)?;
            let th = ir::match_star_step(&a, &core_to_term(x), &w1, &w2)?
                .imp_elim(thx)?
                .imp_elim(thstar)?;
            Ok((th, cat_w(w1, w2)?))
        }
        // The recognizer only emits a plan fitting the core it ran on, so a
        // mismatch is an internal invariant violation, not a user error.
        _ => Err(covalence_core::Error::ConnectiveRule(
            "regex tactic: plan does not fit core (internal)".into(),
        )),
    }
}

/// Recognise then build: search for a derivation skeleton, then assemble the
/// `Thm`. The single entry point both phases run through.
fn run(core: &Core, atoms: &[Atom], vars: &[VarInfo]) -> Result<Option<(Thm, Term)>> {
    let mut rec = Recognizer {
        atoms,
        vars,
        memo: HashMap::new(),
    };
    match rec.rec(core, 0, atoms.len()) {
        None => Ok(None),
        Some(plan) => Ok(Some(build(core, &plan, vars)?)),
    }
}

// ============================================================================
// Public tactic surface.
// ============================================================================

fn byte_atoms(bytes: &[u8]) -> Vec<Atom> {
    bytes.iter().map(|&b| Atom::Byte(b)).collect()
}

/// Prove `⊢ Matches ⌜r⌝ w` for the concrete byte input, or `None` if it is not
/// in `L(r)`. The input is anything byte-like — `&str`, `&[u8]`, `Vec<u8>`,
/// `[u8; N]`, `b"…"` — via [`AsRef<[u8]>`]. `w` is rule-shaped (byte literals +
/// `cat` + single-byte `cons` + `nil`); read it off `thm.concl()` if you need it.
pub fn prove_matches(r: &Regex<u8>, input: impl AsRef<[u8]>) -> Result<Option<Thm>> {
    prove_matches_bytes(r, input.as_ref())
}

fn prove_matches_bytes(r: &Regex<u8>, bytes: &[u8]) -> Result<Option<Thm>> {
    let core = desugar(r);
    Ok(run(&core, &byte_atoms(bytes), &[])?.map(|(thm, _)| thm))
}

/// Prove that the input is **in the language** the regex denotes:
/// `⊢ mem w ⟦⌜r⌝⟧`. Chains [`prove_matches`] through regex *soundness*
/// ([`crate::init::regex::soundness_at`]). Accepts any [`AsRef<[u8]>`].
pub fn prove_member(r: &Regex<u8>, input: impl AsRef<[u8]>) -> Result<Option<Thm>> {
    prove_member_bytes(r, input.as_ref())
}

fn prove_member_bytes(r: &Regex<u8>, bytes: &[u8]) -> Result<Option<Thm>> {
    let a = u8ty();
    let core = desugar(r);
    let rterm = core_to_term(&core);
    let Some((der, w)) = run(&core, &byte_atoms(bytes), &[])? else {
        return Ok(None);
    };
    // Soundness lives at the denotation instance `'r := set (list u8)`; the
    // `Matches`/rule machinery is schematic in `'r`, so pin the derivation
    // there before discharging it into soundness.
    let lang_ty = ir::denote(&a, rterm.clone())?.type_of()?;
    let der = der.inst_tfree("r", lang_ty)?;
    let snd = ir::soundness_at(&a, &rterm, &w)?; // ⊢ Matches r w ⟹ mem w ⟦r⟧
    Ok(Some(snd.imp_elim(der)?))
}

/// A bytestring **expression** the matcher can prove against — byte literals,
/// concatenation, and variables carrying a "parses as this category"
/// assumption. The general (bonus) input shape: with no [`Word::Var`] it is an
/// ordinary concrete bytestring, equivalent to [`prove_matches`].
pub enum Word {
    /// The empty word.
    Nil,
    /// A single byte.
    Byte(u8),
    /// A literal block of bytes.
    Bytes(Vec<u8>),
    /// Concatenation `w₁ w₂`.
    Cat(Box<Word>, Box<Word>),
    /// A variable `X` assumed to parse as `category` (its occurrences share one
    /// free `list u8` variable, keyed by `name`).
    Var { name: String, category: Regex<u8> },
}

impl Word {
    /// `w₁ w₂`.
    pub fn cat(w1: Word, w2: Word) -> Word {
        Word::Cat(Box::new(w1), Box::new(w2))
    }

    /// A literal block of bytes (`&str`, `&[u8]`, `Vec<u8>`, …).
    pub fn bytes(b: impl AsRef<[u8]>) -> Word {
        Word::Bytes(b.as_ref().to_vec())
    }

    /// A variable `X` assumed to parse as `category`.
    pub fn var(name: impl Into<String>, category: Regex<u8>) -> Word {
        Word::Var {
            name: name.into(),
            category,
        }
    }
}

fn flatten(w: &Word, atoms: &mut Vec<Atom>, vars: &mut Vec<VarInfo>) {
    match w {
        Word::Nil => {}
        Word::Byte(b) => atoms.push(Atom::Byte(*b)),
        Word::Bytes(bs) => atoms.extend(bs.iter().map(|&b| Atom::Byte(b))),
        Word::Cat(l, r) => {
            flatten(l, atoms, vars);
            flatten(r, atoms, vars);
        }
        Word::Var { name, category } => {
            let idx = match vars.iter().position(|v| &v.name == name) {
                Some(i) => i,
                None => {
                    vars.push(VarInfo {
                        name: name.clone(),
                        term: Term::free(name, word_ty()),
                        category: desugar(category),
                    });
                    vars.len() - 1
                }
            };
            atoms.push(Atom::Var(idx));
        }
    }
}

/// Prove `{Matches ⌜cᵢ⌝ Xᵢ}ᵢ ⊢ Matches ⌜r⌝ w` for a word **expression** that may
/// contain variables, or `None` if no derivation exists. Each distinct
/// [`Word::Var`] contributes one `Matches ⌜category⌝ X` hypothesis.
pub fn prove_word(r: &Regex<u8>, w: &Word) -> Result<Option<Thm>> {
    let core = desugar(r);
    let mut atoms = Vec::new();
    let mut vars = Vec::new();
    flatten(w, &mut atoms, &mut vars);
    Ok(run(&core, &atoms, &vars)?.map(|(thm, _)| thm))
}

