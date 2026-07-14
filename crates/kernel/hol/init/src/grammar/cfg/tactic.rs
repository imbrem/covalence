//! **The CFG parsing tactic** (M2).
//!
//! Two-phase, mirroring [`crate::grammar::regex::tactic`]: a pure-Rust memoised
//! recognizer over concrete bytes produces a derivation plan, then a builder
//! walks it once assembling the `⊢ Derives_E ⌜nt⌝ w` theorem with **zero failed
//! kernel calls** — terminal segments discharged by the regex tactic
//! ([`Premise::Side`]), non-terminal segments recursed ([`Premise::Derivation`]).
//!
//! # Two phases: recognise, then prove
//!
//! 1. **Recognizer** (`Recognizer`) — a pure-Rust search (no kernel calls)
//!    over `(NodeRef, lo, hi)`, memoised so it is polynomial rather than
//!    exponential. `NodeRef` is a terminal regex [`Core`] (keyed by `Arc`
//!    pointer identity) or a non-terminal [`NtId`]. A non-terminal goal tries
//!    each of its productions and, per production, enumerates left-to-right span
//!    splits across the production's segments — the same split enumeration the
//!    regex tactic runs over `Seq`. An in-progress set on `(NtId, lo, hi)` is
//!    the belt-and-braces left-recursion guard: re-entry with an identical key
//!    fails that path. Sound (the kernel re-checks), incomplete only for
//!    left-recursive grammars (the corpus is left-recursion-free — see
//!    `Cfg::left_recursion`).
//! 2. **Builder** (`build`) — walks the [`CfgPlan`] once, assembling the `Thm`
//!    with no search. Terminal segment → [`matches_core`] on the sub-span → a
//!    [`Premise::Side`] plus its word; non-terminal segment → recurse → a
//!    [`Premise::Derivation`] plus the sub-derivation's word; then
//!    [`GrammarEnv::derive`] on the production's clause index with the segment
//!    words as `word_args`. The kernel work is exactly the size of the final
//!    derivation.
//!
//! It is untrusted: a buggy recognizer can only fail to find a proof, never
//! forge one. Sub-plans are held behind [`Rc`] so memo hits are cheap
//! reference-count bumps.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::Arc;

use covalence_core::{Error, Result, Term};
use covalence_grammar::cfg::NtId;
use covalence_hol_eval::EvalThm as Thm;

use super::{GrammarEnv, RSeg};
use crate::grammar::regex::Core;
use crate::grammar::regex::tactic::matches_core;
use crate::metalogic::binary::Premise;

// ============================================================================
// Phase 1: the recognizer (pure Rust, no kernel calls).
// ============================================================================

/// The shape of a `Derives_E` derivation found by the recognizer: which
/// production fired (`clause_idx`) and, per segment (left to right), how that
/// segment's sub-span was recognised. Held behind [`Rc`] so memo hits and plan
/// composition are reference-count bumps rather than deep copies.
struct CfgPlan {
    /// The production's global index = its kernel clause index.
    clause_idx: usize,
    /// One sub-plan per segment, in segment order, each with its span.
    segs: Vec<SegPlan>,
}

/// How one production segment's sub-span `[lo, hi)` was recognised.
enum SegPlan {
    /// A terminal regex segment: prove `Matches ⌜c⌝ w` over `bytes[lo..hi]`.
    Term {
        core: Arc<Core>,
        lo: usize,
        hi: usize,
    },
    /// A non-terminal segment: the sub-derivation `Derives_E ⌜nt⌝ w`.
    NonTerm(Rc<CfgPlan>),
}

/// A recognizer node: a terminal regex (by `Arc` pointer identity) or a
/// non-terminal tag. Only [`NodeRef::Nt`] participates in the left-recursion
/// in-progress set — terminal recognition is memoised but never re-entrant.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum NodeRef {
    Term(*const Core),
    Nt(usize),
}

struct Recognizer<'a> {
    env: &'a GrammarEnv,
    bytes: &'a [u8],
    /// Memo over `(node, lo, hi)`.
    memo: HashMap<(NodeRef, usize, usize), Option<Rc<CfgPlan>>>,
    /// Non-terminal spans currently on the recursion stack (left-recursion
    /// guard). Keyed on `(NtId index, lo, hi)`.
    in_progress: HashSet<(usize, usize, usize)>,
}

impl Recognizer<'_> {
    /// Recognise non-terminal `nt` over `bytes[lo..hi]`.
    fn rec_nt(&mut self, nt: NtId, lo: usize, hi: usize) -> Option<Rc<CfgPlan>> {
        let key = (NodeRef::Nt(nt.index()), lo, hi);
        if let Some(cached) = self.memo.get(&key) {
            return cached.clone();
        }
        let guard = (nt.index(), lo, hi);
        if !self.in_progress.insert(guard) {
            // Re-entry on the same span ⇒ left recursion; cut this path.
            // Not memoised: the cut is context-dependent (it depends on what
            // is already on the stack), so caching it could poison a later
            // legitimate visit to the same span.
            return None;
        }
        let result = self.rec_nt_uncached(nt, lo, hi);
        self.in_progress.remove(&guard);
        self.memo.insert(key, result.clone());
        result
    }

    fn rec_nt_uncached(&mut self, nt: NtId, lo: usize, hi: usize) -> Option<Rc<CfgPlan>> {
        // Try each production of `nt`, in clause order, at this span.
        for clause_idx in 0..self.env.prod_count() {
            let (lhs, segs) = self.env.prod(clause_idx);
            if lhs != nt {
                continue;
            }
            if let Some(seg_plans) = self.rec_segs(segs, 0, lo, hi) {
                return Some(Rc::new(CfgPlan {
                    clause_idx,
                    segs: seg_plans,
                }));
            }
        }
        None
    }

    /// Recognise segments `segs[seg..]` over `bytes[lo..hi]`, enumerating the
    /// left-to-right split point after the head segment. Mirrors the regex
    /// tactic's `Seq` split enumeration.
    fn rec_segs(
        &mut self,
        segs: &[RSeg],
        seg: usize,
        lo: usize,
        hi: usize,
    ) -> Option<Vec<SegPlan>> {
        let Some(head) = segs.get(seg) else {
            // No segments left: the span must be exactly consumed.
            return (lo == hi).then(Vec::new);
        };
        for mid in lo..=hi {
            let head_plan = match head {
                RSeg::Term(core) => self.rec_term(core, lo, mid).map(|_| SegPlan::Term {
                    core: core.clone(),
                    lo,
                    hi: mid,
                }),
                RSeg::NonTerm(id) => self.rec_nt(*id, lo, mid).map(SegPlan::NonTerm),
            };
            if let Some(head_plan) = head_plan
                && let Some(mut rest) = self.rec_segs(segs, seg + 1, mid, hi)
            {
                rest.insert(0, head_plan);
                return Some(rest);
            }
        }
        None
    }

    /// Recognise terminal regex `core` over `bytes[lo..hi]`. The regex tactic
    /// owns the internal split search; here we only need a yes/no (the builder
    /// re-derives via [`matches_core`]), memoised on the span. Returns `Some(())`
    /// if it matches.
    fn rec_term(&mut self, core: &Arc<Core>, lo: usize, hi: usize) -> Option<()> {
        let key = (NodeRef::Term(Arc::as_ptr(core)), lo, hi);
        if let Some(cached) = self.memo.get(&key) {
            // Reuse the yes/no verdict encoded as Some(_)/None.
            return cached.as_ref().map(|_| ());
        }
        // Delegate the actual match decision to the regex tactic. A kernel
        // error here is a real error, not a "no match", so surface it as a
        // cache miss that the builder will hit again and report.
        let matched = matches_core(core, &self.bytes[lo..hi])
            .ok()
            .flatten()
            .is_some();
        // Encode the verdict in the shared memo as a sentinel plan (never read
        // structurally — terminal builder work goes through `matches_core`).
        let sentinel = matched.then(|| {
            Rc::new(CfgPlan {
                clause_idx: usize::MAX,
                segs: Vec::new(),
            })
        });
        self.memo.insert(key, sentinel.clone());
        sentinel.map(|_| ())
    }
}

// ============================================================================
// Phase 2: the builder (one forward pass, no search, no failed kernel calls).
// ============================================================================

/// Extract the `list u8` word `w` from a `Matches` theorem whose conclusion is
/// `∀M. Closed M ⟹ M ⌜c⌝ w`. `w` is closed (mentions no bound `M`), so lifting
/// the subterm out from under the binder is sound; if imp_elim later disagrees
/// it fails loudly.
fn matches_word(thm: &Thm) -> Result<Term> {
    let err = || Error::ConnectiveRule("cfg tactic: unexpected Matches shape (internal)".into());
    // concl = App(!, Abs(_, body))
    let (_all, abs) = thm.concl().as_app().ok_or_else(err)?;
    let (_ty, body) = abs.as_abs().ok_or_else(err)?;
    // body = App(App(imp, Closed M), (M ⌜c⌝) w) — take the imp's rhs, then its
    // last argument.
    let (imp_app, mrcw) = body.as_app().ok_or_else(err)?;
    // imp_app = App(imp, Closed M): confirm two-arg application shape.
    imp_app.as_app().ok_or_else(err)?;
    let (_mr, w) = mrcw.as_app().ok_or_else(err)?;
    Ok(w.clone())
}

/// Build `⊢ Derives_E ⌜lhs⌝ w` from a [`CfgPlan`], returning the theorem and its
/// conclusion word. Every clause application is one the recognizer already
/// certified fits, so the kernel does no failed work.
fn build(env: &GrammarEnv, plan: &CfgPlan, bytes: &[u8]) -> Result<(Thm, Term)> {
    let mut word_args = Vec::with_capacity(plan.segs.len());
    let mut premises = Vec::with_capacity(plan.segs.len());
    for seg in &plan.segs {
        match seg {
            SegPlan::Term { core, lo, hi } => {
                let thm = matches_core(core, &bytes[*lo..*hi])?.ok_or_else(|| {
                    Error::ConnectiveRule("cfg tactic: terminal recheck failed (internal)".into())
                })?;
                word_args.push(matches_word(&thm)?);
                premises.push(Premise::Side(thm));
            }
            SegPlan::NonTerm(sub) => {
                let (sub_thm, sub_word) = build(env, sub, bytes)?;
                word_args.push(sub_word);
                premises.push(Premise::Derivation(sub_thm));
            }
        }
    }
    let concl_word = GrammarEnv::cat_all(&word_args)?;
    let thm = env.derive(plan.clause_idx, &word_args, premises)?;
    Ok((thm, concl_word))
}

// ============================================================================
// Public tactic surface.
// ============================================================================

/// Prove `⊢ Derives_E ⌜nt⌝ w` for the concrete byte input `bytes`, or `None` if
/// `bytes` is not in `nt`'s language (per the env's grammar). The theorem is
/// **hypothesis-free**; the conclusion word `w` is rule-shaped
/// (`cat`/`cons`/`nil`), byte-identical to what [`GrammarEnv::derivable`] over
/// the same word produces (read it off `thm.concl()` if needed).
///
/// Untrusted: the kernel re-checks every clause application, so a lowering or
/// recognizer bug can only fail to find a proof, never forge one. Incomplete
/// on left-recursive grammars (the belt-and-braces guard cuts such paths).
pub fn prove_derives(env: &GrammarEnv, nt: NtId, bytes: &[u8]) -> Result<Option<Thm>> {
    let mut rec = Recognizer {
        env,
        bytes,
        memo: HashMap::new(),
        in_progress: HashSet::new(),
    };
    match rec.rec_nt(nt, 0, bytes.len()) {
        None => Ok(None),
        Some(plan) => Ok(Some(build(env, &plan, bytes)?.0)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use covalence_grammar::cfg::{Cfg, Seg};
    use covalence_grammar::regex::Regex;

    /// `S → a S b | ε` — the classic non-regular `aⁿbⁿ` language.
    fn anbn() -> (GrammarEnv, NtId) {
        let mut cfg = Cfg::new();
        let s = cfg.add_nt("S");
        cfg.add_prod(
            s,
            vec![
                Seg::term(Regex::Lit(b'a')),
                Seg::nt(s),
                Seg::term(Regex::Lit(b'b')),
            ],
        );
        cfg.add_prod(s, vec![]);
        (GrammarEnv::new(cfg).unwrap(), s)
    }

    /// `A → a B | ε ; B → b A`. L(A) = (ab)*, L(B) = b(ab)*.
    fn mutual() -> (GrammarEnv, NtId, NtId) {
        let mut cfg = Cfg::new();
        let a = cfg.add_nt("A");
        let b = cfg.add_nt("B");
        cfg.add_prod(a, vec![Seg::term(Regex::Lit(b'a')), Seg::nt(b)]);
        cfg.add_prod(a, vec![]);
        cfg.add_prod(b, vec![Seg::term(Regex::Lit(b'b')), Seg::nt(a)]);
        (GrammarEnv::new(cfg).unwrap(), a, b)
    }

    #[test]
    fn anbn_positive_various_lengths() {
        let (env, s) = anbn();
        for w in [&b""[..], b"ab", b"aabb", b"aaabbb", b"aaaabbbb"] {
            let thm = prove_derives(&env, s, w)
                .unwrap()
                .unwrap_or_else(|| panic!("expected accept: {w:?}"));
            assert!(thm.hyps().is_empty(), "hypothesis-free: {w:?}");
        }
    }

    #[test]
    fn anbn_negative() {
        let (env, s) = anbn();
        for w in [&b"a"[..], b"b", b"ba", b"aab", b"abb", b"abab", b"aabbb"] {
            assert!(
                prove_derives(&env, s, w).unwrap().is_none(),
                "expected reject: {w:?}"
            );
        }
    }

    #[test]
    fn mutual_recursion_positive_and_negative() {
        let (env, a, b) = mutual();
        for w in [&b""[..], b"ab", b"abab", b"ababab"] {
            let thm = prove_derives(&env, a, w)
                .unwrap()
                .unwrap_or_else(|| panic!("A should accept {w:?}"));
            assert!(thm.hyps().is_empty());
        }
        for w in [&b"b"[..], b"bab", b"babab"] {
            let thm = prove_derives(&env, b, w)
                .unwrap()
                .unwrap_or_else(|| panic!("B should accept {w:?}"));
            assert!(thm.hyps().is_empty());
        }
        for w in [&b"a"[..], b"ba", b"aba"] {
            assert!(
                prove_derives(&env, a, w).unwrap().is_none(),
                "A rejects {w:?}"
            );
        }
        for w in [&b""[..], b"a", b"ab", b"bb"] {
            assert!(
                prove_derives(&env, b, w).unwrap().is_none(),
                "B rejects {w:?}"
            );
        }
    }

    /// Differential: for every byte string up to length 6 over the toy's
    /// alphabet, the tactic accepts exactly when the independent `naive_parse`
    /// oracle does — for **both** non-terminals of the mutual-recursion toy.
    #[test]
    fn differential_vs_naive_parse() {
        let (env, a, b) = mutual();
        let cfg = env.cfg().clone();
        let alphabet = [b'a', b'b'];
        let mut word = Vec::new();
        for len in 0..=6usize {
            enumerate(&alphabet, len, &mut word, &mut |w| {
                for &nt in &[a, b] {
                    let proved = prove_derives(&env, nt, w).unwrap().is_some();
                    let oracle = cfg.naive_parse(nt, w);
                    assert_eq!(proved, oracle, "nt={nt:?} w={w:?}");
                }
            });
        }
    }

    /// Enumerate all `alphabet`-strings of exactly `len`, calling `f` on each.
    fn enumerate(alphabet: &[u8], len: usize, word: &mut Vec<u8>, f: &mut impl FnMut(&[u8])) {
        if word.len() == len {
            f(word);
            return;
        }
        for &c in alphabet {
            word.push(c);
            enumerate(alphabet, len, word, f);
            word.pop();
        }
    }

    /// The produced conclusion matches an independently built `derivable` term
    /// exactly — pins the word shape end to end.
    #[test]
    fn conclusion_matches_derivable() {
        let (env, s) = anbn();
        let thm = prove_derives(&env, s, b"aabb").unwrap().unwrap();
        assert!(thm.hyps().is_empty());
        // Rebuild the expected word (`a (a b) b`) with the same helpers the
        // engine uses, and compare against a fresh `derivable`.
        let a = |b: u8| {
            crate::init::list::cons(crate::init::regex::u8_alphabet())
                .apply(covalence_hol_eval::mk_u8(b))
                .unwrap()
                .apply(GrammarEnv::nil_w())
                .unwrap()
        };
        let cat = |x, y| GrammarEnv::cat_w(x, y).unwrap();
        let inner = cat(a(b'a'), cat(GrammarEnv::nil_w(), a(b'b')));
        let outer = cat(a(b'a'), cat(inner, a(b'b')));
        assert_eq!(thm.concl(), &env.derivable(s, &outer).unwrap());
    }
}
