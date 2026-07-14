//! **The CFG stratum** — a kernel-checked `Derives` judgement over context-free
//! grammars whose terminals are byte regexes, one stratum up from
//! [`crate::init::regex`]'s `Matches`.
//!
//! This is the untrusted *driver*: it lowers a neutral
//! [`covalence_grammar::cfg::Cfg<u8>`] into a binary rule set
//! ([`crate::metalogic::binary::RuleSet2`]) and drives derivations. The kernel
//! re-checks every step, so a lowering bug can only fail to prove, never forge.
//!
//! ## The judgement
//!
//! A [`GrammarEnv`] assigns each non-terminal a **`nat`-literal tag** (its dense
//! `Cfg` index — names are efficiency, never soundness) and lowers every
//! production, *in `Cfg`'s deterministic order*, to one closure clause. For a
//! production `NT → σ₁…σₖ`:
//!
//! ```text
//!   ∀w₁…wₖ. A₁ ⟹ … ⟹ Aₖ ⟹ d ⌜NT⌝ (cat w₁ (cat w₂ … wₖ))
//! ```
//!
//! where `Aⱼ = Matches ⌜cⱼ⌝ wⱼ` for a terminal segment (a **side** antecedent
//! embedding the existing reified `regex u8` term, so `init::regex`'s `Matches`
//! theorems plug in as leaf premises) and `Aⱼ = d ⌜NTⱼ⌝ wⱼ` for a non-terminal
//! segment. All non-terminals share one `d`, so mutual recursion and
//! cross-grammar references compose for free. The judgement is
//!
//! ```text
//!   Derives_E n w := ∀d. Closed_E d ⟹ d n w
//! ```
//!
//! All clauses are first-order (quantifiers only over `list u8` words), so the
//! β-capture wall does not bite.
//!
//! See `notes/vibes/logics/cfg-stratum-design.md` for the full design (soundness
//! is the discharge-free family least-fixpoint package in [`soundness`], the
//! parsing tactic in [`tactic`]).

use std::sync::Arc;

use covalence_core::{Result, Term, Type};
use covalence_grammar::cfg::{Cfg, NtId, Seg};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::mk_nat;

use crate::grammar::regex::{Core, desugar};
use crate::init::ext::TermExt;
use crate::metalogic::binary::{Premise, RuleSet2, derivable2, derive_mixed};

pub mod soundness;
pub mod tactic;

/// A reified production segment: a desugared terminal regex (whose `.term()` is
/// the reified `⌜c⌝ : regex u8`) or a non-terminal reference.
pub(crate) enum RSeg {
    /// A terminal byte-regex segment, desugared once.
    Term(Arc<Core>),
    /// A non-terminal reference (by `Cfg` index = tag).
    NonTerm(NtId),
}

/// A **grammar environment**: a validated [`Cfg<u8>`] with its productions
/// pre-reified into clauses. The unit of derivation and (per-env) soundness.
pub struct GrammarEnv {
    cfg: Cfg<u8>,
    /// Per production (in `cfg.productions()` order = clause order), the lhs tag
    /// and reified segments.
    prods: Vec<(NtId, Vec<RSeg>)>,
}

impl GrammarEnv {
    /// Build an environment from a neutral CFG, validating references and
    /// pre-desugaring every terminal segment.
    pub fn new(cfg: Cfg<u8>) -> Result<Self> {
        cfg.validate()
            .map_err(|e| covalence_core::Error::ConnectiveRule(format!("cfg: {e}")))?;
        let prods = cfg
            .productions()
            .iter()
            .map(|p| {
                let segs = p
                    .segs
                    .iter()
                    .map(|s| match s {
                        Seg::Term(r) => RSeg::Term(desugar(r)),
                        Seg::NonTerm(id) => RSeg::NonTerm(*id),
                    })
                    .collect();
                (p.lhs, segs)
            })
            .collect();
        Ok(GrammarEnv { cfg, prods })
    }

    /// The source grammar.
    pub fn cfg(&self) -> &Cfg<u8> {
        &self.cfg
    }

    /// The number of closure clauses (= number of productions).
    pub fn n_clauses(&self) -> usize {
        self.prods.len()
    }

    /// Resolve a non-terminal by name.
    pub fn nt(&self, name: &str) -> Option<NtId> {
        self.cfg.lookup(name)
    }

    /// The reified `nat`-literal tag of a non-terminal (its `Cfg` index).
    pub fn tag(&self, nt: NtId) -> Term {
        mk_nat(nt.index() as u64)
    }

    /// The u8 word alphabet type `list u8`.
    pub(crate) fn word_ty() -> Type {
        crate::init::list::list(crate::init::regex::u8_alphabet())
    }

    /// `nil : list u8`.
    pub(crate) fn nil_w() -> Term {
        crate::init::list::nil(crate::init::regex::u8_alphabet())
    }

    /// `cat w1 w2 : list u8`.
    pub(crate) fn cat_w(w1: Term, w2: Term) -> Result<Term> {
        crate::init::list::list_cat(crate::init::regex::u8_alphabet())
            .apply(w1)?
            .apply(w2)
    }

    /// The right-nested concatenation of `words` (`nil` if empty, the lone word
    /// if one) — the conclusion word shape of a production clause.
    pub(crate) fn cat_all(words: &[Term]) -> Result<Term> {
        match words {
            [] => Ok(Self::nil_w()),
            [w] => Ok(w.clone()),
            [first, rest @ ..] => {
                let tail = Self::cat_all(rest)?;
                Self::cat_w(first.clone(), tail)
            }
        }
    }

    /// The binary rule set for this env: one clause per production, in order.
    pub fn rule_set(&self) -> RuleSet2<'_> {
        RuleSet2::new(Type::nat(), Self::word_ty(), move |d_apply| {
            let alpha = crate::init::regex::u8_alphabet();
            let mut clauses = Vec::with_capacity(self.prods.len());
            for (lhs, segs) in &self.prods {
                // Fresh word variable per segment.
                let wvars: Vec<Term> = (0..segs.len())
                    .map(|j| Term::free(&format!("w{j}"), Self::word_ty()))
                    .collect();
                // Antecedents, left to right.
                let mut ants = Vec::with_capacity(segs.len());
                for (seg, w) in segs.iter().zip(&wvars) {
                    let ant = match seg {
                        RSeg::Term(core) => crate::init::regex::matches(&alpha, core.term(), w)?,
                        RSeg::NonTerm(id) => d_apply(&self.tag(*id), w)?,
                    };
                    ants.push(ant);
                }
                // Conclusion `d ⌜lhs⌝ (cat …)`.
                let concl_word = Self::cat_all(&wvars)?;
                let mut body = d_apply(&self.tag(*lhs), &concl_word)?;
                // Chain antecedents right-to-left so σ₁ is outermost.
                for ant in ants.into_iter().rev() {
                    body = ant.imp(body)?;
                }
                // ∀-close word vars, innermost bound first so w0 is outermost.
                for (j, _) in wvars.iter().enumerate().rev() {
                    body = body.forall(&format!("w{j}"), Self::word_ty())?;
                }
                clauses.push(body);
            }
            Ok(clauses)
        })
    }

    /// `Derives_E n w` for a non-terminal tag `n` and word `w`.
    pub fn derivable(&self, nt: NtId, word: &Term) -> Result<Term> {
        derivable2(&self.rule_set(), &self.tag(nt), word)
    }

    /// Apply production `clause_idx` with the given word arguments and premises
    /// (one per segment, in order: [`Premise::Side`] for a terminal `Matches`
    /// theorem, [`Premise::Derivation`] for a non-terminal sub-derivation),
    /// yielding `⊢ Derives_E ⌜lhs⌝ (cat …)`.
    pub fn derive(
        &self,
        clause_idx: usize,
        word_args: &[Term],
        premises: Vec<Premise>,
    ) -> Result<Thm> {
        derive_mixed(
            &self.rule_set(),
            clause_idx,
            self.n_clauses(),
            word_args,
            premises,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use covalence_grammar::regex::Regex;

    /// `S → a S b | ε` — the classic non-regular `aⁿbⁿ` language.
    fn anbn() -> (Cfg<u8>, NtId) {
        let mut cfg = Cfg::new();
        let s = cfg.add_nt("S");
        // production 0: S → a S b
        cfg.add_prod(
            s,
            vec![
                Seg::term(Regex::Lit(b'a')),
                Seg::nt(s),
                Seg::term(Regex::Lit(b'b')),
            ],
        );
        // production 1: S → ε
        cfg.add_prod(s, vec![]);
        (cfg, s)
    }

    #[test]
    fn env_clause_count_matches_productions() {
        let (cfg, _) = anbn();
        let env = GrammarEnv::new(cfg).unwrap();
        assert_eq!(env.n_clauses(), 2);
        assert_eq!(env.rule_set().n_clauses().unwrap(), 2);
    }

    /// `cons b nil : list u8` — the rule-shaped word a single-byte literal
    /// match produces (matching the regex tactic's `singleton_w`).
    fn singleton(b: u8) -> Term {
        crate::init::list::cons(crate::init::regex::u8_alphabet())
            .apply(covalence_hol_eval::mk_u8(b))
            .unwrap()
            .apply(GrammarEnv::nil_w())
            .unwrap()
    }

    /// Hand-drive `⊢ Derives_E ⌜S⌝ ⌜aabb⌝` by three clause applications, with
    /// each terminal leaf discharged by a `Matches` theorem from the existing
    /// regex tactic. This is the M1 end-to-end smoke test for the engine +
    /// env; the [`tactic`] module automates the search.
    #[test]
    fn derive_aabb_by_hand() {
        use crate::grammar::regex::tactic::prove_matches;

        let (cfg, s) = anbn();
        let env = GrammarEnv::new(cfg).unwrap();

        // Leaf `Matches` theorems for the single-byte literals 'a' and 'b'.
        let ma = prove_matches(&Regex::Lit(b'a'), b"a").unwrap().unwrap();
        let mb = prove_matches(&Regex::Lit(b'b'), b"b").unwrap().unwrap();
        let wa = singleton(b'a');
        let wb = singleton(b'b');
        let nil = GrammarEnv::nil_w();

        // Innermost: S → ε  (clause 1), word = nil.
        let inner = env.derive(1, &[], vec![]).unwrap();
        assert!(inner.hyps().is_empty());
        let inner_word = nil.clone();

        // S → a S b  (clause 0): word args [wa, inner_word, wb], premises
        // [Side(ma), Derivation(inner), Side(mb)]. Conclusion word `cat wa
        // (cat inner_word wb)`.
        let mid_word = GrammarEnv::cat_w(
            wa.clone(),
            GrammarEnv::cat_w(inner_word, wb.clone()).unwrap(),
        )
        .unwrap();
        let mid = env
            .derive(
                0,
                &[wa.clone(), nil.clone(), wb.clone()],
                vec![
                    Premise::Side(ma.clone()),
                    Premise::Derivation(inner),
                    Premise::Side(mb.clone()),
                ],
            )
            .unwrap();
        assert!(mid.hyps().is_empty());
        assert_eq!(mid.concl(), &env.derivable(s, &mid_word).unwrap());

        // Outer: S → a S b again, wrapping the middle S — `a (a b) b`.
        let outer = env
            .derive(
                0,
                &[wa.clone(), mid_word.clone(), wb.clone()],
                vec![
                    Premise::Side(ma),
                    Premise::Derivation(mid),
                    Premise::Side(mb),
                ],
            )
            .unwrap();
        assert!(outer.hyps().is_empty());

        let outer_word = GrammarEnv::cat_w(wa, GrammarEnv::cat_w(mid_word, wb).unwrap()).unwrap();
        assert_eq!(outer.concl(), &env.derivable(s, &outer_word).unwrap());
    }
}
