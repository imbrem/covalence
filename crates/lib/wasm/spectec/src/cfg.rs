//! Lower SpecTec grammars ([`Grammar`]) into the neutral
//! [`covalence_grammar::cfg::Cfg<u8>`] IR — the CFG stratum's frontend
//! (design: `notes/vibes/logics/cfg-stratum-design.md` §4).
//!
//! [`lower`] takes a slice of [`Grammar`]s and a set of root grammar names,
//! computes the dependency closure reachable from the roots through
//! non-terminal ([`Var`](spectec_ast::SpecTecSym::Var)) references, and emits
//! one `Cfg<u8>` whose non-terminals are those grammars and whose productions
//! are the lowered SpecTec productions. A [`CfgReport`] records exactly what
//! was lowered, what was skipped (bucketed by reason), and a per-grammar
//! full / partial / none classification.
//!
//! # Soundness direction (the load-bearing invariant)
//!
//! **Lowering under-approximates**: `L(lowered Cfg) ⊆ L(SpecTec grammar)`.
//! Every transformation here either preserves the language exactly
//! (attr-capture stripping, `Alt`-distribution, `Iter` desugaring, resolving a
//! param-independent parametric reference) or *drops* whole productions
//! (premise-carrying, `ListN`, param-dependent parametric refs) — it never
//! *adds* words. Consequently a downstream `⊢ Derives_E n w` theorem, proved
//! against the lowered `Cfg`, implies membership of `w` in the true SpecTec
//! language. The kernel re-checks every construction; a lowering bug can only
//! shrink coverage, never mint an unsound membership proof.
//!
//! # What is skipped (per-production granularity)
//!
//! A single production is skipped — never the whole grammar — when it carries
//! any of:
//!
//! - **premises** (`prs ≠ ∅`): a side condition beyond a CFG
//!   ([`SkipReason::Premise`]);
//! - a **parameter-dependent parametric reference** `Var{x, as1}` with
//!   `as1 ≠ ∅` whose target grammar's language actually depends on its
//!   parameters ([`SkipReason::ParametricRef`]) — monomorphisation is a later
//!   milestone. A `Var{x, as1}` whose target is *param-independent* (its body
//!   ignores its parameters, e.g. `Bvar = 0x00`) is resolved by ignoring the
//!   args, which is language-preserving;
//! - a **`ListN`** iteration or an **iteration with `dom` bindings**
//!   ([`SkipReason::ListN`] / [`SkipReason::IterWithDom`]) — context-sensitive
//!   length iteration is beyond CFG;
//! - a **terminal fragment outside the byte-regex subset**
//!   ([`SkipReason::Bridge`]) — surfaced verbatim from
//!   [`sym_to_regex_u8`](crate::regex::sym_to_regex_u8).
//!
//! A non-terminal is retained even when all of its productions are skipped; it
//! is then flagged *dead* in the report.
//!
//! # Recognition mode (opt-in, [`lower_recognition`] / [`LowerMode::Recognition`])
//!
//! [`lower`] above is [`LowerMode::Under`] and never changes. In addition,
//! [`lower_recognition`] runs the *recognition* mode of the design's M6
//! milestone (`notes/vibes/logics/cfg-stratum-design.md` §"M6 — Missing
//! grammars"). Its per-production transformations **over-approximate**, flipping
//! the invariant to `L(SpecTec grammar) ⊆ L(recognition Cfg)`: the emitted `Cfg`
//! is a *recognizer* whose rejection is sound — a `⊢ ¬Derives_E n w` (a byte
//! string the recognition `Cfg` rejects) proves the bytes are not a well-formed
//! encoding, but membership means only "well-formed *recognition*", not "encodes
//! an in-range value". This is the reverse direction from [`lower`]'s membership
//! witness, so it is a deliberate, separately-reported opt-in.
//!
//! **Caveat — the over-approximation is per-grammar, gated on `Full` coverage.**
//! Recognition mode still *drops* productions it cannot lower (unclassifiable
//! premise, monomorphisation depth cap, grammar-valued parametric param), and a
//! dropped production removes spec-accepted strings — an *under*-approximation.
//! So `L(SpecTec grammar) ⊆ L(recognition Cfg)` holds cleanly only for a grammar
//! the report classifies [`Coverage::Full`] (every production lowered — e.g.
//! `Bu32`, the `*idx` family, the LEB128 chain). A [`Coverage::Partial`] grammar
//! mixes both directions (some productions over-approximated, some dropped), so
//! neither containment holds for it; consult the report's per-grammar coverage
//! before reading a `Derives_E` theorem as a recognizer. The kernel theorem
//! itself is always exact: `⊢ Derives_E ⌜nt⌝ w` means precisely `w ∈ L(lowered
//! Cfg)` regardless of coverage.
//!
//! Recognition mode unlocks the parametric / LEB128 grammars [`lower`] skips:
//!
//! - **LEB128** (`BuN`/`BsN`, and their wrappers `Bu32`/`Bu64`/`Bs33`/`BiN` and
//!   every `*idx`) lower to a *single* byte-count-bounded regex terminal
//!   ([`leb128_regex`]) rather than unrolling the self-recursive byte
//!   productions — cheaper and exact on byte shape.
//! - **Monomorphisation**: a parametric reference `Var{x, as1}` whose arguments
//!   const-fold to ground values is instantiated into a deduped per-instance
//!   non-terminal (e.g. `"BuN@32"`), lowering `x`'s productions under the pushed
//!   parameter binding. `BfN(N)` becomes `N/8` literal full-range byte segments.
//! - **Premise classification** replaces the blanket premise-skip: a premise
//!   over grammar params only is *evaluated* against the instance binding
//!   (dropping the production when false — exact, this is what bounds the `BuN`
//!   recursion); a premise over captured production-local values is dropped
//!   (over-approximate, counted [`CfgReport::premises_dropped`]); anything not
//!   cleanly classifiable is skipped — which *under*-approximates that
//!   production (see the coverage caveat above).
//! - **`ListN`** widens to a Kleene star (`WASM` vectors may be empty), counted
//!   [`CfgReport::listns_widened`].
//!
//! Both modes are total (never panic on any input) and both keep the corpus
//! left-recursion-free.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use covalence_grammar::cfg::{Cfg, NtId, Seg};
use covalence_grammar::regex::{Class, ClassRange, Regex};
use spectec_ast::{
    SpecTecArg, SpecTecBinOp, SpecTecCmpOp, SpecTecExp, SpecTecIter, SpecTecNum, SpecTecParam,
    SpecTecProd, SpecTecSym, SpecTecUnOp,
};

use crate::grammar::Grammar;
use crate::regex::{BridgeError, sym_to_regex_u8};

/// Why a single SpecTec production could not be lowered into the CFG IR.
///
/// Each variant maps to a report bucket ([`CfgReport::skipped`]).
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum CfgLowerError {
    /// The production carries premises (`prs ≠ ∅`) — a side condition beyond
    /// a context-free grammar.
    #[error("production of `{grammar}` carries {count} premise(s) (not context-free)")]
    Premise { grammar: String, count: usize },

    /// A `Var{x, as1}` reference with arguments whose target grammar's
    /// language depends on its parameters. Monomorphisation is a later
    /// milestone (M6).
    #[error("parametric reference `{name}` with {args} argument(s) needs monomorphisation")]
    ParametricRef { name: String, args: usize },

    /// A `ListN` (parametric length) iteration — context-sensitive.
    #[error("`listn` (parametric length iteration) in `{grammar}` is not context-free")]
    ListN { grammar: String },

    /// An iteration carrying `dom` bindings, which bind names in the
    /// surrounding rule — not a CFG feature.
    #[error("iteration with `dom` bindings in `{grammar}` is not context-free")]
    IterWithDom { grammar: String },

    /// A terminal fragment fell outside the byte-regex subset. Wraps the
    /// underlying [`BridgeError`].
    #[error("terminal fragment of `{grammar}` is not a byte regex: {source}")]
    Bridge {
        grammar: String,
        #[source]
        source: BridgeError,
    },
}

/// Coarse skip bucket for [`CfgReport`], independent of the message payload.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum SkipReason {
    Premise,
    ParametricRef,
    ListN,
    IterWithDom,
    Bridge,
}

/// One skipped source production and its exact lowering refusal.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SkippedProduction {
    /// Source grammar containing the production.
    pub grammar: String,
    /// Zero-based production index within that grammar.
    pub production: usize,
    /// Typed reason the production could not be lowered.
    pub error: CfgLowerError,
}

impl SkipReason {
    fn of(err: &CfgLowerError) -> Self {
        match err {
            CfgLowerError::Premise { .. } => SkipReason::Premise,
            CfgLowerError::ParametricRef { .. } => SkipReason::ParametricRef,
            CfgLowerError::ListN { .. } => SkipReason::ListN,
            CfgLowerError::IterWithDom { .. } => SkipReason::IterWithDom,
            CfgLowerError::Bridge { .. } => SkipReason::Bridge,
        }
    }

    fn label(self) -> &'static str {
        match self {
            SkipReason::Premise => "premise",
            SkipReason::ParametricRef => "parametric-ref",
            SkipReason::ListN => "listn",
            SkipReason::IterWithDom => "iter-with-dom",
            SkipReason::Bridge => "bridge",
        }
    }
}

/// Which direction the lowering approximates in.
///
/// [`Under`](LowerMode::Under) is the default [`lower`] behaviour —
/// `L(Cfg) ⊆ L(SpecTec)`, a membership witness. [`Recognition`](LowerMode::Recognition)
/// is the opt-in M6 mode — `L(SpecTec) ⊆ L(Cfg)` per `Full`-coverage grammar, a
/// sound recognizer (see the module docs' coverage caveat; `Partial` grammars
/// mix both directions). The two share all machinery except the recognition-only
/// hooks (LEB128 special-case, monomorphisation, premise classification, `ListN`
/// widening), which are no-ops under `Under`.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LowerMode {
    /// Under-approximate: only lower what is exactly language-preserving.
    Under,
    /// Over-approximate: build a sound recognizer, unlocking parametric /
    /// premise-carrying / `ListN` grammars.
    Recognition,
}

/// An explicitly selected grammar root.
///
/// Parameterised grammars must use [`Instance`](Self::Instance): treating a
/// generic grammar name as an ordinary CFG non-terminal would erase the
/// parameters from the derivability judgement.
#[derive(Debug, Clone, PartialEq)]
pub enum GrammarRoot {
    /// A non-parameterised grammar.
    Plain(String),
    /// A grammar specialised at canonical, ground SpecTec arguments.
    Instance { name: String, args: Vec<SpecTecArg> },
}

/// Why an explicit grammar root could not be represented faithfully.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum GrammarRootError {
    #[error("unknown grammar root `{name}`")]
    Unknown { name: String },
    #[error("parameterised grammar root `{name}` requires an explicit instance")]
    ParametersRequired { name: String },
    #[error("grammar root `{name}` is not parameterised")]
    UnexpectedInstance { name: String },
    #[error("grammar root `{name}` expects {expected} argument(s), got {actual}")]
    Arity {
        name: String,
        expected: usize,
        actual: usize,
    },
    #[error("argument {index} of grammar root `{name}` is not ground or has the wrong kind")]
    UngroundArgument { name: String, index: usize },
}

impl LowerMode {
    fn is_recognition(self) -> bool {
        matches!(self, LowerMode::Recognition)
    }
}

/// Coverage classification of one grammar in the lowered closure.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Coverage {
    /// Every production lowered.
    Full,
    /// Some productions lowered, some skipped.
    Partial,
    /// No production lowered (the non-terminal is *dead* in the `Cfg`).
    None,
}

impl Coverage {
    fn label(self) -> &'static str {
        match self {
            Coverage::Full => "full",
            Coverage::Partial => "partial",
            Coverage::None => "none",
        }
    }
}

/// A structured, ratchet-friendly account of a [`lower`] run.
///
/// The counts and per-grammar map are the surface the coverage tests pin
/// against; nothing here affects the emitted `Cfg`.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct CfgReport {
    /// Number of SpecTec productions successfully lowered (each may expand
    /// into several `Cfg` productions via `Alt`-distribution).
    pub lowered_prods: usize,
    /// Number of SpecTec productions skipped, bucketed by reason.
    pub skipped: BTreeMap<SkipReason, usize>,
    /// Per-production lowering errors, in source traversal order.
    ///
    /// This is the lossless companion to [`Self::skipped`]: consumers can
    /// audit exactly which grammar/form remains outside a lowering mode
    /// without scraping display strings or reimplementing the lowering walk.
    pub skipped_details: Vec<SkippedProduction>,
    /// Attr captures stripped silently (fresh-variable / value captures —
    /// language-preserving).
    pub attrs_captured: usize,
    /// Attr constraints stripped as an approximation (reference enclosing
    /// parameters). Expected to be zero in v1 (they occur only inside
    /// parametric grammars, whose param-dependent productions are skipped).
    pub attrs_constrained: usize,
    /// Synthetic non-terminals created for `Iter` desugaring.
    pub synthetic_nts: usize,
    /// Per-grammar coverage classification, keyed by grammar name.
    pub grammars: BTreeMap<String, Coverage>,

    // --- recognition-mode counters (always zero under [`LowerMode::Under`]) ---
    /// Input-value premises dropped as an over-approximation (recognition mode).
    /// Each accepts encodings the true grammar's side condition would reject
    /// (e.g. over-long / out-of-range LEB128 values). Param-only premises that
    /// are *evaluated* (and drop a production exactly when false) are not
    /// counted here.
    pub premises_dropped: usize,
    /// `ListN` (and `dom`-carrying) iterations widened to a Kleene star
    /// (recognition mode) — over-approximate, WASM vectors may be any length.
    pub listns_widened: usize,
    /// Distinct monomorphised parametric instances created (recognition mode),
    /// e.g. `BuN@32`, `BsN@33`, `Bsection_@1,type,…`. Deduped by
    /// (name, ground args) where a ground arg is an integer, a resolved
    /// grammar-argument non-terminal, or a rendered type argument.
    pub mono_instances: usize,
    /// Parameter-equality attrs over `Bbyte` constant-folded into a literal
    /// byte terminal (recognition mode) — **exact**: the SpecTec capture
    /// `[N]:Bbyte` with `N` ground constrains the byte to equal `N`, and the
    /// fold realises exactly that constraint (e.g. `Bsection_`'s section-id
    /// byte). Folded attrs are *not* also counted in `attrs_captured`.
    pub attrs_folded: usize,
}

impl CfgReport {
    fn note_skip(&mut self, grammar: &str, production: usize, err: &CfgLowerError) {
        *self.skipped.entry(SkipReason::of(err)).or_default() += 1;
        self.skipped_details.push(SkippedProduction {
            grammar: grammar.to_string(),
            production,
            error: err.clone(),
        });
    }

    /// Total productions skipped across all reasons.
    pub fn skipped_total(&self) -> usize {
        self.skipped.values().sum()
    }

    /// Grammars whose every production lowered.
    pub fn full_grammars(&self) -> impl Iterator<Item = &str> {
        self.grammars
            .iter()
            .filter(|(_, c)| **c == Coverage::Full)
            .map(|(n, _)| n.as_str())
    }

    /// Grammars in the given coverage class.
    pub fn grammars_with(&self, cov: Coverage) -> impl Iterator<Item = &str> {
        self.grammars
            .iter()
            .filter(move |(_, c)| **c == cov)
            .map(|(n, _)| n.as_str())
    }

    /// Coverage class of the *source grammar* behind a `Cfg` non-terminal name.
    ///
    /// Whole-grammar non-terminals carry the grammar's own name; synthetic
    /// iteration non-terminals are `{grammar}${kind}{n}` and monomorphised
    /// instances `{grammar}@{args}`, so both attribute to their source grammar
    /// by truncating at the first `$` / `@`. Conservative for instances: e.g.
    /// `BuN@32` reports the coverage of the *generic* `BuN` (typically worse
    /// than what the LEB128-instantiated NT actually achieves), never better.
    /// `None` for names outside the lowered closure.
    pub fn coverage_of_nt(&self, nt_name: &str) -> Option<Coverage> {
        let base = nt_name.split(['$', '@']).next().unwrap_or(nt_name);
        self.grammars.get(base).copied()
    }
}

impl std::fmt::Display for CfgReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "CFG lowering: {} grammars, {} productions lowered, {} skipped",
            self.grammars.len(),
            self.lowered_prods,
            self.skipped_total(),
        )?;
        writeln!(
            f,
            "  attrs: {} captures stripped, {} constraints approximated; {} synthetic NTs",
            self.attrs_captured, self.attrs_constrained, self.synthetic_nts,
        )?;
        // Recognition-mode line — only emitted when a recognition counter fired,
        // so under-approximating (`lower`) reports render byte-identically.
        if self.premises_dropped != 0
            || self.listns_widened != 0
            || self.mono_instances != 0
            || self.attrs_folded != 0
        {
            writeln!(
                f,
                "  recognition: {} mono instances, {} premises dropped, {} listns widened, {} attrs folded",
                self.mono_instances, self.premises_dropped, self.listns_widened, self.attrs_folded,
            )?;
        }
        if !self.skipped.is_empty() {
            write!(f, "  skipped by reason:")?;
            for (reason, n) in &self.skipped {
                write!(f, " {}={}", reason.label(), n)?;
            }
            writeln!(f)?;
        }
        let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
        for c in self.grammars.values() {
            *counts.entry(c.label()).or_default() += 1;
        }
        write!(f, "  coverage:")?;
        for (label, n) in &counts {
            write!(f, " {label}={n}")?;
        }
        writeln!(f)
    }
}

// ============================================================================
// Param-independence analysis
// ============================================================================

/// Whether grammar `g`'s language ignores its parameters. A `Var{x, as1}`
/// reference to such a grammar can be resolved by discarding `as1` — a
/// language-preserving move — even though `x` is nominally parametric.
///
/// Conservative: a grammar is param-independent iff it *has* parameters (a
/// non-parametric grammar is trivially so) and **no symbol anywhere in its
/// productions mentions a parameter name** — neither a `Var{x}` referencing a
/// parameter nor an [`SpecTecArg::Exp`]/`Gram` payload that does. Non-obvious
/// cases (a production body that consults a parameter) are conservatively
/// *not* param-independent, so a reference to them is skipped rather than
/// unsoundly resolved.
fn param_independent(g: &Grammar) -> bool {
    if g.params.is_empty() {
        return true;
    }
    let names: BTreeSet<&str> = g.params.iter().filter_map(param_name).collect();
    if names.is_empty() {
        return true;
    }
    g.prods.iter().all(|p| {
        let SpecTecProd::Prod { g: sym, prs, .. } = p;
        // A production is param-independent only if neither its symbol nor any
        // of its premises consult a parameter — a param-guard premise makes the
        // language genuinely depend on the parameter.
        !sym_mentions_names(sym, &names) && !prs.iter().any(|pr| prem_mentions_names(pr, &names))
    })
}

/// Does a premise mention one of `names`? Only `if e` / `let` premises carry
/// expressions we inspect; other shapes conservatively count as mentioning
/// (so a grammar with an opaque premise is treated as param-dependent).
fn prem_mentions_names(pr: &spectec_ast::SpecTecPrem, names: &BTreeSet<&str>) -> bool {
    match pr {
        spectec_ast::SpecTecPrem::If { e } => exp_mentions_names(e, names),
        spectec_ast::SpecTecPrem::Let { e1, e2 } => {
            exp_mentions_names(e1, names) || exp_mentions_names(e2, names)
        }
        spectec_ast::SpecTecPrem::Rule { .. }
        | spectec_ast::SpecTecPrem::Else
        | spectec_ast::SpecTecPrem::Iter { .. } => true,
    }
}

fn param_name(p: &spectec_ast::SpecTecParam) -> Option<&str> {
    use spectec_ast::SpecTecParam::*;
    match p {
        Exp { x, .. } | Typ { x } | Def { x, .. } | Gram { x, .. } => Some(x.as_str()),
    }
}

/// Does any symbol under `sym` mention one of `names` (as a `Var` head or in
/// an argument expression)?
fn sym_mentions_names(sym: &SpecTecSym, names: &BTreeSet<&str>) -> bool {
    match sym {
        SpecTecSym::Var { x, as1 } => {
            names.contains(x.as_str()) || as1.iter().any(|a| arg_mentions_names(a, names))
        }
        SpecTecSym::Num { .. } | SpecTecSym::Text { .. } | SpecTecSym::Eps => false,
        SpecTecSym::Seq { gs } | SpecTecSym::Alt { gs } => {
            gs.iter().any(|g| sym_mentions_names(g, names))
        }
        SpecTecSym::Range { g1, g2 } => {
            sym_mentions_names(g1, names) || sym_mentions_names(g2, names)
        }
        SpecTecSym::Iter { g1, .. } => sym_mentions_names(g1, names),
        SpecTecSym::Attr { e, g1 } => exp_mentions_names(e, names) || sym_mentions_names(g1, names),
    }
}

fn arg_mentions_names(a: &SpecTecArg, names: &BTreeSet<&str>) -> bool {
    match a {
        SpecTecArg::Exp { e } => exp_mentions_names(e, names),
        SpecTecArg::Gram { g } => sym_mentions_names(g, names),
        SpecTecArg::Def { x } => names.contains(x.as_str()),
        SpecTecArg::Typ { .. } => false,
    }
}

/// Conservative free-name check over expressions: `true` if `e` *might*
/// mention one of `names`. Only the leaf `Var`/`Call` cases can introduce a
/// name; everything else recurses. Unknown-but-name-free constants are safe.
fn exp_mentions_names(e: &SpecTecExp, names: &BTreeSet<&str>) -> bool {
    use SpecTecExp::*;
    match e {
        Var { id } => names.contains(id.as_str()),
        Call { x, as1 } => {
            names.contains(x.as_str()) || as1.iter().any(|a| arg_mentions_names(a, names))
        }
        Bool { .. } | Num { .. } | Text { .. } => false,
        Un { e2, .. } => exp_mentions_names(e2, names),
        Bin { e1, e2, .. }
        | Cmp { e1, e2, .. }
        | Idx { e1, e2, .. }
        | Comp { e1, e2, .. }
        | Mem { e1, e2, .. }
        | Cat { e1, e2, .. } => exp_mentions_names(e1, names) || exp_mentions_names(e2, names),
        Slice { e1, e2, e3, .. } => {
            exp_mentions_names(e1, names)
                || exp_mentions_names(e2, names)
                || exp_mentions_names(e3, names)
        }
        Upd { e1, e2, .. } | Ext { e1, e2, .. } => {
            exp_mentions_names(e1, names) || exp_mentions_names(e2, names)
        }
        Str { efs } => efs.iter().any(|ef| {
            let spectec_ast::SpecTecExpField::Field { e, .. } = ef;
            exp_mentions_names(e, names)
        }),
        Dot { e1, .. }
        | Len { e1 }
        | Iter { e1, .. }
        | Proj { e1, .. }
        | Case { e1, .. }
        | Uncase { e1, .. }
        | Unopt { e1 }
        | Lift { e1 }
        | Cvt { e1, .. }
        | Sub { e1, .. } => exp_mentions_names(e1, names),
        Tup { es } | List { es } => es.iter().any(|e| exp_mentions_names(e, names)),
        Opt { eo } => eo.as_ref().is_some_and(|e| exp_mentions_names(e, names)),
    }
}

// ============================================================================
// Attr classification
// ============================================================================

/// Whether an Attr's captured expression is a plain *value capture* (fresh
/// variable / constructor / tuple / list-comprehension — building a value)
/// rather than a *constraint* (a comparison or boolean relation that
/// restricts the language). Only constraints over-approximate when stripped.
///
/// In the WASM `B*` corpus every Attr is a value capture; this check exists so
/// the report can honestly flag the (currently empty) constraint case.
fn attr_is_constraint(e: &SpecTecExp) -> bool {
    matches!(
        e,
        SpecTecExp::Cmp { .. }
            | SpecTecExp::Bool { .. }
            | SpecTecExp::Mem { .. }
            | SpecTecExp::Bin { .. }
    )
}

/// Is `sym` a bare (argument-free) reference to the corpus's full-range byte
/// grammar `Bbyte`? Target check of the recognition-mode parameter-equality
/// attr fold: `[e]:Bbyte` with `e` ground constrains the parsed byte to equal
/// `e`, so the segment folds to the literal byte — exact because `Bbyte`'s
/// value is the byte itself. Name-keyed like the `BuN`/`BsN`/`BfN`
/// special-cases (corpus-specific, driver-side only).
fn is_bare_bbyte(sym: &SpecTecSym) -> bool {
    matches!(sym, SpecTecSym::Var { x, as1 } if x == "Bbyte" && as1.is_empty())
}

/// Const-fold an attr *capture expression* to a ground integer, unwrapping the
/// constructor layers the corpus puts around byte values: `Case{op, Tup[e]}`
/// (the byte/`u32` case wrapper) and single-element `Tup`s, then [`fold_exp`].
fn fold_attr_exp(env: &ParamEnv, e: &SpecTecExp) -> Option<i64> {
    match e {
        SpecTecExp::Case { e1, .. } => fold_attr_exp(env, e1),
        SpecTecExp::Tup { es } if es.len() == 1 => fold_attr_exp(env, &es[0]),
        _ => fold_exp(env, e),
    }
}

// ============================================================================
// Recognition mode: constant folding, predicate evaluation, LEB128 regex
// ============================================================================

/// A parameter binding environment: grammar-parameter name → ground integer
/// value. Threaded through recognition-mode lowering so [`fold_exp`] and
/// [`eval_pred`] can resolve `Var{id}` / `Call` references to instance values.
type ParamEnv = BTreeMap<String, i64>;

/// The full per-instance binding threaded through lowering: `Exp` params bound
/// to ground integers (the [`ParamEnv`] fragment [`fold_exp`]/[`eval_pred`]
/// consume) plus **grammar-valued** params (`Blist`/`Bsection_`'s `BX`) bound
/// to their resolved non-terminals. Empty at the top level and under
/// [`LowerMode::Under`]; populated by [`instantiate`].
#[derive(Debug, Clone, Default)]
struct Binding {
    /// `Exp`-param name → ground integer value.
    ints: ParamEnv,
    /// `Gram`-param name → resolved (possibly itself monomorphised)
    /// non-terminal.
    grams: BTreeMap<String, NtId>,
}

/// One ground argument of a monomorphisation key. Two references instantiate
/// the same non-terminal iff their target name and *entire* argument vectors
/// agree — including type arguments, which never affect the byte language
/// (they only appear in stripped captures / dropped value premises) but are
/// kept in the key conservatively so distinct call shapes stay distinct.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum InstArg {
    /// A const-folded integer `Exp` argument.
    Int(i64),
    /// A grammar-valued argument, resolved to a non-terminal of the `Cfg`
    /// under construction (a plain grammar NT or a nested instance NT).
    Gram(NtId),
    /// A type argument, canonically rendered by [`render_typ`].
    Typ(String),
}

/// Constant-fold an expression to a ground integer under `env`, over the
/// fragment the WASM binary grammars use for parameter arithmetic:
/// numeric literals, `+ - * ^` (and `/` as integer division), the numeric
/// `Cvt` (which is the identity on the *value*, only changing the SpecTec
/// number type), and `Var`/`Call`-of-a-param name looked up in `env`.
///
/// Returns `None` for anything outside that fragment (a non-param `Var`, a
/// missing binding, a non-integer op, or arithmetic that would overflow or
/// divide by zero) — the caller then conservatively skips, preserving totality
/// and soundness.
fn fold_exp(env: &ParamEnv, e: &SpecTecExp) -> Option<i64> {
    use SpecTecExp::*;
    match e {
        Num { n } => num_to_i64(n),
        Var { id } => env.get(id.as_str()).copied(),
        // A nullary call to a bound name behaves like a variable reference; a
        // call with arguments is outside the const-fold fragment.
        Call { x, as1 } if as1.is_empty() => env.get(x.as_str()).copied(),
        // `Cvt` between numeric types is value-preserving here (Nat↔Int↔Rat on
        // whole numbers) — fold the inner expression, keep the value.
        Cvt { e1, .. } => fold_exp(env, e1),
        Un {
            op: SpecTecUnOp::Minus,
            e2,
            ..
        } => fold_exp(env, e2)?.checked_neg(),
        Un {
            op: SpecTecUnOp::Plus,
            e2,
            ..
        } => fold_exp(env, e2),
        Bin { op, e1, e2, .. } => {
            let a = fold_exp(env, e1)?;
            let b = fold_exp(env, e2)?;
            match op {
                SpecTecBinOp::Add => a.checked_add(b),
                SpecTecBinOp::Sub => a.checked_sub(b),
                SpecTecBinOp::Mul => a.checked_mul(b),
                SpecTecBinOp::Div if b != 0 => Some(a.div_euclid(b)),
                SpecTecBinOp::Mod if b != 0 => Some(a.rem_euclid(b)),
                SpecTecBinOp::Pow if b >= 0 && b <= u32::MAX as i64 => a.checked_pow(b as u32),
                _ => None,
            }
        }
        _ => None,
    }
}

fn num_to_i64(n: &SpecTecNum) -> Option<i64> {
    match n {
        SpecTecNum::Nat(v) => i64::try_from(*v).ok(),
        SpecTecNum::Int(v) => Some(*v),
        SpecTecNum::Rat(_) | SpecTecNum::Real(_) => None,
    }
}

/// Evaluate a boolean *predicate* over `env`, returning `Some(true/false)` when
/// every leaf const-folds and `None` otherwise. Covers the comparison /
/// boolean-connective fragment the `B*` premises use (`< > ≤ ≥ = ≠`, `∧ ∨ ⟹`).
///
/// Used by premise classification: a *param-only* premise (`exp_mentions_names`
/// against non-param names is empty) is evaluated here; `Some(false)` drops the
/// production exactly, `Some(true)`/absent keeps it, `None` is treated
/// conservatively (skip).
fn eval_pred(env: &ParamEnv, e: &SpecTecExp) -> Option<bool> {
    use SpecTecExp::*;
    match e {
        Bool { b } => Some(*b),
        Cmp { op, e1, e2, .. } => {
            let a = fold_exp(env, e1)?;
            let b = fold_exp(env, e2)?;
            Some(match op {
                SpecTecCmpOp::Eq => a == b,
                SpecTecCmpOp::Ne => a != b,
                SpecTecCmpOp::Lt => a < b,
                SpecTecCmpOp::Gt => a > b,
                SpecTecCmpOp::Le => a <= b,
                SpecTecCmpOp::Ge => a >= b,
            })
        }
        Bin { op, e1, e2, .. } => {
            let a = eval_pred(env, e1)?;
            let b = eval_pred(env, e2)?;
            match op {
                SpecTecBinOp::And => Some(a && b),
                SpecTecBinOp::Or => Some(a || b),
                SpecTecBinOp::Impl => Some(!a || b),
                SpecTecBinOp::Equiv => Some(a == b),
                _ => None,
            }
        }
        Un {
            op: SpecTecUnOp::Not,
            e2,
            ..
        } => Some(!eval_pred(env, e2)?),
        _ => None,
    }
}

/// The byte-count-bounded unsigned-LEB128 byte-shape regex for an `N`-bit value:
/// up to `ceil(N/7) − 1` continuation bytes `[\x80-\xFF]` followed by exactly
/// one terminator byte `[\x00-\x7F]`. This over-approximates the true encoding
/// only in the top bits of the final byte (the irreducible recognition-vs-value
/// gap); it is exact on byte count. Built directly as
/// `[\x80-\xFF]{0, k−1} [\x00-\x7F]` with `k = ceil(N/7)`.
///
/// `N ≤ 0` (never produced by the corpus, but kept total) yields a single
/// terminator byte (`k = 1`).
pub fn leb128_regex(n_bits: i64) -> Regex<u8> {
    let bits = n_bits.max(1) as u64;
    let k = bits.div_ceil(7).max(1); // ceil(N/7), at least one byte
    let cont_max = (k - 1).min(u32::MAX as u64) as u32;
    let cont = Regex::Class(Class::new(vec![ClassRange::new(0x80u8, 0xFFu8)]));
    let term = Regex::Class(Class::new(vec![ClassRange::new(0x00u8, 0x7Fu8)]));
    Regex::concat([
        Regex::Rep {
            inner: std::sync::Arc::new(cont),
            min: 0,
            max: Some(cont_max),
        },
        term,
    ])
}

/// One full-range byte `[\x00-\xFF]` — the recognition segment of `Bbyte`.
fn any_byte_regex() -> Regex<u8> {
    Regex::Class(Class::new(vec![ClassRange::new(0x00u8, 0xFFu8)]))
}

// ============================================================================
// Dependency closure
// ============================================================================

/// Collect the non-terminal references in `sym` that would lower to a real
/// `NonTerm` edge: a bare `Var{x}` (empty args) or a `Var{x, as1}` whose
/// target grammar is param-independent (args discarded, sound). Param-dependent
/// parametric references are *not* followed — they will be skipped, so their
/// targets do not belong in the dependency closure.
fn referenced_resolvable(ctx: &Ctx, sym: &SpecTecSym, out: &mut BTreeSet<String>) {
    match sym {
        SpecTecSym::Var { x, as1 } => {
            if ctx.var_resolvable(x, as1) {
                out.insert(x.clone());
            }
        }
        SpecTecSym::Num { .. } | SpecTecSym::Text { .. } | SpecTecSym::Eps => {}
        SpecTecSym::Seq { gs } | SpecTecSym::Alt { gs } => {
            gs.iter().for_each(|g| referenced_resolvable(ctx, g, out))
        }
        SpecTecSym::Range { g1, g2 } => {
            referenced_resolvable(ctx, g1, out);
            referenced_resolvable(ctx, g2, out);
        }
        SpecTecSym::Iter { g1, .. } => referenced_resolvable(ctx, g1, out),
        SpecTecSym::Attr { g1, .. } => referenced_resolvable(ctx, g1, out),
    }
}

/// Recognition-mode closure edge: collect *every* referenced grammar name
/// (bare `Var{x}` or parametric `Var{x, as1}`), regardless of premises or
/// args. Monomorphised instances resolve their body's bare references through
/// the closure `ids`, so all reachable grammar bodies must be present. Args are
/// not followed structurally (they are const-folded, not lowered) but grammar-
/// valued args are followed so `Blist`-style `BX` params resolve.
fn referenced_all(sym: &SpecTecSym, out: &mut BTreeSet<String>) {
    match sym {
        SpecTecSym::Var { x, as1 } => {
            out.insert(x.clone());
            for a in as1 {
                if let SpecTecArg::Gram { g } = a {
                    referenced_all(g, out);
                }
            }
        }
        SpecTecSym::Num { .. } | SpecTecSym::Text { .. } | SpecTecSym::Eps => {}
        SpecTecSym::Seq { gs } | SpecTecSym::Alt { gs } => {
            gs.iter().for_each(|g| referenced_all(g, out))
        }
        SpecTecSym::Range { g1, g2 } => {
            referenced_all(g1, out);
            referenced_all(g2, out);
        }
        SpecTecSym::Iter { g1, .. } => referenced_all(g1, out),
        SpecTecSym::Attr { g1, .. } => referenced_all(g1, out),
    }
}

// ============================================================================
// Lowering context
// ============================================================================

/// Maximum monomorphisation recursion depth. The mono cache already makes
/// instantiation terminate (a repeated `(name, args)` reuses its NT), and the
/// evaluated param-guard premises bound the natural recursions (`BuN(N)` stops
/// at `N ≤ 7`); this is a belt-and-braces cap so a pathological grammar can
/// never make lowering non-total.
const MAX_INST_DEPTH: usize = 64;

struct Ctx<'a> {
    /// All grammars by name.
    by_name: BTreeMap<&'a str, &'a Grammar>,
    /// Cache of param-independence per grammar name.
    param_indep: BTreeMap<&'a str, bool>,
    cfg: Cfg<u8>,
    report: CfgReport,
    /// Fresh-name counter for synthetic non-terminals.
    synth_ctr: usize,
    /// Under- vs recognition-approximation.
    mode: LowerMode,
    /// Deduped monomorphised instances, keyed by (grammar name, ground args —
    /// integers, resolved grammar-arg non-terminals, rendered type args).
    /// Recognition mode only; empty under [`LowerMode::Under`].
    mono: BTreeMap<(String, Vec<InstArg>), NtId>,
    /// Current instantiation recursion depth (guards [`MAX_INST_DEPTH`]).
    inst_depth: usize,
}

impl<'a> Ctx<'a> {
    fn new(grammars: &'a [Grammar], mode: LowerMode) -> Self {
        let by_name: BTreeMap<&str, &Grammar> =
            grammars.iter().map(|g| (g.name.as_str(), g)).collect();
        let param_indep = by_name
            .iter()
            .map(|(n, g)| (*n, param_independent(g)))
            .collect();
        Ctx {
            by_name,
            param_indep,
            cfg: Cfg::new(),
            report: CfgReport::default(),
            synth_ctr: 0,
            mode,
            mono: BTreeMap::new(),
            inst_depth: 0,
        }
    }

    fn is_param_indep(&self, name: &str) -> bool {
        // Unknown grammars are conservatively treated as param-dependent so a
        // reference to a missing grammar is skipped rather than resolved.
        self.param_indep.get(name).copied().unwrap_or(false)
    }

    /// A `Var{x, as1}` is *resolvable as a plain non-terminal* iff its args
    /// are empty, or its target is param-independent (args discarded, sound).
    fn var_resolvable(&self, x: &str, as1: &[SpecTecArg]) -> bool {
        as1.is_empty() || self.is_param_indep(x)
    }

    fn fresh_synth(&mut self, base: &str, suffix: &str) -> NtId {
        self.synth_ctr += 1;
        let name = format!("{base}${suffix}{}", self.synth_ctr);
        self.report.synthetic_nts += 1;
        self.cfg.add_nt(name)
    }
}

/// Lower SpecTec grammars into a neutral [`Cfg<u8>`], dependency-closed from
/// the named `roots`, **under-approximating** (`L(Cfg) ⊆ L(SpecTec)`).
///
/// `grammars` is the universe of available grammar definitions (e.g.
/// [`crate::grammar::wasm3_binary`]); `roots` names the grammars to start
/// from. The result's non-terminals are the roots plus every grammar
/// transitively reachable through resolvable non-terminal references, in
/// discovery order. Unknown root names are ignored (they contribute nothing).
///
/// See the module docs for the under-approximation invariant and the skip
/// rules. This function is total and never panics on any input.
pub fn lower(grammars: &[Grammar], roots: &[&str]) -> (Cfg<u8>, CfgReport) {
    lower_with(grammars, roots, LowerMode::Under)
}

/// Lower SpecTec grammars into a **recognition** `Cfg<u8>`
/// (`L(SpecTec) ⊆ L(Cfg)` — a sound recognizer). Same closure/roots contract as
/// [`lower`], but unlocks the parametric / LEB128 / premise-carrying / `ListN`
/// grammars via monomorphisation, the LEB128 regex special-case, premise
/// classification, and `ListN` widening (see the module docs). Also total.
pub fn lower_recognition(grammars: &[Grammar], roots: &[&str]) -> (Cfg<u8>, CfgReport) {
    lower_with(grammars, roots, LowerMode::Recognition)
}

/// Lower explicitly selected recognition roots without erasing grammar
/// parameters.
///
/// Each instance is introduced through a fresh, non-parameterised wrapper
/// non-terminal whose sole production references the fully ground instance.
/// Existing monomorphisation then bakes the canonical argument vector into the
/// target non-terminal's identity. The returned IDs are the wrappers, in input
/// order. Distinct ground instances therefore cannot alias even when they
/// share a source grammar.
///
/// Generic parameterised roots and non-ground arguments are rejected before
/// lowering. In particular this API deliberately does not pretend that the
/// text grammar's symbolic identifier context `I` is a ground CFG parameter.
pub fn lower_recognition_roots(
    grammars: &[Grammar],
    roots: &[GrammarRoot],
) -> Result<(Cfg<u8>, CfgReport, Vec<NtId>), GrammarRootError> {
    let by_name: BTreeMap<&str, &Grammar> = grammars.iter().map(|g| (g.name.as_str(), g)).collect();
    let mut universe = grammars.to_vec();
    let mut wrapper_names = Vec::with_capacity(roots.len());

    for (root_index, root) in roots.iter().enumerate() {
        let (name, args) = match root {
            GrammarRoot::Plain(name) => {
                let target = by_name
                    .get(name.as_str())
                    .ok_or_else(|| GrammarRootError::Unknown { name: name.clone() })?;
                if !target.params.is_empty() {
                    return Err(GrammarRootError::ParametersRequired { name: name.clone() });
                }
                (name, Vec::new())
            }
            GrammarRoot::Instance { name, args } => {
                let target = by_name
                    .get(name.as_str())
                    .ok_or_else(|| GrammarRootError::Unknown { name: name.clone() })?;
                if target.params.is_empty() {
                    return Err(GrammarRootError::UnexpectedInstance { name: name.clone() });
                }
                if target.params.len() != args.len() {
                    return Err(GrammarRootError::Arity {
                        name: name.clone(),
                        expected: target.params.len(),
                        actual: args.len(),
                    });
                }
                for (index, (param, arg)) in target.params.iter().zip(args).enumerate() {
                    if !ground_arg_matches(param, arg, &by_name) {
                        return Err(GrammarRootError::UngroundArgument {
                            name: name.clone(),
                            index,
                        });
                    }
                }
                (name, args.clone())
            }
        };

        let mut wrapper = format!("$root{root_index}");
        while by_name.contains_key(wrapper.as_str())
            || wrapper_names.iter().any(|existing| existing == &wrapper)
        {
            wrapper.insert(0, '$');
        }
        wrapper_names.push(wrapper.clone());
        universe.push(Grammar {
            name: wrapper,
            params: Vec::new(),
            typ: spectec_ast::SpecTecTyp::Tup { ets: Vec::new() },
            prods: vec![SpecTecProd::Prod {
                ps: Vec::new(),
                g: SpecTecSym::Var {
                    x: name.clone(),
                    as1: args,
                },
                e: SpecTecExp::Bool { b: true },
                prs: Vec::new(),
            }],
        });
    }

    let root_refs: Vec<&str> = wrapper_names.iter().map(String::as_str).collect();
    let (cfg, report) = lower_recognition(&universe, &root_refs);
    let root_ids = wrapper_names
        .iter()
        .map(|name| cfg.lookup(name).expect("fresh root belongs to closure"))
        .collect();
    Ok((cfg, report, root_ids))
}

fn ground_arg_matches(
    param: &SpecTecParam,
    arg: &SpecTecArg,
    grammars: &BTreeMap<&str, &Grammar>,
) -> bool {
    match (param, arg) {
        (SpecTecParam::Exp { .. }, SpecTecArg::Exp { e }) => {
            fold_exp(&ParamEnv::new(), e).is_some()
        }
        (SpecTecParam::Typ { .. }, SpecTecArg::Typ { .. }) => true,
        (SpecTecParam::Gram { .. }, SpecTecArg::Gram { g }) => ground_grammar_arg(g, grammars),
        // Definition-valued grammar arguments do not yet have a canonical
        // instance-key representation.
        (SpecTecParam::Def { .. }, SpecTecArg::Def { .. }) => false,
        _ => false,
    }
}

fn ground_grammar_arg(sym: &SpecTecSym, grammars: &BTreeMap<&str, &Grammar>) -> bool {
    let SpecTecSym::Var { x, as1 } = sym else {
        return false;
    };
    let Some(target) = grammars.get(x.as_str()) else {
        return false;
    };
    target.params.len() == as1.len()
        && target
            .params
            .iter()
            .zip(as1)
            .all(|(param, arg)| ground_arg_matches(param, arg, grammars))
}

/// The shared lowering driver, parameterised by [`LowerMode`].
fn lower_with(grammars: &[Grammar], roots: &[&str], mode: LowerMode) -> (Cfg<u8>, CfgReport) {
    let mut ctx = Ctx::new(grammars, mode);

    // 1. Dependency closure (BFS over resolvable + param-dependent refs, so a
    //    grammar whose *some* productions reference a target is included even
    //    if the reference itself will be skipped).
    let mut order: Vec<&str> = Vec::new();
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut queue: VecDeque<&str> = VecDeque::new();
    for r in roots {
        if let Some((name, _)) = ctx.by_name.get_key_value(*r)
            && seen.insert(name)
        {
            queue.push_back(name);
        }
    }
    while let Some(name) = queue.pop_front() {
        order.push(name);
        let g = ctx.by_name[name];
        let mut refs = BTreeSet::new();
        for p in &g.prods {
            let SpecTecProd::Prod { g: sym, prs, .. } = p;
            if ctx.mode.is_recognition() {
                // Recognition mode follows *every* reference (premise-carrying
                // productions still lower; parametric targets are needed so a
                // monomorphised instance can resolve its body's bare refs).
                referenced_all(sym, &mut refs);
            } else if prs.is_empty() {
                // Under mode only follows references that will actually be
                // *lowered*: a premise-carrying production is skipped whole, so
                // its references do not enter the dependency closure (keeps demo
                // closures tight, e.g. Bheaptype's skipped `Bs33` branch stays
                // out of the `{Breftype}` closure). Within a kept production,
                // only resolvable references form a real edge.
                referenced_resolvable(&ctx, sym, &mut refs);
            }
        }
        for r in refs {
            if let Some((rn, _)) = ctx.by_name.get_key_value(r.as_str())
                && seen.insert(rn)
            {
                queue.push_back(rn);
            }
        }
    }

    // 2. Assign a non-terminal to every grammar in the closure (kept even if
    //    it lowers to zero productions — flagged dead below). NtIds are dense
    //    in discovery order.
    let ids: BTreeMap<&str, NtId> = order
        .iter()
        .map(|name| (*name, ctx.cfg.add_nt(*name)))
        .collect();

    // 3. Lower each grammar's productions (under the empty top-level binding).
    let root_env = Binding::default();
    for name in &order {
        let g = ctx.by_name[name];
        let lhs = ids[name];
        let mut lowered_here = 0usize;
        let mut skipped_here = 0usize;
        for (production, p) in g.prods.iter().enumerate() {
            match lower_prod(&mut ctx, &ids, &root_env, g, lhs, p) {
                Ok(n) => {
                    lowered_here += n;
                    ctx.report.lowered_prods += 1;
                }
                Err(err) => {
                    ctx.report.note_skip(&g.name, production, &err);
                    skipped_here += 1;
                }
            }
        }
        let cov = match (lowered_here, skipped_here) {
            (0, _) => Coverage::None,
            (_, 0) => Coverage::Full,
            _ => Coverage::Partial,
        };
        ctx.report.grammars.insert((*name).to_string(), cov);
    }

    (ctx.cfg, ctx.report)
}

/// Lower one SpecTec production. Returns the number of `Cfg` productions
/// emitted (>1 under `Alt`-distribution), or a [`CfgLowerError`] describing
/// why it was skipped as a whole.
fn lower_prod(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    g: &Grammar,
    lhs: NtId,
    p: &SpecTecProd,
) -> Result<usize, CfgLowerError> {
    let SpecTecProd::Prod { g: sym, prs, .. } = p;
    if !prs.is_empty() {
        if !ctx.mode.is_recognition() {
            return Err(CfgLowerError::Premise {
                grammar: g.name.clone(),
                count: prs.len(),
            });
        }
        // Recognition mode: classify each premise (design §M6.3).
        match classify_premises(ctx, env, g, prs) {
            PremiseVerdict::Drop => {
                // A param-only premise evaluated to `false` under this instance
                // binding — the production genuinely cannot fire (exact).
                return Ok(0);
            }
            PremiseVerdict::Skip => {
                // Not cleanly classifiable / not evaluable — skip conservatively.
                return Err(CfgLowerError::Premise {
                    grammar: g.name.clone(),
                    count: prs.len(),
                });
            }
            PremiseVerdict::Keep => { /* fall through and lower the RHS */ }
        }
    }
    // Segment the RHS into one-or-more alternative segment sequences
    // (Alt-distribution). Attr captures are stripped along the way.
    let alts = segment_alts(ctx, ids, env, g, sym)?;
    let n = alts.len();
    for segs in alts {
        ctx.cfg.add_prod(lhs, segs);
    }
    Ok(n)
}

/// Recognition-mode premise classification outcome for a whole production.
enum PremiseVerdict {
    /// Keep the production (all premises are input-value premises dropped as
    /// over-approx, or param-guards that evaluate true / absent).
    Keep,
    /// Drop the production entirely — a param-guard evaluated false (exact).
    Drop,
    /// Skip conservatively (a premise is neither cleanly param-only nor
    /// value-only, or cannot be evaluated).
    Skip,
}

/// Classify a production's premises against the instance binding `env`
/// (design §M6.3). A premise mentioning **only** grammar parameters is a
/// *param-guard*: it is evaluated, and a `false` verdict drops the production
/// exactly (this is what bounds the `BuN` recursion at `N ≤ 7`). A premise
/// mentioning captured production-local values (the `Attr`-bound `n`/`m`/…) is
/// an *input-value* premise: it is dropped as an over-approximation and counted
/// [`CfgReport::premises_dropped`]. An `Iter`-wrapped `if` over
/// production-locals is treated as an input-value premise too (dropped,
/// counted). Anything unclassifiable / unevaluable ⇒
/// [`PremiseVerdict::Skip`] (sound).
fn classify_premises(
    ctx: &mut Ctx,
    env: &Binding,
    g: &Grammar,
    prs: &[spectec_ast::SpecTecPrem],
) -> PremiseVerdict {
    let param_names: BTreeSet<&str> = g.params.iter().filter_map(param_name).collect();
    let mut dropped_value_premises = 0usize;
    let mut verdict = PremiseVerdict::Keep;
    for pr in prs {
        match pr {
            spectec_ast::SpecTecPrem::If { e } => {
                if premise_is_param_only(e, &param_names) {
                    match eval_pred(&env.ints, e) {
                        Some(true) => { /* guard holds — keep */ }
                        Some(false) => return PremiseVerdict::Drop,
                        None => return PremiseVerdict::Skip,
                    }
                } else {
                    // Mentions a captured production-local value ⇒ input-value
                    // premise.
                    dropped_value_premises += 1;
                }
            }
            // An **iterated** `if` premise (`(if e)^…` with `dom` bindings over
            // captured production-locals — `Bmodule`'s data-count and
            // func/code-correlation checks) instantiates its body once per
            // element of a value-level iteration. When the body mentions
            // production-local values it is an input-value premise exactly like
            // the plain-`If` case: dropped as an over-approximation, counted.
            // A param-only iterated body cannot be evaluated without the
            // (value-level) iteration domain, so it stays a conservative skip.
            spectec_ast::SpecTecPrem::Iter { pr1, .. } => {
                let spectec_ast::SpecTecPrem::If { e } = pr1.as_ref() else {
                    return PremiseVerdict::Skip;
                };
                if premise_is_param_only(e, &param_names) {
                    return PremiseVerdict::Skip;
                }
                dropped_value_premises += 1;
            }
            // Other premise shapes (rule / let / else) are unclassifiable.
            spectec_ast::SpecTecPrem::Rule { .. }
            | spectec_ast::SpecTecPrem::Let { .. }
            | spectec_ast::SpecTecPrem::Else => return PremiseVerdict::Skip,
        }
    }
    if dropped_value_premises > 0 {
        ctx.report.premises_dropped += dropped_value_premises;
        verdict = PremiseVerdict::Keep;
    }
    verdict
}

/// Whether every free name in `e` is a grammar parameter (so `e` is a
/// param-guard, evaluable from the instance binding alone). The corpus's
/// premises reference exactly the grammar params (`N`) and captured
/// production-local values (`n`, `m`); a premise that mentions *only* the
/// params is param-only.
fn premise_is_param_only(e: &SpecTecExp, param_names: &BTreeSet<&str>) -> bool {
    !exp_mentions_non_params(e, param_names)
}

/// Does `e` mention any free name that is *not* one of `param_names`? Mirrors
/// [`exp_mentions_names`]'s traversal but with an inverted membership test:
/// a leaf `Var{id}` / nullary `Call{x}` counts iff `id`/`x ∉ param_names`.
fn exp_mentions_non_params(e: &SpecTecExp, param_names: &BTreeSet<&str>) -> bool {
    use SpecTecExp::*;
    match e {
        Var { id } => !param_names.contains(id.as_str()),
        Call { x, as1 } => {
            !param_names.contains(x.as_str())
                || as1.iter().any(|a| arg_mentions_non_params(a, param_names))
        }
        Bool { .. } | Num { .. } | Text { .. } => false,
        Un { e2, .. } => exp_mentions_non_params(e2, param_names),
        Bin { e1, e2, .. }
        | Cmp { e1, e2, .. }
        | Idx { e1, e2, .. }
        | Comp { e1, e2, .. }
        | Mem { e1, e2, .. }
        | Cat { e1, e2, .. } => {
            exp_mentions_non_params(e1, param_names) || exp_mentions_non_params(e2, param_names)
        }
        Slice { e1, e2, e3, .. } => {
            exp_mentions_non_params(e1, param_names)
                || exp_mentions_non_params(e2, param_names)
                || exp_mentions_non_params(e3, param_names)
        }
        Upd { e1, e2, .. } | Ext { e1, e2, .. } => {
            exp_mentions_non_params(e1, param_names) || exp_mentions_non_params(e2, param_names)
        }
        Str { efs } => efs.iter().any(|ef| {
            let spectec_ast::SpecTecExpField::Field { e, .. } = ef;
            exp_mentions_non_params(e, param_names)
        }),
        Dot { e1, .. }
        | Len { e1 }
        | Iter { e1, .. }
        | Proj { e1, .. }
        | Case { e1, .. }
        | Uncase { e1, .. }
        | Unopt { e1 }
        | Lift { e1 }
        | Cvt { e1, .. }
        | Sub { e1, .. } => exp_mentions_non_params(e1, param_names),
        Tup { es } | List { es } => es.iter().any(|e| exp_mentions_non_params(e, param_names)),
        Opt { eo } => eo
            .as_ref()
            .is_some_and(|e| exp_mentions_non_params(e, param_names)),
    }
}

fn arg_mentions_non_params(a: &SpecTecArg, param_names: &BTreeSet<&str>) -> bool {
    match a {
        SpecTecArg::Exp { e } => exp_mentions_non_params(e, param_names),
        SpecTecArg::Gram { .. } => true, // grammar arg = not a plain param name
        SpecTecArg::Def { x } => !param_names.contains(x.as_str()),
        SpecTecArg::Typ { .. } => false,
    }
}

/// A partially-built alternative: a sequence of segments.
type SegSeq = Vec<Seg<u8>>;

/// Segment a symbol into a set of alternative segment-sequences, distributing
/// any `Alt` that contains a non-terminal (language-preserving). Attr wrappers
/// are stripped (counted) and their bodies segmented in place.
///
/// The cartesian product across sequential positions realises
/// `Alt`-distribution: `a (b | X) c` with `X` a non-terminal becomes
/// `{a b c, a X c}`.
fn segment_alts(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    g: &Grammar,
    sym: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    // Flatten to a top-level sequence of items, then take the cartesian
    // product of each item's alternatives.
    let items = flatten_seq(sym);
    let mut acc: Vec<SegSeq> = vec![Vec::new()];
    for item in items {
        let item_alts = segment_item(ctx, ids, env, g, item)?;
        let mut next: Vec<SegSeq> = Vec::with_capacity(acc.len() * item_alts.len());
        for prefix in &acc {
            for suffix in &item_alts {
                let mut combined = prefix.clone();
                combined.extend(suffix.iter().cloned());
                next.push(combined);
            }
        }
        acc = next;
    }
    Ok(acc)
}

/// Flatten a top-level `Seq` (and Attr-wrapped `Seq`s) into an item list.
/// Non-`Seq` symbols yield a single-item list.
fn flatten_seq(sym: &SpecTecSym) -> Vec<&SpecTecSym> {
    match sym {
        SpecTecSym::Seq { gs } => gs.iter().flat_map(flatten_seq).collect(),
        other => vec![other],
    }
}

/// Segment one sequence item into its alternative segment-sequences.
///
/// - A `Var`-free item routes wholesale through [`sym_to_regex_u8`] to a
///   single `Term` segment.
/// - An `Attr` is stripped (counted) and its body re-segmented.
/// - An `Alt` containing a non-terminal distributes into one alternative per
///   arm.
/// - A `Var` (resolvable) becomes a single `NonTerm` segment.
/// - An `Iter` over a `Var`-containing body desugars via synthetic
///   non-terminals.
fn segment_item(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    g: &Grammar,
    item: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    // Fast path: no non-terminal anywhere → one terminal segment.
    if !contains_nonterminal(item) {
        let r = bridge(ctx, g, item)?;
        return Ok(vec![vec![Seg::Term(r)]]);
    }
    match item {
        SpecTecSym::Attr { e, g1 } => {
            // Recognition mode: a *parameter-equality* attr over `Bbyte` whose
            // expression const-folds to a ground byte (`Bsection_`'s id byte
            // `[N]:Bbyte` under an instance binding, or a literal constant)
            // folds to exactly that literal byte — **exact**: the SpecTec
            // capture constrains the parsed byte to equal the ground value.
            // Restricted to recognition mode so `lower()`'s corpus output is
            // byte-identical to before (Under mode never has bindings and
            // never reaches these productions anyway).
            if ctx.mode.is_recognition()
                && is_bare_bbyte(g1)
                && let Some(v) = fold_attr_exp(&env.ints, e)
                && (0..=255).contains(&v)
            {
                ctx.report.attrs_folded += 1;
                return Ok(vec![vec![Seg::Term(Regex::Lit(v as u8))]]);
            }
            if attr_is_constraint(e) {
                ctx.report.attrs_constrained += 1;
            } else {
                ctx.report.attrs_captured += 1;
            }
            segment_item(ctx, ids, env, g, g1)
        }
        SpecTecSym::Seq { .. } => segment_alts(ctx, ids, env, g, item),
        SpecTecSym::Var { x, as1 } => {
            // A bare reference to a **grammar-valued parameter** (`BX` inside
            // `Blist`/`Bsection_`) resolves through the instance binding to
            // the argument non-terminal. Only recognition-mode instantiation
            // populates `grams`, so this arm is inert under `lower()`.
            if as1.is_empty()
                && let Some(&nt) = env.grams.get(x.as_str())
            {
                return Ok(vec![vec![Seg::NonTerm(nt)]]);
            }
            if ctx.var_resolvable(x, as1) {
                // Bare / param-independent ref → plain non-terminal (both modes).
                return match ids.get(x.as_str()) {
                    Some(&nt) => Ok(vec![vec![Seg::NonTerm(nt)]]),
                    // A reference outside the closure shouldn't happen (the BFS
                    // added every referenced grammar), but if the target is
                    // unknown entirely, treat it as an unresolvable ref.
                    None => Err(CfgLowerError::ParametricRef {
                        name: x.clone(),
                        args: as1.len(),
                    }),
                };
            }
            // Under mode: parametric ref needs monomorphisation (later); skip.
            if !ctx.mode.is_recognition() {
                return Err(CfgLowerError::ParametricRef {
                    name: x.clone(),
                    args: as1.len(),
                });
            }
            // Recognition mode: resolve the args to ground instance arguments
            // (const-folding `Exp`s, recursively instantiating grammar-valued
            // args, rendering type args) and monomorphise.
            let gargs = fold_inst_args(ctx, ids, env, x, as1)?;
            let nt = instantiate(ctx, ids, x, &gargs)?;
            Ok(vec![vec![Seg::NonTerm(nt)]])
        }
        SpecTecSym::Alt { gs } => {
            // Distribute: one alternative segment-sequence per arm.
            let mut out = Vec::new();
            for arm in gs {
                out.extend(segment_alts(ctx, ids, env, g, arm)?);
            }
            Ok(out)
        }
        SpecTecSym::Iter { g1, it, xes } => {
            if !xes.is_empty() {
                // `dom`-carrying iteration: skip under Under mode; widen to a
                // star under recognition mode (over-approx).
                if ctx.mode.is_recognition() {
                    ctx.report.listns_widened += 1;
                    return desugar_star(ctx, ids, env, g, g1);
                }
                return Err(CfgLowerError::IterWithDom {
                    grammar: g.name.clone(),
                });
            }
            match it {
                SpecTecIter::ListN { .. } => {
                    if ctx.mode.is_recognition() {
                        // Widen the parametric-length iteration to a star
                        // (WASM vectors may be empty) — over-approx.
                        ctx.report.listns_widened += 1;
                        desugar_star(ctx, ids, env, g, g1)
                    } else {
                        Err(CfgLowerError::ListN {
                            grammar: g.name.clone(),
                        })
                    }
                }
                SpecTecIter::Opt => desugar_opt(ctx, ids, env, g, g1),
                SpecTecIter::List => desugar_star(ctx, ids, env, g, g1),
                SpecTecIter::List1 => desugar_plus(ctx, ids, env, g, g1),
            }
        }
        // Range / Num / Text / Eps never contain a non-terminal (the fast path
        // above handles them); reaching here means a genuinely non-regular
        // leaf, which the bridge will reject with a typed error.
        other => {
            let r = bridge(ctx, g, other)?;
            Ok(vec![vec![Seg::Term(r)]])
        }
    }
}

/// Resolve a parametric reference's arguments to ground [`InstArg`]s
/// (recognition mode):
///
/// - an `Exp` argument const-folds to an [`InstArg::Int`] via [`fold_exp`];
/// - a **grammar-valued** argument (`Blist`/`Bsection_`'s `BX`) resolves via
///   [`resolve_gram_sym`] to a non-terminal — a plain grammar NT, a
///   pass-through of an enclosing grammar param, or a recursively
///   monomorphised nested instance (`Btypesec`'s
///   `Bsection_(1, type, Blist(type, Btype))`);
/// - a `Typ` argument is rendered canonically ([`render_typ`]) — it never
///   affects the byte language but stays in the key so distinct call shapes
///   stay distinct;
/// - a `Def` argument (none occur in the corpus's grammar refs) fails.
///
/// Any unresolvable argument fails the whole reference with a
/// [`CfgLowerError::ParametricRef`] — the caller then skips that production
/// (an honest under-approximation of the recognition `Cfg`).
fn fold_inst_args(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    name: &str,
    as1: &[SpecTecArg],
) -> Result<Vec<InstArg>, CfgLowerError> {
    let err = || CfgLowerError::ParametricRef {
        name: name.to_string(),
        args: as1.len(),
    };
    let mut out = Vec::with_capacity(as1.len());
    for a in as1 {
        match a {
            SpecTecArg::Exp { e } => {
                out.push(InstArg::Int(fold_exp(&env.ints, e).ok_or_else(err)?))
            }
            SpecTecArg::Gram { g } => {
                out.push(InstArg::Gram(resolve_gram_sym(ctx, ids, env, name, g)?))
            }
            SpecTecArg::Typ { t } => out.push(InstArg::Typ(render_typ(t))),
            SpecTecArg::Def { .. } => return Err(err()),
        }
    }
    Ok(out)
}

/// Resolve a grammar-valued argument symbol to a non-terminal (recognition
/// mode). The corpus's grammar args are always `Var` references; anything else
/// fails with a typed [`CfgLowerError::ParametricRef`] (honest skip).
fn resolve_gram_sym(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    referrer: &str,
    sym: &SpecTecSym,
) -> Result<NtId, CfgLowerError> {
    let SpecTecSym::Var { x, as1 } = sym else {
        return Err(CfgLowerError::ParametricRef {
            name: format!("{referrer}<non-var grammar arg>"),
            args: 0,
        });
    };
    // A bare grammar-param name passes the enclosing binding through.
    if as1.is_empty()
        && let Some(&nt) = env.grams.get(x.as_str())
    {
        return Ok(nt);
    }
    // A bare / param-independent grammar resolves to its plain NT.
    if ctx.var_resolvable(x, as1) {
        return ids
            .get(x.as_str())
            .copied()
            .ok_or(CfgLowerError::ParametricRef {
                name: x.clone(),
                args: as1.len(),
            });
    }
    // Otherwise it is itself a parametric reference: recursively instantiate
    // (`Blist(type, Btype)` nested inside `Bsection_`'s argument list).
    let gargs = fold_inst_args(ctx, ids, env, x, as1)?;
    instantiate(ctx, ids, x, &gargs)
}

/// Canonical rendering of a type argument for the instance key / name.
/// Injective enough for the corpus (plain `Var` types, iterated types, small
/// tuples); collisions could only merge instances whose byte languages agree
/// anyway (type args never reach the byte level).
fn render_typ(t: &spectec_ast::SpecTecTyp) -> String {
    use spectec_ast::SpecTecTyp::*;
    match t {
        Var { x, as1 } if as1.is_empty() => x.clone(),
        Var { x, as1 } => format!("{x}<{}>", as1.len()),
        Bool => "bool".into(),
        Num(_) => "num".into(),
        Text => "text".into(),
        Tup { ets } => format!("tup{}", ets.len()),
        Iter { t1, it } => {
            let mut s = render_typ(t1);
            for i in it {
                s.push(match i {
                    SpecTecIter::Opt => '?',
                    SpecTecIter::List | SpecTecIter::ListN { .. } => '*',
                    SpecTecIter::List1 => '+',
                });
            }
            s
        }
    }
}

/// Monomorphise grammar `name` at ground arguments `args` into a deduped
/// per-instance non-terminal (recognition mode). Returns the cached instance
/// NT if one exists; otherwise mints `"name@a,b,…"`, caches it, and lowers
/// `name`'s productions under the binding `params ↦ args`.
///
/// LEB128 (`BuN`/`BsN`) short-circuits to a single [`leb128_regex`] terminal
/// rather than unrolling the self-recursive byte productions (design §M6.1);
/// `BfN` becomes `N/8` full-range byte segments. The mono cache + the
/// [`MAX_INST_DEPTH`] guard keep instantiation total even for self-recursive
/// grammars whose recursion the cache does not immediately close.
fn instantiate(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    name: &str,
    args: &[InstArg],
) -> Result<NtId, CfgLowerError> {
    let key = (name.to_string(), args.to_vec());
    if let Some(&nt) = ctx.mono.get(&key) {
        return Ok(nt);
    }

    // LEB128 special-case: a single regex terminal, exact on byte count.
    if (name == "BuN" || name == "BsN")
        && let [InstArg::Int(n)] = args
    {
        let n = *n;
        let nt = ctx.cfg.add_nt(inst_name(ctx, name, args));
        ctx.mono.insert(key, nt);
        ctx.report.mono_instances += 1;
        ctx.cfg.add_prod(nt, vec![Seg::Term(leb128_regex(n))]);
        return Ok(nt);
    }
    // BfN(N): exactly N/8 full-range bytes (fixed count, exact byte shape).
    if name == "BfN"
        && let [InstArg::Int(n)] = args
    {
        let k = n.div_euclid(8).max(0);
        let nt = ctx.cfg.add_nt(inst_name(ctx, name, args));
        ctx.mono.insert(key, nt);
        ctx.report.mono_instances += 1;
        let segs: Vec<Seg<u8>> = (0..k).map(|_| Seg::Term(any_byte_regex())).collect();
        ctx.cfg.add_prod(nt, segs);
        return Ok(nt);
    }

    // General path: look up the target grammar, bind its params, lower its body.
    let Some(&target) = ctx.by_name.get(name) else {
        return Err(CfgLowerError::ParametricRef {
            name: name.to_string(),
            args: args.len(),
        });
    };
    if ctx.inst_depth >= MAX_INST_DEPTH || target.params.len() != args.len() {
        return Err(CfgLowerError::ParametricRef {
            name: name.to_string(),
            args: args.len(),
        });
    }
    // Positionally bind the grammar's params to the ground args: `Exp` params
    // to integers, `Gram` params to resolved non-terminals. A `Typ` param
    // binds nothing (type args never reach the byte level); any other
    // param/arg shape mismatch fails the instantiation.
    let mut inst_env = Binding::default();
    for (p, a) in target.params.iter().zip(args) {
        match (p, a) {
            (SpecTecParam::Exp { x, .. }, InstArg::Int(v)) => {
                inst_env.ints.insert(x.clone(), *v);
            }
            (SpecTecParam::Gram { x, .. }, InstArg::Gram(nt)) => {
                inst_env.grams.insert(x.clone(), *nt);
            }
            (SpecTecParam::Typ { .. }, InstArg::Typ(_)) => {}
            _ => {
                return Err(CfgLowerError::ParametricRef {
                    name: name.to_string(),
                    args: args.len(),
                });
            }
        }
    }
    // Mint + cache the instance NT *before* lowering, so a self-reference at the
    // same key closes on the cache instead of recursing forever.
    let nt = ctx.cfg.add_nt(inst_name(ctx, name, args));
    ctx.mono.insert(key, nt);
    ctx.report.mono_instances += 1;

    ctx.inst_depth += 1;
    for p in &target.prods {
        // Each production of the instance is lowered under `inst_env`; premise
        // classification + monomorphisation recurse with the pushed binding.
        // Errors skip that production (the instance may be partial); the
        // instance NT survives (possibly dead), like any other grammar.
        let _ = lower_prod(ctx, ids, &inst_env, target, nt, p);
    }
    ctx.inst_depth -= 1;
    Ok(nt)
}

/// Instance non-terminal name, e.g. `BuN@32`, `Bsection_@1,type,Blist@type,Btype`.
/// Grammar args render as their resolved NT's name, type args as their
/// canonical rendering. Purely a driver-side label (names are efficiency,
/// never soundness); the dedup key is the full [`InstArg`] vector.
fn inst_name(ctx: &Ctx, name: &str, args: &[InstArg]) -> String {
    let joined = args
        .iter()
        .map(|a| match a {
            InstArg::Int(v) => v.to_string(),
            InstArg::Gram(nt) => ctx.cfg.nt_name(*nt).unwrap_or("<nt>").to_string(),
            InstArg::Typ(s) => s.clone(),
        })
        .collect::<Vec<_>>()
        .join(",");
    format!("{name}@{joined}")
}

/// `X? ⇒ Xo → ε | X` (synthetic `Xo`).
fn desugar_opt(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    g: &Grammar,
    body: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    let body_alts = segment_alts(ctx, ids, env, g, body)?;
    let xo = ctx.fresh_synth(&g.name, "opt");
    ctx.cfg.add_prod(xo, Vec::new());
    for segs in body_alts {
        ctx.cfg.add_prod(xo, segs);
    }
    Ok(vec![vec![Seg::NonTerm(xo)]])
}

/// `X* ⇒ Xs → ε | X Xs` (synthetic `Xs`, right-recursive to avoid left
/// recursion).
fn desugar_star(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    g: &Grammar,
    body: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    let body_alts = segment_alts(ctx, ids, env, g, body)?;
    let xs = ctx.fresh_synth(&g.name, "star");
    ctx.cfg.add_prod(xs, Vec::new());
    for segs in body_alts {
        let mut with_tail = segs;
        with_tail.push(Seg::NonTerm(xs));
        ctx.cfg.add_prod(xs, with_tail);
    }
    Ok(vec![vec![Seg::NonTerm(xs)]])
}

/// `X+ ⇒ Xp → X Xs ; Xs → ε | X Xs` (synthetic, right-recursive).
fn desugar_plus(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    env: &Binding,
    g: &Grammar,
    body: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    let body_alts = segment_alts(ctx, ids, env, g, body)?;
    let xs = ctx.fresh_synth(&g.name, "plusStar");
    ctx.cfg.add_prod(xs, Vec::new());
    for segs in &body_alts {
        let mut with_tail = segs.clone();
        with_tail.push(Seg::NonTerm(xs));
        ctx.cfg.add_prod(xs, with_tail);
    }
    let xp = ctx.fresh_synth(&g.name, "plus");
    for segs in body_alts {
        let mut with_tail = segs;
        with_tail.push(Seg::NonTerm(xs));
        ctx.cfg.add_prod(xp, with_tail);
    }
    Ok(vec![vec![Seg::NonTerm(xp)]])
}

/// Whether `sym` contains a *resolvable* non-terminal reference (a `Var` that
/// will lower to a `NonTerm` segment). Attr wrappers, `Seq`/`Alt`, `Iter`, and
/// `Range` are transparent. A param-dependent `Var{x, as1}` still "contains a
/// non-terminal" so it is routed to `segment_item` (which reports it), rather
/// than mis-sent to the byte-regex bridge.
fn contains_nonterminal(sym: &SpecTecSym) -> bool {
    match sym {
        SpecTecSym::Var { .. } => true,
        SpecTecSym::Num { .. } | SpecTecSym::Text { .. } | SpecTecSym::Eps => false,
        SpecTecSym::Seq { gs } | SpecTecSym::Alt { gs } => gs.iter().any(contains_nonterminal),
        SpecTecSym::Range { g1, g2 } => contains_nonterminal(g1) || contains_nonterminal(g2),
        SpecTecSym::Iter { g1, .. } => contains_nonterminal(g1),
        SpecTecSym::Attr { g1, .. } => contains_nonterminal(g1),
    }
}

/// Bridge a `Var`-free symbol to a byte regex, wrapping the error with grammar
/// context.
fn bridge(ctx: &mut Ctx, g: &Grammar, sym: &SpecTecSym) -> Result<Regex<u8>, CfgLowerError> {
    // Strip any Attr captures nested inside the terminal fragment (counted),
    // so a captured pure-byte fragment like `[b]:0x00` still bridges.
    let stripped = strip_attrs(ctx, sym);
    sym_to_regex_u8(&stripped).map_err(|source| CfgLowerError::Bridge {
        grammar: g.name.clone(),
        source,
    })
}

/// Deep-strip Attr wrappers (counting captures / constraints) from a symbol,
/// returning an Attr-free equivalent. Used inside terminal fragments.
fn strip_attrs(ctx: &mut Ctx, sym: &SpecTecSym) -> SpecTecSym {
    match sym {
        SpecTecSym::Attr { e, g1 } => {
            if attr_is_constraint(e) {
                ctx.report.attrs_constrained += 1;
            } else {
                ctx.report.attrs_captured += 1;
            }
            strip_attrs(ctx, g1)
        }
        SpecTecSym::Seq { gs } => SpecTecSym::Seq {
            gs: gs.iter().map(|g| strip_attrs(ctx, g)).collect(),
        },
        SpecTecSym::Alt { gs } => SpecTecSym::Alt {
            gs: gs.iter().map(|g| strip_attrs(ctx, g)).collect(),
        },
        SpecTecSym::Range { g1, g2 } => SpecTecSym::Range {
            g1: Box::new(strip_attrs(ctx, g1)),
            g2: Box::new(strip_attrs(ctx, g2)),
        },
        SpecTecSym::Iter { g1, it, xes } => SpecTecSym::Iter {
            g1: Box::new(strip_attrs(ctx, g1)),
            it: it.clone(),
            xes: xes.clone(),
        },
        other => other.clone(),
    }
}

// ============================================================================
// Coverage report over the whole binary corpus
// ============================================================================

/// A whole-corpus coverage summary over [`crate::grammar::wasm3_binary`]: for
/// each `B*` grammar, `lower` it as a singleton root and record the coverage
/// of that grammar itself (not its dependencies). This is the "ratchet"
/// surface — its numbers are pinned in tests from the parser's own output.
pub fn coverage() -> CorpusCoverage {
    coverage_in(LowerMode::Under)
}

/// The recognition-mode ([`lower_recognition`]) analogue of [`coverage`]: each
/// `B*` grammar lowered as a singleton root under the over-approximating
/// recognizer. Parametric / LEB128 / premise-carrying grammars that skip under
/// [`coverage`] now classify Full/Partial. Pinned by a *separate* ratchet.
pub fn coverage_recognition() -> CorpusCoverage {
    coverage_in(LowerMode::Recognition)
}

fn coverage_in(mode: LowerMode) -> CorpusCoverage {
    let grammars = crate::grammar::wasm3_binary();
    let names: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
    let mut per_grammar: BTreeMap<String, Coverage> = BTreeMap::new();
    for g in &grammars {
        let (_cfg, report) = lower_with(&grammars, &[g.name.as_str()], mode);
        let cov = report
            .grammars
            .get(&g.name)
            .copied()
            .unwrap_or(Coverage::None);
        per_grammar.insert(g.name.clone(), cov);
    }
    let mut premise_grammars = BTreeSet::new();
    for g in &grammars {
        let has_prem = g.prods.iter().any(|p| {
            let SpecTecProd::Prod { prs, .. } = p;
            !prs.is_empty()
        });
        if has_prem {
            premise_grammars.insert(g.name.clone());
        }
    }
    CorpusCoverage {
        total: names.len(),
        per_grammar,
        premise_grammars,
    }
}

/// Result of [`coverage`].
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CorpusCoverage {
    /// Total number of `B*` grammars.
    pub total: usize,
    /// Per-grammar coverage when lowered as a singleton root.
    pub per_grammar: BTreeMap<String, Coverage>,
    /// Grammars carrying at least one production premise.
    pub premise_grammars: BTreeSet<String>,
}

impl CorpusCoverage {
    /// Count of grammars in a given coverage class.
    pub fn count(&self, cov: Coverage) -> usize {
        self.per_grammar.values().filter(|c| **c == cov).count()
    }

    /// Coverage of a named grammar, if present.
    pub fn of(&self, name: &str) -> Option<Coverage> {
        self.per_grammar.get(name).copied()
    }
}

impl std::fmt::Display for CorpusCoverage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "B* corpus: {} grammars — full={} partial={} none={}; {} carry premises",
            self.total,
            self.count(Coverage::Full),
            self.count(Coverage::Partial),
            self.count(Coverage::None),
            self.premise_grammars.len(),
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- synthetic grammars exercising each rule in isolation ---

    fn prod(sym: SpecTecSym) -> SpecTecProd {
        SpecTecProd::Prod {
            ps: Vec::new(),
            g: sym,
            e: SpecTecExp::Bool { b: true },
            prs: Vec::new(),
        }
    }

    fn prod_with_prem(sym: SpecTecSym) -> SpecTecProd {
        SpecTecProd::Prod {
            ps: Vec::new(),
            g: sym,
            e: SpecTecExp::Bool { b: true },
            prs: vec![spectec_ast::SpecTecPrem::If {
                e: SpecTecExp::Bool { b: true },
            }],
        }
    }

    fn gram(name: &str, prods: Vec<SpecTecProd>) -> Grammar {
        Grammar {
            name: name.to_string(),
            params: Vec::new(),
            typ: spectec_ast::SpecTecTyp::Var {
                x: "x".into(),
                as1: Vec::new(),
            },
            prods,
        }
    }

    fn num(n: i64) -> SpecTecSym {
        SpecTecSym::Num { n }
    }
    fn var(x: &str) -> SpecTecSym {
        SpecTecSym::Var {
            x: x.into(),
            as1: Vec::new(),
        }
    }
    fn capture(inner: SpecTecSym) -> SpecTecSym {
        SpecTecSym::Attr {
            e: SpecTecExp::Var { id: "cap".into() },
            g1: Box::new(inner),
        }
    }

    #[test]
    fn lowers_pure_byte_grammar_to_full() {
        // Bmagic-shaped: one production, four byte literals.
        let g = gram(
            "M",
            vec![prod(SpecTecSym::Seq {
                gs: vec![num(0x00), num(0x61), num(0x73), num(0x6D)],
            })],
        );
        let (cfg, report) = lower(&[g], &["M"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(report.grammars.get("M"), Some(&Coverage::Full));
        assert_eq!(report.lowered_prods, 1);
        let m = cfg.lookup("M").unwrap();
        assert!(cfg.naive_parse(m, &[0x00, 0x61, 0x73, 0x6D]));
        assert!(!cfg.naive_parse(m, &[0x00, 0x61, 0x73]));
    }

    #[test]
    fn skipped_details_are_lossless() {
        let grammars = crate::grammar::wasm3();
        let roots: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
        for (_, report) in [
            lower(&grammars, &roots),
            lower_recognition(&grammars, &roots),
        ] {
            assert_eq!(report.skipped_details.len(), report.skipped_total());
            let mut buckets = BTreeMap::new();
            for skipped in &report.skipped_details {
                let grammar = grammars
                    .iter()
                    .find(|g| g.name == skipped.grammar)
                    .expect("skip names a source grammar");
                assert!(
                    skipped.production < grammar.prods.len(),
                    "skip names a source production"
                );
                *buckets.entry(SkipReason::of(&skipped.error)).or_insert(0) += 1;
            }
            assert_eq!(buckets, report.skipped);
        }
    }

    #[test]
    fn explicit_ground_roots_keep_instance_identity_distinct() {
        let grammars = crate::grammar::wasm3_binary();
        let int_arg = |n| SpecTecArg::Exp {
            e: SpecTecExp::Num {
                n: SpecTecNum::Nat(n),
            },
        };
        let (cfg, _, roots) = lower_recognition_roots(
            &grammars,
            &[
                GrammarRoot::Instance {
                    name: "BuN".into(),
                    args: vec![int_arg(32)],
                },
                GrammarRoot::Instance {
                    name: "BuN".into(),
                    args: vec![int_arg(64)],
                },
            ],
        )
        .unwrap();
        assert_ne!(roots[0], roots[1], "root judgements remain distinct");
        let n32 = cfg.lookup("BuN@32").expect("32-bit instance");
        let n64 = cfg.lookup("BuN@64").expect("64-bit instance");
        assert_ne!(n32, n64, "ground instance keys cannot alias");
    }

    #[test]
    fn explicit_roots_refuse_generic_and_symbolic_parameters() {
        let grammars = crate::grammar::wasm3_binary();
        assert_eq!(
            lower_recognition_roots(&grammars, &[GrammarRoot::Plain("BuN".into())]).unwrap_err(),
            GrammarRootError::ParametersRequired { name: "BuN".into() }
        );
        let symbolic = GrammarRoot::Instance {
            name: "BuN".into(),
            args: vec![SpecTecArg::Exp {
                e: SpecTecExp::Var { id: "N".into() },
            }],
        };
        assert_eq!(
            lower_recognition_roots(&grammars, &[symbolic]).unwrap_err(),
            GrammarRootError::UngroundArgument {
                name: "BuN".into(),
                index: 0,
            }
        );
    }

    #[test]
    fn strips_capture_attr_silently() {
        let g = gram("A", vec![prod(capture(num(0x2A)))]);
        let (cfg, report) = lower(&[g], &["A"]);
        assert_eq!(report.attrs_captured, 1);
        assert_eq!(report.attrs_constrained, 0);
        assert_eq!(report.grammars.get("A"), Some(&Coverage::Full));
        let a = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(a, &[0x2A]));
    }

    #[test]
    fn counts_constraint_attr_separately() {
        // A comparison attr is classified as a (language-approximating)
        // constraint, not a capture.
        let constraint = SpecTecSym::Attr {
            e: SpecTecExp::Cmp {
                op: spectec_ast::SpecTecCmpOp::Eq,
                t: spectec_ast::SpecTecOpTyp::Bool(spectec_ast::SpecTecBoolTyp::Bool),
                e1: Box::new(SpecTecExp::Var { id: "n".into() }),
                e2: Box::new(SpecTecExp::Var { id: "m".into() }),
            },
            g1: Box::new(num(0x00)),
        };
        let g = gram("C", vec![prod(constraint)]);
        let (_cfg, report) = lower(&[g], &["C"]);
        assert_eq!(report.attrs_constrained, 1);
        assert_eq!(report.attrs_captured, 0);
    }

    #[test]
    fn resolves_nonterminal_reference() {
        // A → 0x64 B ; B → 0x70. Two-hop chain, Breftype-shaped.
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Seq {
                gs: vec![num(0x64), var("B")],
            })],
        );
        let b = gram("B", vec![prod(num(0x70))]);
        let (cfg, report) = lower(&[a, b], &["A"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(report.grammars.get("A"), Some(&Coverage::Full));
        assert_eq!(report.grammars.get("B"), Some(&Coverage::Full));
        let a = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(a, &[0x64, 0x70]));
        assert!(!cfg.naive_parse(a, &[0x64]));
    }

    #[test]
    fn distributes_alt_containing_var() {
        // A → 0x00 (B | 0x01) ; B → 0x70.  The Alt with a Var distributes
        // into two Cfg productions.
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Seq {
                gs: vec![
                    num(0x00),
                    SpecTecSym::Alt {
                        gs: vec![var("B"), num(0x01)],
                    },
                ],
            })],
        );
        let b = gram("B", vec![prod(num(0x70))]);
        let (cfg, _report) = lower(&[a, b], &["A"]);
        assert_eq!(cfg.validate(), Ok(()));
        let aid = cfg.lookup("A").unwrap();
        // Two productions for A (one per Alt arm).
        assert_eq!(cfg.productions_of(aid).count(), 2);
        assert!(cfg.naive_parse(aid, &[0x00, 0x70]));
        assert!(cfg.naive_parse(aid, &[0x00, 0x01]));
        assert!(!cfg.naive_parse(aid, &[0x00, 0x02]));
    }

    #[test]
    fn desugars_star_of_var() {
        // A → B* ; B → 0x70.  Synthetic Xs → ε | B Xs.
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Iter {
                g1: Box::new(var("B")),
                it: SpecTecIter::List,
                xes: Vec::new(),
            })],
        );
        let b = gram("B", vec![prod(num(0x70))]);
        let (cfg, report) = lower(&[a, b], &["A"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert!(report.synthetic_nts >= 1);
        assert_eq!(cfg.left_recursion(), None, "right-recursive desugaring");
        let aid = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(aid, &[]));
        assert!(cfg.naive_parse(aid, &[0x70]));
        assert!(cfg.naive_parse(aid, &[0x70, 0x70, 0x70]));
        assert!(!cfg.naive_parse(aid, &[0x71]));
    }

    #[test]
    fn desugars_plus_of_var() {
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Iter {
                g1: Box::new(var("B")),
                it: SpecTecIter::List1,
                xes: Vec::new(),
            })],
        );
        let b = gram("B", vec![prod(num(0x70))]);
        let (cfg, _report) = lower(&[a, b], &["A"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(cfg.left_recursion(), None);
        let aid = cfg.lookup("A").unwrap();
        assert!(!cfg.naive_parse(aid, &[]), "plus needs at least one");
        assert!(cfg.naive_parse(aid, &[0x70]));
        assert!(cfg.naive_parse(aid, &[0x70, 0x70]));
    }

    #[test]
    fn desugars_opt_of_var() {
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Iter {
                g1: Box::new(var("B")),
                it: SpecTecIter::Opt,
                xes: Vec::new(),
            })],
        );
        let b = gram("B", vec![prod(num(0x70))]);
        let (cfg, _report) = lower(&[a, b], &["A"]);
        assert_eq!(cfg.validate(), Ok(()));
        let aid = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(aid, &[]));
        assert!(cfg.naive_parse(aid, &[0x70]));
        assert!(!cfg.naive_parse(aid, &[0x70, 0x70]));
    }

    #[test]
    fn skips_premise_production() {
        let g = gram("A", vec![prod_with_prem(num(0x00)), prod(num(0x01))]);
        let (cfg, report) = lower(&[g], &["A"]);
        assert_eq!(report.grammars.get("A"), Some(&Coverage::Partial));
        assert_eq!(report.skipped.get(&SkipReason::Premise), Some(&1));
        assert_eq!(report.lowered_prods, 1);
        let a = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(a, &[0x01]));
        assert!(!cfg.naive_parse(a, &[0x00]), "premise branch dropped");
    }

    #[test]
    fn dead_nonterminal_kept_and_flagged() {
        // Grammar whose only production carries a premise → 0 lowered → dead.
        let g = gram("A", vec![prod_with_prem(num(0x00))]);
        let (cfg, report) = lower(&[g], &["A"]);
        assert_eq!(report.grammars.get("A"), Some(&Coverage::None));
        // The non-terminal is still present.
        assert!(cfg.lookup("A").is_some());
        assert_eq!(cfg.productions_of(cfg.lookup("A").unwrap()).count(), 0);
    }

    #[test]
    fn skips_parametric_reference() {
        // A → P<arg> where P actually consults its parameter → skip.
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Var {
                x: "P".into(),
                as1: vec![SpecTecArg::Exp {
                    e: SpecTecExp::Num {
                        n: spectec_ast::SpecTecNum::Nat(1),
                    },
                }],
            })],
        );
        // P consults its parameter `q` (in a capture expression), so it is
        // param-dependent — a reference to it needs monomorphisation — yet its
        // own production still lowers (the capture is stripped to `0x00`).
        let mut p = gram(
            "P",
            vec![prod(SpecTecSym::Attr {
                e: SpecTecExp::Var { id: "q".into() },
                g1: Box::new(num(0x00)),
            })],
        );
        p.params = vec![spectec_ast::SpecTecParam::Exp {
            x: "q".into(),
            t: spectec_ast::SpecTecTyp::Var {
                x: "t".into(),
                as1: Vec::new(),
            },
        }];
        assert!(!param_independent(&p), "P consults its parameter");
        let (_cfg, report) = lower(&[a, p], &["A"]);
        // A's parametric ref to P is skipped (A has no other production).
        assert_eq!(report.grammars.get("A"), Some(&Coverage::None));
        // Exactly one parametric-ref skip (A → P<arg>); P itself is not in the
        // closure because the only reference to it is unresolvable.
        assert_eq!(report.skipped.get(&SkipReason::ParametricRef), Some(&1));
    }

    #[test]
    fn resolves_param_independent_reference() {
        // A → P<arg> where P = 0x00 (ignores its parameter) → resolve,
        // discarding the arg. Bvar/Bsym-shaped.
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Var {
                x: "P".into(),
                as1: vec![SpecTecArg::Typ {
                    t: spectec_ast::SpecTecTyp::Var {
                        x: "t".into(),
                        as1: Vec::new(),
                    },
                }],
            })],
        );
        let mut p = gram("P", vec![prod(num(0x00))]);
        p.params = vec![spectec_ast::SpecTecParam::Typ { x: "q".into() }];
        assert!(param_independent(&p));
        let (cfg, report) = lower(&[a, p], &["A"]);
        assert_eq!(report.grammars.get("A"), Some(&Coverage::Full));
        assert_eq!(report.grammars.get("P"), Some(&Coverage::Full));
        let aid = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(aid, &[0x00]));
    }

    #[test]
    fn skips_listn_and_dom_iter() {
        let listn = gram(
            "A",
            vec![prod(SpecTecSym::Iter {
                g1: Box::new(var("B")),
                it: SpecTecIter::ListN {
                    e: Vec::new(),
                    xo: Vec::new(),
                },
                xes: Vec::new(),
            })],
        );
        let b = gram("B", vec![prod(num(0x00))]);
        let (_cfg, report) = lower(&[listn, b.clone()], &["A"]);
        assert_eq!(report.skipped.get(&SkipReason::ListN), Some(&1));

        let dom = gram(
            "A",
            vec![prod(SpecTecSym::Iter {
                g1: Box::new(var("B")),
                it: SpecTecIter::List,
                xes: vec![spectec_ast::SpecTecIterExp::Dom {
                    x: "i".into(),
                    e: SpecTecExp::Var { id: "n".into() },
                }],
            })],
        );
        let (_cfg, report) = lower(&[dom, b], &["A"]);
        assert_eq!(report.skipped.get(&SkipReason::IterWithDom), Some(&1));
    }

    // ========================================================================
    // Corpus coverage ratchet — pinned from the parser's own output.
    // ========================================================================

    /// THE COVERAGE RATCHET. Pins the measured B* corpus facts. Any drop in
    /// coverage or drift in the premise-grammar set fails here; raise the
    /// numbers only when lowering genuinely improves.
    #[test]
    fn coverage_ratchet() {
        let cov = coverage();

        // Total B* grammar count (from the parser, not a prose constant).
        assert_eq!(cov.total, 89, "B* grammar count");

        // Exactly these grammars carry production premises.
        let expected_premise: BTreeSet<String> = [
            "BuN",
            "BsN",
            "Bname",
            "Bheaptype",
            "Bblocktype",
            "Bmemarg",
            "Bsection_",
            "Btable",
            "Bfunc",
            "Bcode",
            "Bmodule",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        assert_eq!(
            cov.premise_grammars, expected_premise,
            "premise-carrying grammar set"
        );
        assert_eq!(cov.premise_grammars.len(), 11);

        // Fully-regular grammars lower to full coverage.
        for name in [
            "Bnumtype",
            "Bvectype",
            "Babsheaptype",
            "Bmut",
            "Bpacktype",
            "Bcastop",
            "Bmagic",
            "Bversion",
            "Bvar",
            "Bsym",
        ] {
            assert_eq!(
                cov.of(name),
                Some(Coverage::Full),
                "{name} should lower to full coverage",
            );
        }

        // Whole-corpus sweep: every B* grammar classifies (never panics), and
        // a premise-free non-parametric grammar is never spuriously `None`
        // unless genuinely empty. Just assert totals are consistent.
        assert_eq!(
            cov.count(Coverage::Full) + cov.count(Coverage::Partial) + cov.count(Coverage::None),
            cov.total,
        );
    }

    /// The `{Breftype}` dependency closure and the T2 demo chain.
    #[test]
    fn breftype_closure() {
        let grammars = crate::grammar::wasm3_binary();
        let (cfg, report) = lower(&grammars, &["Breftype"]);
        assert_eq!(cfg.validate(), Ok(()));

        // Closure is exactly {Breftype, Bheaptype, Babsheaptype}.
        let closure: BTreeSet<&str> = report.grammars.keys().map(|s| s.as_str()).collect();
        let expected: BTreeSet<&str> = ["Breftype", "Bheaptype", "Babsheaptype"]
            .into_iter()
            .collect();
        assert_eq!(closure, expected, "Breftype closure");

        // Breftype lowers (full — all 3 prods are premise-free).
        assert_eq!(report.grammars.get("Breftype"), Some(&Coverage::Full));
        // Bheaptype is PARTIAL — its Bs33 premise branch is skipped.
        assert_eq!(report.grammars.get("Bheaptype"), Some(&Coverage::Partial));
        // Babsheaptype is fully regular.
        assert_eq!(report.grammars.get("Babsheaptype"), Some(&Coverage::Full));

        // No left recursion across the lowered closure.
        assert_eq!(cfg.left_recursion(), None);

        // The chain productions are present and parse the demo bytes:
        //   [0x70]        via Breftype → Babsheaptype
        //   [0x64, 0x70]  via Breftype → 0x64 Bheaptype → Babsheaptype
        let refty = cfg.lookup("Breftype").unwrap();
        assert!(cfg.naive_parse(refty, &[0x70]), "one-hop [0x70]");
        assert!(cfg.naive_parse(refty, &[0x64, 0x70]), "two-hop [0x64,0x70]");
        assert!(cfg.naive_parse(refty, &[0x63, 0x70]), "two-hop [0x63,0x70]");
        // Babsheaptype admits 0x70 directly.
        let abs = cfg.lookup("Babsheaptype").unwrap();
        assert!(cfg.naive_parse(abs, &[0x70]));
        assert!(
            !cfg.naive_parse(abs, &[0x68]),
            "0x68 out of range 0x69-0x74"
        );
    }

    /// Whole-corpus sweep: lowering every B* grammar (as its own root, and the
    /// entire universe at once) is total — it never panics, always validates,
    /// and never left-recurses. Typed skips are fine; panics are not.
    #[test]
    fn whole_corpus_never_panics() {
        let grammars = crate::grammar::wasm3_binary();
        // Each grammar as a singleton root.
        for g in &grammars {
            let (cfg, _report) = lower(&grammars, &[g.name.as_str()]);
            assert_eq!(cfg.validate(), Ok(()), "{} validates", g.name);
        }
        // The entire B* universe at once.
        let roots: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
        let (cfg, report) = lower(&grammars, &roots);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(
            cfg.left_recursion(),
            None,
            "no left recursion across the lowerable B* corpus",
        );
        // Every B* grammar is classified.
        assert_eq!(report.grammars.len(), grammars.len());
        // No constraint attrs occur in the lowered corpus (design claim).
        assert_eq!(
            report.attrs_constrained, 0,
            "no equality/constraint attrs in the B* corpus",
        );
    }

    /// The **whole** bundled spec (all 231 grammars, binary `B*` + text `T*`)
    /// as one universe: lowering is total in both modes, but — unlike the
    /// `B*`-only corpus above — the `T*` text grammars introduce genuine
    /// **left recursion** (the `Thexnum` cycle), which [`Cfg::left_recursion`]
    /// flags. Consumers offering top-down parsing over a whole-spec env must
    /// guard against it (the kernel-side tactic's in-progress set does).
    #[test]
    fn whole_spec_left_recursion() {
        let grammars = crate::grammar::wasm3();
        assert_eq!(grammars.len(), 231, "89 B* + 142 T*");
        let roots: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
        for (label, (cfg, report)) in [
            ("under", lower(&grammars, &roots)),
            ("recognition", lower_recognition(&grammars, &roots)),
        ] {
            assert_eq!(cfg.validate(), Ok(()), "{label} validates");
            assert_eq!(report.grammars.len(), 231, "{label} classifies all");
            assert!(
                cfg.left_recursion().is_some(),
                "{label}: the T* corpus is left-recursive",
            );
        }
        // Rooted at `Thexnum` alone, the offending cycle must name it.
        let (cfg, _report) = lower_recognition(&grammars, &["Thexnum"]);
        let cycle = cfg.left_recursion().expect("Thexnum is left-recursive");
        let names: Vec<&str> = cycle.iter().filter_map(|nt| cfg.nt_name(*nt)).collect();
        assert!(names.contains(&"Thexnum"), "cycle {names:?} names Thexnum");
    }

    /// [`CfgReport::coverage_of_nt`] attributes synthetic (`X$…`) and
    /// monomorphised-instance (`X@…`) non-terminals to their source grammar.
    #[test]
    fn coverage_of_nt_attribution() {
        // A → B* ; B → 0x70 — the star mints a synthetic `A$star…` NT.
        let a = gram(
            "A",
            vec![prod(SpecTecSym::Iter {
                g1: Box::new(var("B")),
                it: SpecTecIter::List,
                xes: Vec::new(),
            })],
        );
        let b = gram("B", vec![prod(num(0x70))]);
        let (cfg, report) = lower(&[a, b], &["A"]);
        let synth = cfg
            .nts()
            .iter()
            .find(|d| d.name.starts_with("A$"))
            .expect("synthetic NT minted");
        assert_eq!(report.coverage_of_nt(&synth.name), Some(Coverage::Full));
        assert_eq!(report.coverage_of_nt("A"), Some(Coverage::Full));
        assert_eq!(report.coverage_of_nt("nope"), None);
        // Instance NTs attribute to the generic grammar (conservative).
        assert_eq!(
            report.coverage_of_nt("A@32,1"),
            Some(Coverage::Full),
            "X@args strips to X"
        );
    }

    // ========================================================================
    // Differential: lowered Cfg vs sym_to_regex_u8 for fully-regular grammars.
    // ========================================================================

    /// For a fully-regular grammar with single-symbol productions, the lowered
    /// `Cfg` accepts exactly the bytes each production's regex accepts.
    #[test]
    fn differential_regular_grammars() {
        let grammars = crate::grammar::wasm3_binary();

        // Babsheaptype: 12 single-byte productions 0x69..=0x74.
        let (cfg, _r) = lower(&grammars, &["Babsheaptype"]);
        let abs = cfg.lookup("Babsheaptype").unwrap();
        for b in 0x69u8..=0x74 {
            assert!(cfg.naive_parse(abs, &[b]), "Babsheaptype accepts {b:#x}");
        }
        for b in [0x68u8, 0x75, 0x00, 0xFF] {
            assert!(!cfg.naive_parse(abs, &[b]), "Babsheaptype rejects {b:#x}");
        }

        // Bnumtype: 0x7C..=0x7F.
        let (cfg, _r) = lower(&grammars, &["Bnumtype"]);
        let nt = cfg.lookup("Bnumtype").unwrap();
        for b in 0x7Cu8..=0x7F {
            assert!(cfg.naive_parse(nt, &[b]), "Bnumtype accepts {b:#x}");
        }
        for b in [0x7Bu8, 0x80] {
            assert!(!cfg.naive_parse(nt, &[b]), "Bnumtype rejects {b:#x}");
        }
        // Cross-check against sym_to_regex_u8: each production is a single-byte
        // regex, and the union of their languages is what the Cfg accepts.
        let g = grammars.iter().find(|g| g.name == "Bnumtype").unwrap();
        let mut regex_bytes = BTreeSet::new();
        for p in &g.prods {
            let SpecTecProd::Prod { g: sym, .. } = p;
            // These are bare byte literals; the bridge must succeed.
            if let Regex::Lit(b) = sym_to_regex_u8(sym).unwrap() {
                regex_bytes.insert(b);
            }
        }
        assert_eq!(
            regex_bytes,
            [0x7C, 0x7D, 0x7E, 0x7F].into_iter().collect(),
            "Bnumtype regex bytes",
        );
        for &b in &regex_bytes {
            assert!(cfg.naive_parse(nt, &[b]));
        }
    }

    #[test]
    fn report_display_is_stable() {
        let g = gram("A", vec![prod(num(0x00)), prod_with_prem(num(0x01))]);
        let (_cfg, report) = lower(&[g], &["A"]);
        let s = format!("{report}");
        assert!(s.contains("productions lowered"));
        assert!(s.contains("premise=1"));
        assert!(s.contains("partial=1"));
    }

    // ========================================================================
    // M6 recognition mode: const-fold, eval-pred, LEB128 regex, monomorphiser.
    // ========================================================================

    fn nat(n: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(n),
        }
    }

    fn bin(op: SpecTecBinOp, a: SpecTecExp, b: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Bin {
            op,
            t: spectec_ast::SpecTecOpTyp::Num(spectec_ast::SpecTecNumTyp::Nat),
            e1: Box::new(a),
            e2: Box::new(b),
        }
    }

    fn cmp(op: SpecTecCmpOp, a: SpecTecExp, b: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Cmp {
            op,
            t: spectec_ast::SpecTecOpTyp::Num(spectec_ast::SpecTecNumTyp::Nat),
            e1: Box::new(a),
            e2: Box::new(b),
        }
    }

    fn var_exp(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }

    #[test]
    fn fold_exp_arithmetic() {
        let mut env = ParamEnv::new();
        env.insert("N".into(), 32);
        // N - 7 = 25
        assert_eq!(
            fold_exp(&env, &bin(SpecTecBinOp::Sub, var_exp("N"), nat(7))),
            Some(25),
        );
        // 2 ^ 7 = 128
        assert_eq!(
            fold_exp(&env, &bin(SpecTecBinOp::Pow, nat(2), nat(7))),
            Some(128),
        );
        // Cvt is value-preserving.
        let cvt = SpecTecExp::Cvt {
            nt1: spectec_ast::SpecTecNumTyp::Nat,
            nt2: spectec_ast::SpecTecNumTyp::Int,
            e1: Box::new(var_exp("N")),
        };
        assert_eq!(fold_exp(&env, &cvt), Some(32));
        // Unknown var / division by zero / non-int are None.
        assert_eq!(fold_exp(&env, &var_exp("M")), None);
        assert_eq!(
            fold_exp(&env, &bin(SpecTecBinOp::Div, nat(1), nat(0))),
            None,
        );
    }

    #[test]
    fn eval_pred_guards() {
        let mut env = ParamEnv::new();
        env.insert("N".into(), 32);
        // N > 7  ⇒ true
        assert_eq!(
            eval_pred(&env, &cmp(SpecTecCmpOp::Gt, var_exp("N"), nat(7))),
            Some(true),
        );
        // N > 7 && N < 4  ⇒ false
        let conj = bin(
            SpecTecBinOp::And,
            cmp(SpecTecCmpOp::Gt, var_exp("N"), nat(7)),
            cmp(SpecTecCmpOp::Lt, var_exp("N"), nat(4)),
        );
        assert_eq!(eval_pred(&env, &conj), Some(false));
        // Unbound var ⇒ None (unevaluable).
        assert_eq!(
            eval_pred(&env, &cmp(SpecTecCmpOp::Lt, var_exp("n"), nat(128))),
            None,
        );
        // At N = 4 the BuN continuation guard `N > 7` is false — this is what
        // bounds the recursion.
        let mut env4 = ParamEnv::new();
        env4.insert("N".into(), 4);
        assert_eq!(
            eval_pred(&env4, &cmp(SpecTecCmpOp::Gt, var_exp("N"), nat(7))),
            Some(false),
        );
    }

    #[test]
    fn leb128_regex_byte_count() {
        // ceil(32/7) = 5 bytes ⇒ up to 4 continuation bytes then 1 terminator.
        match leb128_regex(32) {
            Regex::Concat(items) => {
                assert_eq!(items.len(), 2);
                match &items[0] {
                    Regex::Rep { min, max, .. } => {
                        assert_eq!(*min, 0);
                        assert_eq!(*max, Some(4));
                    }
                    other => panic!("expected Rep, got {other:?}"),
                }
            }
            other => panic!("expected Concat, got {other:?}"),
        }
        // ceil(64/7) = 10 ⇒ max 9 continuation bytes.
        if let Regex::Concat(items) = leb128_regex(64)
            && let Regex::Rep { max, .. } = &items[0]
        {
            assert_eq!(*max, Some(9));
        } else {
            panic!("bad leb128_regex(64)");
        }
        // ceil(33/7) = 5 (Bs33) ⇒ max 4.
        if let Regex::Concat(items) = leb128_regex(33)
            && let Regex::Rep { max, .. } = &items[0]
        {
            assert_eq!(*max, Some(4));
        } else {
            panic!("bad leb128_regex(33)");
        }
    }

    #[test]
    fn leb128_regex_matches_like_unbounded_oracle() {
        use covalence_grammar::cfg::{Cfg, Seg};
        // A single-terminal Cfg over leb128_regex(32); compare its acceptance
        // to the crate's unbounded `simple::leb128_unsigned` regex on the
        // bytes within the 5-byte bound. Both accept the same words there.
        let mut cfg: Cfg<u8> = Cfg::new();
        let n = cfg.add_nt("L");
        cfg.add_prod(n, vec![Seg::Term(leb128_regex(32))]);
        let ln = cfg.lookup("L").unwrap();
        let unbounded = crate::grammar::simple::leb128_unsigned();

        for bytes in [
            &[0x00u8][..],
            &[0x7F][..],
            &[0x80, 0x01][..],
            &[0xE5, 0x8E, 0x26][..],
            &[0x80, 0x80, 0x80, 0x80, 0x00][..], // 5 bytes = exactly the bound
        ] {
            let mut mono: Cfg<u8> = Cfg::new();
            let m = mono.add_nt("M");
            mono.add_prod(m, vec![Seg::Term(unbounded.clone())]);
            let mm = mono.lookup("M").unwrap();
            assert!(cfg.naive_parse(ln, bytes), "bounded accepts {bytes:?}");
            assert!(mono.naive_parse(mm, bytes), "unbounded accepts {bytes:?}");
        }
        // Incomplete (no terminator) is rejected by both.
        assert!(!cfg.naive_parse(ln, &[0x80]));
        // The 6-byte over-long encoding: unbounded accepts, bounded rejects
        // (the byte-count bound is the extra precision the recognizer buys).
        let overlong = &[0x80u8, 0x80, 0x80, 0x80, 0x80, 0x00][..];
        assert!(!cfg.naive_parse(ln, overlong), "bounded rejects 6-byte");
    }

    /// A parametric grammar builder for monomorphiser tests: `grammar name(N)`.
    fn param_gram(name: &str, prods: Vec<SpecTecProd>) -> Grammar {
        let mut g = gram(name, prods);
        g.params = vec![SpecTecParam::Exp {
            x: "N".into(),
            t: spectec_ast::SpecTecTyp::Var {
                x: "nat".into(),
                as1: Vec::new(),
            },
        }];
        g
    }

    fn var_arg(x: &str, arg: SpecTecExp) -> SpecTecSym {
        SpecTecSym::Var {
            x: x.into(),
            as1: vec![SpecTecArg::Exp { e: arg }],
        }
    }

    #[test]
    fn monomorphises_bun_leb128_from_corpus() {
        // The real Bu32 = BuN(32) chain: recognition mode instantiates BuN@32
        // to a single leb128 regex terminal and Bu32 resolves through to it.
        let gs = crate::grammar::wasm3_binary();

        // Under mode: Bu32 still skips (BuN parametric ref unresolved).
        let (_c, ur) = lower(&gs, &["Bu32"]);
        assert_eq!(
            ur.grammars.get("Bu32"),
            Some(&Coverage::None),
            "Under mode leaves Bu32 dead (unchanged)",
        );
        assert_eq!(ur.mono_instances, 0, "Under mode never monomorphises");

        // Recognition mode: BuN@32 instance NT lowering to the leb128 regex.
        let (cfg, rep) = lower_recognition(&gs, &["Bu32"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(cfg.left_recursion(), None);
        assert!(rep.mono_instances >= 1, "at least BuN@32 minted");
        assert!(cfg.lookup("BuN@32").is_some(), "BuN@32 instance NT present");
        assert_eq!(rep.grammars.get("Bu32"), Some(&Coverage::Full));

        // BuN@32 lowers to exactly one production, a single leb128 regex term.
        let buni = cfg.lookup("BuN@32").unwrap();
        let prods: Vec<_> = cfg.productions_of(buni).collect();
        assert_eq!(prods.len(), 1);
        assert!(
            matches!(prods[0].1.segs.as_slice(), [Seg::Term(_)]),
            "BuN@32 is a single terminal",
        );

        // Differential: Bu32 accepts real LEB128 varints, rejects incomplete.
        let bu32 = cfg.lookup("Bu32").unwrap();
        assert!(cfg.naive_parse(bu32, &[0x80, 0x01]), "128");
        assert!(cfg.naive_parse(bu32, &[0xE5, 0x8E, 0x26]), "624485");
        assert!(cfg.naive_parse(bu32, &[0x00]), "0");
        assert!(!cfg.naive_parse(bu32, &[0x80]), "incomplete rejected");
    }

    #[test]
    fn instance_dedup_shares_nt() {
        // Two references to P(32) share a single P@32 instance NT. `P` is made
        // param-dependent (a param-guard premise) so it is monomorphised rather
        // than resolved as a bare (param-ignoring) reference.
        let a = param_gram(
            "A",
            vec![prod(SpecTecSym::Seq {
                gs: vec![var_arg("P", nat(32)), var_arg("P", nat(32))],
            })],
        );
        let p = param_gram(
            "P",
            vec![prod_if(
                num(0x00),
                cmp(SpecTecCmpOp::Ge, var_exp("N"), nat(0)),
            )],
        );
        let (cfg, rep) = lower_recognition(&[a, p], &["A"]);
        assert_eq!(cfg.validate(), Ok(()));
        // Exactly one P@32 minted despite two references.
        assert_eq!(rep.mono_instances, 1);
        assert!(cfg.lookup("P@32").is_some());
    }

    #[test]
    fn param_guard_premise_drops_branch_exactly() {
        // A(N) → 0x00       if N > 7
        //      | 0x01       if N < 4
        // At N = 5 the first guard holds, the second fails ⇒ only 0x00 lowers.
        let guard_gt7 = prod_if(num(0x00), cmp(SpecTecCmpOp::Gt, var_exp("N"), nat(7)));
        let guard_lt4 = prod_if(num(0x01), cmp(SpecTecCmpOp::Lt, var_exp("N"), nat(4)));
        let a = param_gram("A", vec![guard_gt7, guard_lt4]);
        // Root that instantiates A at N = 8 (8 > 7 true, 8 < 4 false).
        let root = gram("R", vec![prod(var_arg("A", nat(8)))]);
        let (cfg, rep) = lower_recognition(&[root, a], &["R"]);
        assert_eq!(cfg.validate(), Ok(()));
        let ai = cfg.lookup("A@8").unwrap();
        // Only the 0x00 branch survives (the N<4 guard evaluated false).
        assert!(cfg.naive_parse(ai, &[0x00]));
        assert!(!cfg.naive_parse(ai, &[0x01]), "N<4 branch dropped exactly");
        // No `premises_dropped` counted — both guards are param-only (evaluated,
        // not over-approximated).
        assert_eq!(rep.premises_dropped, 0);
    }

    #[test]
    fn value_premise_dropped_over_approx() {
        // A(N) → 0x00   if n < 128  and  N > 7
        // `n` is a captured value (input-value premise: dropped + counted);
        // `N > 7` is a param-guard (evaluated true at N=32, keeps the branch).
        // The `N > 7` guard also makes A param-dependent, so it is
        // monomorphised into A@32 rather than resolved as a bare ref.
        let a = param_gram(
            "A",
            vec![
                prod_if(num(0x00), cmp(SpecTecCmpOp::Lt, var_exp("n"), nat(128))),
                prod_if(num(0x01), cmp(SpecTecCmpOp::Gt, var_exp("N"), nat(7))),
            ],
        );
        let root = gram("R", vec![prod(var_arg("A", nat(32)))]);
        let (cfg, rep) = lower_recognition(&[root, a], &["R"]);
        let ai = cfg.lookup("A@32").unwrap();
        // The value-premise branch is kept (over-approx) and the param-guard
        // branch holds at N=32, so A@32 accepts both bytes.
        assert!(cfg.naive_parse(ai, &[0x00]), "value premise dropped, kept");
        assert!(cfg.naive_parse(ai, &[0x01]), "N>7 guard holds at N=32");
        // At least the instance's value premise was dropped + counted. (The bare
        // `A` closure NT also drops it, so the total is ≥ 1.)
        assert!(rep.premises_dropped >= 1);
    }

    #[test]
    fn under_mode_byte_identical_on_corpus() {
        // Recognition mode is purely additive: Under-mode coverage is unchanged.
        let cov = coverage();
        assert_eq!(cov.count(Coverage::Full), 48, "Under full count pinned");
        assert_eq!(cov.count(Coverage::Partial), 8);
        assert_eq!(cov.count(Coverage::None), 33);
    }

    /// THE RECOGNITION-MODE COVERAGE RATCHET (separate from `coverage_ratchet`).
    /// Pins the M6 + grammar-valued-monomorphisation jump; raise only when
    /// recognition lowering genuinely improves.
    #[test]
    fn recognition_coverage_ratchet() {
        let cov = coverage_recognition();
        assert_eq!(cov.total, 89, "B* grammar count (mode-independent)");

        // The recognition-mode jump over Under mode: 48/8/33 → 60/7/22 (M6)
        // → 84/3/2 (grammar-valued params + iter-premise drop + attr fold).
        assert_eq!(cov.count(Coverage::Full), 84, "recognition full");
        assert_eq!(cov.count(Coverage::Partial), 3, "recognition partial");
        assert_eq!(cov.count(Coverage::None), 2, "recognition none");
        assert_eq!(
            cov.count(Coverage::Full) + cov.count(Coverage::Partial) + cov.count(Coverage::None),
            cov.total,
        );

        // LEB128 wrappers now lower Full (they skipped as None under Under mode).
        for name in ["Bu32", "Bu64", "Bs33", "BfN"] {
            assert_eq!(
                cov.of(name),
                Some(Coverage::Full),
                "{name} lowers Full in recognition mode",
            );
        }
        // The whole-module chain lowers Full: `Bmodule`, every section grammar,
        // and the `Blist`-consuming leaf grammars (grammar-valued
        // monomorphisation + iterated-premise drop + section-id attr fold).
        for name in [
            "Bmodule",
            "Btypesec",
            "Bimportsec",
            "Bfuncsec",
            "Btablesec",
            "Bmemsec",
            "Btagsec",
            "Bglobalsec",
            "Bexportsec",
            "Bstartsec",
            "Belemsec",
            "Bdatacntsec",
            "Bcodesec",
            "Bdatasec",
            "Bcustomsec",
            "Bfunc",
            "Bcode",
            "Bdata",
            "Belem",
            "Bname",
            "Bresulttype",
        ] {
            assert_eq!(cov.of(name), Some(Coverage::Full), "{name} Full");
        }
        // The *generic* parametric grammars stay honest: rooted alone (no
        // ground call site) their open-param productions cannot lower. BuN /
        // BsN / Bsection_ are Partial (a premise-free / Eps production lowers,
        // the open-param one skips); BiN / Blist are None. Their coverage is
        // realised through instances (`BuN@32`, `Blist@…`) at call sites.
        for name in ["BuN", "BsN", "Bsection_"] {
            assert_eq!(cov.of(name), Some(Coverage::Partial), "{name} partial");
        }
        for name in ["BiN", "Blist"] {
            assert_eq!(cov.of(name), Some(Coverage::None), "{name} generic-dead");
        }
        // Every `*idx` (Bu32 wrappers) is Full.
        for name in [
            "Bfuncidx",
            "Btypeidx",
            "Bglobalidx",
            "Blocalidx",
            "Bmemidx",
            "Btableidx",
            "Blabelidx",
            "Bdataidx",
            "Belemidx",
        ] {
            assert_eq!(cov.of(name), Some(Coverage::Full), "{name} idx Full");
        }
    }

    #[test]
    fn recognition_whole_corpus_never_panics() {
        let grammars = crate::grammar::wasm3_binary();
        // Each grammar as a singleton root.
        for g in &grammars {
            let (cfg, _report) = lower_recognition(&grammars, &[g.name.as_str()]);
            assert_eq!(cfg.validate(), Ok(()), "{} validates (recognition)", g.name);
        }
        // The entire B* universe at once.
        let roots: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
        let (cfg, report) = lower_recognition(&grammars, &roots);
        assert_eq!(cfg.validate(), Ok(()));
        // With `Bmodule` lowering, the recognition corpus contains exactly one
        // kind of left-recursion finding: a synthetic star over a **nullable**
        // body (`Bcustomsec*` — `Bcustomsec` is genuinely nullable per the
        // spec, via `Bsection_`'s ε production). The named-grammar corpus
        // stays left-recursion-free; the top-down tactic remains complete on
        // nullable-body stars (a star derivation never needs a same-span
        // re-entry: ε-contributions can be dropped).
        if let Some(cycle) = cfg.left_recursion() {
            for nt in &cycle {
                let name = cfg.nt_name(*nt).unwrap_or("");
                assert!(
                    name.contains("$star") || name.contains("$plusStar"),
                    "left-recursion only through nullable-body star synthetics, got {name}",
                );
            }
        }
        // The monomorphiser fired and the LEB128 wrappers are present.
        assert!(report.mono_instances >= 1);
        assert!(cfg.lookup("BuN@32").is_some());
        assert_eq!(report.attrs_constrained, 0, "no constraint attrs");
    }

    #[test]
    fn recognition_report_display_shows_counters() {
        let gs = crate::grammar::wasm3_binary();
        let (_cfg, report) = lower_recognition(&gs, &["Bu32"]);
        let s = format!("{report}");
        assert!(s.contains("recognition:"), "{s}");
        assert!(s.contains("mono instances"), "{s}");
    }

    fn prod_if(sym: SpecTecSym, e: SpecTecExp) -> SpecTecProd {
        SpecTecProd::Prod {
            ps: Vec::new(),
            g: sym,
            e: SpecTecExp::Bool { b: true },
            prs: vec![spectec_ast::SpecTecPrem::If { e }],
        }
    }

    // ========================================================================
    // Grammar-valued parameter monomorphisation (whole-module chain).
    // ========================================================================

    /// Synthetic `Blist`-shape: `L(el, BX) → 0x10 BX` instantiated at two
    /// different grammar arguments mints two distinct, deduped instances.
    #[test]
    fn monomorphises_grammar_valued_params() {
        let mut l = gram(
            "L",
            vec![prod(SpecTecSym::Seq {
                gs: vec![num(0x10), var("BX")],
            })],
        );
        l.params = vec![
            SpecTecParam::Typ { x: "el".into() },
            SpecTecParam::Gram {
                x: "BX".into(),
                t: spectec_ast::SpecTecTyp::Var {
                    x: "el".into(),
                    as1: Vec::new(),
                },
            },
        ];
        let gram_arg = |target: &str| SpecTecArg::Gram {
            g: SpecTecSym::Var {
                x: target.into(),
                as1: Vec::new(),
            },
        };
        let typ_arg = |t: &str| SpecTecArg::Typ {
            t: spectec_ast::SpecTecTyp::Var {
                x: t.into(),
                as1: Vec::new(),
            },
        };
        let root = gram(
            "R",
            vec![
                prod(SpecTecSym::Var {
                    x: "L".into(),
                    as1: vec![typ_arg("a"), gram_arg("A")],
                }),
                prod(SpecTecSym::Var {
                    x: "L".into(),
                    as1: vec![typ_arg("b"), gram_arg("B")],
                }),
                // Same instance as the first — must dedup on the full key.
                prod(SpecTecSym::Var {
                    x: "L".into(),
                    as1: vec![typ_arg("a"), gram_arg("A")],
                }),
            ],
        );
        let a = gram("A", vec![prod(num(0x0A))]);
        let b = gram("B", vec![prod(num(0x0B))]);
        // Under mode: grammar-valued args still skip (unchanged).
        let (_c, ur) = lower(&[root.clone(), l.clone(), a.clone(), b.clone()], &["R"]);
        assert_eq!(ur.mono_instances, 0, "Under mode never monomorphises");
        assert_eq!(ur.grammars.get("R"), Some(&Coverage::None));

        // Recognition mode: two deduped instances, each recognising its arm.
        let (cfg, rep) = lower_recognition(&[root, l, a, b], &["R"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(rep.mono_instances, 2, "L@a,A and L@b,B, third ref deduped");
        assert_eq!(rep.grammars.get("R"), Some(&Coverage::Full));
        let r = cfg.lookup("R").unwrap();
        assert!(cfg.naive_parse(r, &[0x10, 0x0A]));
        assert!(cfg.naive_parse(r, &[0x10, 0x0B]));
        assert!(!cfg.naive_parse(r, &[0x10, 0x0C]));
    }

    /// The parameter-equality attr fold: `[N]:Bbyte` under a ground instance
    /// binding lowers to the literal byte `N` (exact), not a full-range byte.
    #[test]
    fn attr_over_bbyte_folds_to_literal_under_binding() {
        // S(N) → [N]:Bbyte 0x02, referenced at S(7).
        let byte_attr = SpecTecSym::Attr {
            e: SpecTecExp::Var { id: "N".into() },
            g1: Box::new(var("Bbyte")),
        };
        // param_gram adds the Exp param `N`.
        let s = param_gram(
            "S",
            vec![prod(SpecTecSym::Seq {
                gs: vec![byte_attr, num(0x02)],
            })],
        );
        let bbyte = gram(
            "Bbyte",
            vec![prod(SpecTecSym::Range {
                g1: Box::new(num(0x00)),
                g2: Box::new(num(0xFF)),
            })],
        );
        let root = gram("R", vec![prod(var_arg("S", nat(7)))]);
        let (cfg, rep) = lower_recognition(&[root, s, bbyte], &["R"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(rep.attrs_folded, 1, "the id byte folded");
        let r = cfg.lookup("R").unwrap();
        assert!(cfg.naive_parse(r, &[0x07, 0x02]), "the ground id byte");
        assert!(
            !cfg.naive_parse(r, &[0x08, 0x02]),
            "a wrong id byte is rejected (exact fold, not a stripped capture)",
        );
    }

    /// An `Iter`-wrapped `if` premise over production-locals (`Bmodule`'s
    /// data-count / func-code correlation shape) is dropped as an input-value
    /// premise in recognition mode (counted), and still skips under Under mode.
    #[test]
    fn iterated_value_premise_dropped_in_recognition() {
        let iter_prem = spectec_ast::SpecTecPrem::Iter {
            pr1: Box::new(spectec_ast::SpecTecPrem::If {
                e: cmp(SpecTecCmpOp::Eq, var_exp("n"), var_exp("m")),
            }),
            it: SpecTecIter::List,
            xes: vec![spectec_ast::SpecTecIterExp::Dom {
                x: "n".into(),
                e: SpecTecExp::Var { id: "ns".into() },
            }],
        };
        let g = Grammar {
            prods: vec![SpecTecProd::Prod {
                ps: Vec::new(),
                g: num(0x2A),
                e: SpecTecExp::Bool { b: true },
                prs: vec![iter_prem],
            }],
            ..gram("A", Vec::new())
        };
        let (_c, ur) = lower(&[g.clone()], &["A"]);
        assert_eq!(ur.grammars.get("A"), Some(&Coverage::None), "Under skips");
        let (cfg, rep) = lower_recognition(&[g], &["A"]);
        assert_eq!(rep.grammars.get("A"), Some(&Coverage::Full));
        assert_eq!(rep.premises_dropped, 1, "iterated value premise counted");
        let a = cfg.lookup("A").unwrap();
        assert!(cfg.naive_parse(a, &[0x2A]));
    }

    /// **The whole-module differential** (the kernel-side end-to-end proof
    /// lives in `covalence-init/tests/cfg_grammar.rs`): the recognition-mode
    /// `Bmodule` closure accepts the real 27-byte binary for
    /// `(module (func (result i32) i32.const 42))` and refuses corruptions the
    /// recognizer can genuinely see. Also documents, as a *pinned caveat*, an
    /// over-approximation this closure inherits: dropping the final byte is
    /// still accepted, because section `len` premises are dropped and `ListN`
    /// vectors are star-widened, so the func section's `typeidx*` swallows the
    /// dangling tail. Recognition ≠ validation.
    #[test]
    fn bmodule_recognition_differential() {
        let gs = crate::grammar::wasm3_binary();
        let (cfg, rep) = lower_recognition(&gs, &["Bmodule"]);
        assert_eq!(cfg.validate(), Ok(()));
        assert_eq!(
            rep.grammars.get("Bmodule"),
            Some(&Coverage::Full),
            "Bmodule lowers Full in recognition mode",
        );
        let m = cfg.lookup("Bmodule").unwrap();
        let module = wasm_module_i32_const_42();
        assert!(cfg.naive_parse(m, &module), "real module accepted");
        // Magic/version alone: the empty module.
        assert!(
            cfg.naive_parse(m, &[0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]),
            "empty module accepted",
        );
        // Genuine refusals: corrupt magic; an invalid section id right after
        // the version (before any `0x00` byte can open a custom section).
        let mut bad_magic = module.clone();
        bad_magic[0] = 0x01;
        assert!(!cfg.naive_parse(m, &bad_magic), "bad magic refused");
        let mut bad_secid = module.clone();
        bad_secid[8] = 0xFF; // type-section id 0x01 → invalid id 0xFF
        assert!(
            !cfg.naive_parse(m, &bad_secid),
            "invalid section id refused"
        );
        // PINNED CAVEATS (over-approximations, not bugs) — the two byte-sinks
        // a recognition-mode `Bmodule` inherits:
        //  1. truncating the final `end` opcode still recognises: section
        //     `len` premises are dropped and `ListN` vectors star-widened, so
        //     the func section's `typeidx*` swallows the low-LEB tail;
        //  2. appending a dangling `0x80` still recognises: the parse can
        //     re-split so a *custom section* opens at an earlier `0x00` byte,
        //     and `Bcustom`'s `byte*` accepts arbitrary bytes.
        assert!(
            cfg.naive_parse(m, &module[..module.len() - 1]),
            "known over-approximation: truncated tail swallowed by widened vectors",
        );
        let mut dangling = module.clone();
        dangling.push(0x80);
        assert!(
            cfg.naive_parse(m, &dangling),
            "known over-approximation: custom-section byte* is a universal sink",
        );
    }

    /// The real 27-byte binary encoding of
    /// `(module (func (result i32) i32.const 42))`, byte by byte.
    pub(crate) fn wasm_module_i32_const_42() -> Vec<u8> {
        vec![
            0x00, 0x61, 0x73, 0x6D, // magic `\0asm`
            0x01, 0x00, 0x00, 0x00, // version 1
            0x01, 0x05, // type section: id 1, size 5
            0x01, // — 1 rectype
            0x60, 0x00, 0x01, 0x7F, // — functype [] → [i32]
            0x03, 0x02, // func section: id 3, size 2
            0x01, 0x00, // — 1 func, typeidx 0
            0x0A, 0x06, // code section: id 10, size 6
            0x01, // — 1 code entry
            0x04, // — body size 4
            0x00, // — 0 local groups
            0x41, 0x2A, // — i32.const 42
            0x0B, // — end
        ]
    }
}
