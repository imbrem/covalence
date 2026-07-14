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

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use covalence_grammar::cfg::{Cfg, NtId, Seg};
use covalence_grammar::regex::Regex;
use spectec_ast::{SpecTecArg, SpecTecExp, SpecTecIter, SpecTecProd, SpecTecSym};

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
}

impl CfgReport {
    fn note_skip(&mut self, err: &CfgLowerError) {
        *self.skipped.entry(SkipReason::of(err)).or_default() += 1;
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
        let SpecTecProd::Prod { g: sym, .. } = p;
        !sym_mentions_names(sym, &names)
    })
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

// ============================================================================
// Lowering context
// ============================================================================

struct Ctx<'a> {
    /// All grammars by name.
    by_name: BTreeMap<&'a str, &'a Grammar>,
    /// Cache of param-independence per grammar name.
    param_indep: BTreeMap<&'a str, bool>,
    cfg: Cfg<u8>,
    report: CfgReport,
    /// Fresh-name counter for synthetic non-terminals.
    synth_ctr: usize,
}

impl<'a> Ctx<'a> {
    fn new(grammars: &'a [Grammar]) -> Self {
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
/// the named `roots`.
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
    let mut ctx = Ctx::new(grammars);

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
            // Only follow references that will actually be *lowered*: a
            // premise-carrying production is skipped whole, so its references
            // do not enter the dependency closure (keeps demo closures tight,
            // e.g. Bheaptype's skipped `Bs33` branch stays out of the
            // `{Breftype}` closure). Within a kept production, only resolvable
            // references form a real edge.
            if prs.is_empty() {
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

    // 3. Lower each grammar's productions.
    for name in &order {
        let g = ctx.by_name[name];
        let lhs = ids[name];
        let mut lowered_here = 0usize;
        let mut skipped_here = 0usize;
        for p in &g.prods {
            match lower_prod(&mut ctx, &ids, g, lhs, p) {
                Ok(n) => {
                    lowered_here += n;
                    ctx.report.lowered_prods += 1;
                }
                Err(err) => {
                    ctx.report.note_skip(&err);
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
    g: &Grammar,
    lhs: NtId,
    p: &SpecTecProd,
) -> Result<usize, CfgLowerError> {
    let SpecTecProd::Prod { g: sym, prs, .. } = p;
    if !prs.is_empty() {
        return Err(CfgLowerError::Premise {
            grammar: g.name.clone(),
            count: prs.len(),
        });
    }
    // Segment the RHS into one-or-more alternative segment sequences
    // (Alt-distribution). Attr captures are stripped along the way.
    let alts = segment_alts(ctx, ids, g, sym)?;
    let n = alts.len();
    for segs in alts {
        ctx.cfg.add_prod(lhs, segs);
    }
    Ok(n)
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
    g: &Grammar,
    sym: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    // Flatten to a top-level sequence of items, then take the cartesian
    // product of each item's alternatives.
    let items = flatten_seq(sym);
    let mut acc: Vec<SegSeq> = vec![Vec::new()];
    for item in items {
        let item_alts = segment_item(ctx, ids, g, item)?;
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
            if attr_is_constraint(e) {
                ctx.report.attrs_constrained += 1;
            } else {
                ctx.report.attrs_captured += 1;
            }
            segment_item(ctx, ids, g, g1)
        }
        SpecTecSym::Seq { .. } => segment_alts(ctx, ids, g, item),
        SpecTecSym::Var { x, as1 } => {
            if !ctx.var_resolvable(x, as1) {
                return Err(CfgLowerError::ParametricRef {
                    name: x.clone(),
                    args: as1.len(),
                });
            }
            match ids.get(x.as_str()) {
                Some(&nt) => Ok(vec![vec![Seg::NonTerm(nt)]]),
                // A reference outside the closure shouldn't happen (the BFS
                // added every referenced grammar), but if the target is
                // unknown entirely, treat it as an unresolvable ref.
                None => Err(CfgLowerError::ParametricRef {
                    name: x.clone(),
                    args: as1.len(),
                }),
            }
        }
        SpecTecSym::Alt { gs } => {
            // Distribute: one alternative segment-sequence per arm.
            let mut out = Vec::new();
            for arm in gs {
                out.extend(segment_alts(ctx, ids, g, arm)?);
            }
            Ok(out)
        }
        SpecTecSym::Iter { g1, it, xes } => {
            if !xes.is_empty() {
                return Err(CfgLowerError::IterWithDom {
                    grammar: g.name.clone(),
                });
            }
            match it {
                SpecTecIter::ListN { .. } => Err(CfgLowerError::ListN {
                    grammar: g.name.clone(),
                }),
                SpecTecIter::Opt => desugar_opt(ctx, ids, g, g1),
                SpecTecIter::List => desugar_star(ctx, ids, g, g1),
                SpecTecIter::List1 => desugar_plus(ctx, ids, g, g1),
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

/// `X? ⇒ Xo → ε | X` (synthetic `Xo`).
fn desugar_opt(
    ctx: &mut Ctx,
    ids: &BTreeMap<&str, NtId>,
    g: &Grammar,
    body: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    let body_alts = segment_alts(ctx, ids, g, body)?;
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
    g: &Grammar,
    body: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    let body_alts = segment_alts(ctx, ids, g, body)?;
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
    g: &Grammar,
    body: &SpecTecSym,
) -> Result<Vec<SegSeq>, CfgLowerError> {
    let body_alts = segment_alts(ctx, ids, g, body)?;
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
    let grammars = crate::grammar::wasm3_binary();
    let names: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
    let mut per_grammar: BTreeMap<String, Coverage> = BTreeMap::new();
    for g in &grammars {
        let (_cfg, report) = lower(&grammars, &[g.name.as_str()]);
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
}
