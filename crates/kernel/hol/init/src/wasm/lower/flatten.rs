//! **Condition flattening** — compile a SpecTec `If` condition (and, after
//! [`super::else_`] preprocessing, an `Else`) into [`super::LowerPrem`]s:
//! function calls become `fn.<f>` graph premises ([`super::fn_graph`]),
//! structural operators become `ev.*` evaluator premises
//! ([`super::evalrel`], emitted on demand), store/struct/list **writes**
//! (`Upd`/`Ext` along `Dot`/`Idx` paths) become `ev.upd.*`/`ev.ext.*` write
//! premises ([`super::evalrel::upd_ext_families`] — in both encoding modes;
//! `Slice` paths refuse), pure constructor equalities become
//! syntactic `Side` equations over encodings, and value-fragment arithmetic
//! becomes real arithmetic `Side` antecedents over **bare** numeric
//! metavariables. See `notes/vibes/logics/spectec-total-load.md` legs 3 & 5.
//!
//! ## The numeric-metavar discipline
//!
//! A rule metavariable `n` that a condition uses *arithmetically* appears in
//! judgement spines as `app(st$c$num.nat, st$v$n)` (the **wrapped** form —
//! exactly the encoding of a numeric literal with the bare `∀`-bound `nat`
//! variable as child) and in arithmetic `Side` antecedents as the **bare**
//! `st$v$n`. Instantiation currency for such metavars is then the bare
//! numeral, which simultaneously yields `encode(Num k)` in the spine and a
//! closed, kernel-reducible antecedent. Non-numeric metavars stay bare leaves
//! `st$v$x` instantiated with full encodings — the two currencies produce
//! **identical ground judgement terms**, so mixed-classification rules of one
//! relation still meet on the same keys. Numeric-ness is decided *per rule* by
//! a pre-scan ([`Flattener::begin_rule`]) so every occurrence agrees.
//!
//! ## Soundness frame
//!
//! Nothing here weakens: every antecedent emitted is at least as strong as the
//! SpecTec premise it lowers (evaluation premises are hoisted conjunctively —
//! extra strength; `ev.*`/`fn.*` judgements are derivable only for genuine
//! evaluations). Equations over encodings ([`Flattener::cond_eq`]) are
//! refl-dischargeable exactly at genuinely-equal instances **because the
//! encoding is injective at every encoded position** (`encode.rs` module docs;
//! iteration binders/domains/`ListN` bounds and `upd`/`ext` path
//! sub-expressions are part of the encoding since review R1-F1/F2 — the sole
//! residual coarse position, non-expression `call` arguments, never reaches an
//! equation side undistinguished because `Call`s in condition positions are
//! flattened to `fn.*` premises keyed on those arguments). An equation side
//! that still contains a **value-dead** operator spine (`Slice`, `Cvt` — nodes
//! the cond-mode encoder leaves coarse while ground values encode as plain
//! values, so the Side could never be discharged at a genuine point) is
//! censused as `cond.slice` / `cond.coarse-eq` instead of silently loading a
//! dead equation (review R3-F1). A condition shape that cannot be expressed
//! becomes an [`super::opaque`] premise — the rule loads, cannot fire, and is
//! **counted** ([`CensusReport`]), never dropped.

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::subst::subst_free;
use covalence_core::{Result, Term, Var};
use covalence_hol_eval::derived::DerivedRules;
use covalence_hol_eval::{EvalThm as Thm, mk_bool, mk_nat};
use covalence_spectec::ast::{
    SpecTecArg, SpecTecBinOp, SpecTecCmpOp, SpecTecDef, SpecTecExp, SpecTecExpField, SpecTecIter,
    SpecTecIterExp, SpecTecNum, SpecTecNumTyp, SpecTecOpTyp, SpecTecPath, SpecTecPrem, SpecTecRule,
    SpecTecUnOp,
};

use super::super::encode::{
    self, app, con, encode_exp, metavar, metavar_name, mixop_key, phi, tag,
};
use super::super::syntax::CaseCatalogue;
use super::decision::{DecisionAnswer, DecisionLowerer, DecisionRequest, OpaqueDecisions};
#[cfg(test)]
use super::else_::preprocess_else;
use super::else_::{ElseStatus, negate, preprocess_else_with_catalogue};
use super::evalrel::{self, ev_graph, wrap_nat};
use super::sortguard;
use super::star::{self, IterNote, StarSite};
use super::{Clause, CondFlattener, Flattened, LowerPrem, fn_graph, opaque};
use crate::init::ext::{TermExt, ThmExt};
use crate::init::nat;

// ===========================================================================
// The flattener
// ===========================================================================

/// The real [`CondFlattener`]: catalogue-gated evaluator relations, a fresh
/// metavariable counter, an on-demand (deduplicated) evaluator-clause
/// accumulator, and the per-rule numeric-metavariable set.
pub struct Flattener<'a> {
    cat: &'a CaseCatalogue,
    /// Global fresh counter (names `%f<k>` — `%` cannot occur in SpecTec ids).
    fresh: usize,
    /// On-demand evaluator clauses (deduplicated by `ev_keys`).
    ev_clauses: Vec<Clause>,
    ev_keys: BTreeSet<String>,
    /// `ev.neq` pairs emitted (a subset of `ev_keys`, counted for the census).
    neq_pairs: usize,
    /// Per-rule: metavariables under the numeric discipline.
    numeric: BTreeSet<String>,
    /// Per-rule: opaque-premise reasons emitted while flattening.
    opaque_reasons: Vec<String>,
    /// Soft census: `Call`s left coarsely encoded under an `Iter` spine.
    pub iter_embedded_calls: usize,
}

impl<'a> Flattener<'a> {
    pub fn new(cat: &'a CaseCatalogue) -> Self {
        Flattener {
            cat,
            fresh: 0,
            ev_clauses: Vec::new(),
            ev_keys: BTreeSet::new(),
            neq_pairs: 0,
            numeric: BTreeSet::new(),
            opaque_reasons: Vec::new(),
            iter_embedded_calls: 0,
        }
    }

    /// The per-rule opaque reasons recorded since
    /// [`CondFlattener::begin_rule`] (empty ⟺ the rule flattened fully).
    pub fn take_opaque_reasons(&mut self) -> Vec<String> {
        std::mem::take(&mut self.opaque_reasons)
    }

    /// Drain the accumulated evaluator clauses (call once, after lowering).
    pub fn drain_ev_clauses(&mut self) -> Vec<Clause> {
        std::mem::take(&mut self.ev_clauses)
    }

    /// Number of `ev.neq` tag-pair clauses emitted so far.
    pub fn neq_pairs(&self) -> usize {
        self.neq_pairs
    }

    /// Whether a metavariable is under the numeric discipline for this rule.
    pub fn is_numeric(&self, id: &str) -> bool {
        self.numeric.contains(id)
    }

    fn fresh_var(&mut self, fl: &mut Flattened) -> String {
        let name = format!("%f{}", self.fresh);
        self.fresh += 1;
        fl.new_metavars.push(name.clone());
        name
    }

    fn opaque_prem(&mut self, reason: &str, body: Term) -> Result<LowerPrem> {
        self.opaque_reasons.push(reason.to_string());
        Ok(LowerPrem::Judgement(opaque(reason, body)?))
    }

    /// Emit an evaluator-clause family once (deduplicated by `key`); returns
    /// whether this call actually emitted.
    fn emit_ev(&mut self, key: &str, build: impl FnOnce() -> Result<Vec<Clause>>) -> Result<bool> {
        if self.ev_keys.insert(key.to_string()) {
            self.ev_clauses.extend(build()?);
            return Ok(true);
        }
        Ok(false)
    }

    // =======================================================================
    // Numeric pre-scan
    // =======================================================================

    /// Mark every metavariable that appears in an arithmetic position (see the
    /// module docs). Skips `Iter` subtrees (iteration variables' currency is
    /// whole lists, never bare numerals).
    fn scan_numeric(&mut self, e: &SpecTecExp) {
        use SpecTecExp as E;
        match e {
            // A supported partial conversion denotes a natural even when it
            // is nested below a structural value operation (notably the
            // byte-count operand of `Slice`).  Discover its payload
            // variables here; waiting for an arithmetic comparison misses
            // the `ibytes_(...) = mem.BYTES[start : count]` conditions.
            E::Cvt { .. } if shape_nat_cvt(e) => self.mark_arith(e),
            E::Iter { .. } => {}
            E::Bin { op, t, e1, e2 } if is_nat_arith(op, t) => {
                self.mark_arith(e1);
                self.mark_arith(e2);
            }
            E::Cmp { op, t, e1, e2 } => {
                if cmp_is_nat_arith(op, t, e1, e2) {
                    self.mark_arith(e1);
                    self.mark_arith(e2);
                } else if (matches!(
                    op,
                    SpecTecCmpOp::Lt | SpecTecCmpOp::Gt | SpecTecCmpOp::Le | SpecTecCmpOp::Ge
                ) && matches!(t, SpecTecOpTyp::Num(SpecTecNumTyp::Rat)))
                    || (matches!(op, SpecTecCmpOp::Eq | SpecTecCmpOp::Ne)
                        && shape_rat_nat(e1)
                        && shape_rat_nat(e2))
                {
                    self.mark_arith(e1);
                    self.mark_arith(e2);
                } else {
                    self.scan_numeric(e1);
                    self.scan_numeric(e2);
                }
            }
            other => {
                for c in children(other) {
                    self.scan_numeric(c);
                }
            }
        }
    }

    /// Mark variables along an arithmetic spine; non-arithmetic subtrees
    /// (list/call/projection innards) fall back to the generic scan.
    fn mark_arith(&mut self, e: &SpecTecExp) {
        use SpecTecExp as E;
        match e {
            E::Var { id } => {
                self.numeric.insert(id.clone());
            }
            E::Num { .. } => {}
            E::Bin { op, t, e1, e2 } if is_nat_arith(op, t) => {
                self.mark_arith(e1);
                self.mark_arith(e2);
            }
            // Inside an explicit numeric conversion, Int/Rat arithmetic is
            // still ultimately carried by bare natural witnesses for the
            // supported conversion normal forms.
            E::Bin {
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Int | SpecTecNumTyp::Rat),
                e1,
                e2,
                ..
            } => {
                self.mark_arith(e1);
                self.mark_arith(e2);
            }
            E::Cvt { e1, .. } => self.mark_arith(e1),
            // Evaluated-to-nat nodes: their innards are structural.
            E::Len { e1 } => self.scan_numeric(e1),
            E::Call { .. } | E::Uncase { .. } | E::Proj { .. } | E::Dot { .. } | E::Idx { .. } => {
                for c in children(e) {
                    self.scan_numeric(c);
                }
            }
            other => self.scan_numeric(other),
        }
    }

    // =======================================================================
    // Judgement-position encoding (`expr`) — the encoder with call flattening,
    // numeric wrapping and (in condition mode) structural-operator flattening
    // =======================================================================

    fn enc(&mut self, e: &SpecTecExp, mode: Mode, fl: &mut Flattened) -> Result<Term> {
        use SpecTecExp as E;
        // The canonical view (Sub-strip + identity-iteration collapse) —
        // `encode::shape`'s preprocessing, mirrored so mixed `enc`/`encode_exp`
        // terms (and the `Dec` graph leg's collapsed patterns) meet on the
        // same keys.
        let e = encode::canon(e);
        match e {
            E::Var { id } => {
                let v = metavar(id);
                if self.is_numeric(id) {
                    wrap_nat(v)
                } else {
                    Ok(v)
                }
            }
            // Literals and other leaves: exactly the shared encoding.
            E::Bool { .. } | E::Num { .. } | E::Text { .. } => encode_exp(e),
            // Real nat arithmetic in a spine: evaluate through a fresh numeric
            // metavar pinned by an arithmetic Side (`r = e`), so ground keys
            // carry real numerals instead of coarse `bin.*` nodes.
            E::Bin { op, t, .. } if is_nat_arith(op, t) && self.can_ndenote(e) => {
                let t = self.ndenote(e, fl)?;
                let r = self.fresh_var(fl);
                self.numeric.insert(r.clone());
                fl.prems.push(LowerPrem::Side(metavar(&r).equals(t)?));
                wrap_nat(metavar(&r))
            }
            E::Call { x, as1 } => self.flatten_call(x, as1, mode, fl),
            // Exact natural→integer conversion in condition position. The
            // integer encoding is sign/magnitude, so a natural is simply the
            // non-negative case with its real-nat denotation as magnitude.
            E::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Int,
                e1,
            } if mode == Mode::Cond && self.can_ndenote(e1) => {
                evalrel::wrap_int(0, self.ndenote(e1, fl)?)
            }
            // Exact supported partial conversions back to Nat, using the
            // same wrapped-numeric currency as other evaluated results.
            E::Cvt { .. } if mode == Mode::Cond && shape_nat_cvt(e) => {
                wrap_nat(self.ndenote(e, fl)?)
            }
            // Exact identity ListN: `(x)^(n) with x <- xs` is `xs`, together
            // with the elaboration constraint `|xs| = n`. Unlike the plain
            // List/Opt identity collapse, dropping this bound would
            // over-approximate; expressing it through `ev.len` makes the
            // representation exact in patterns, call arguments, and results.
            E::Iter {
                e1,
                it: SpecTecIter::ListN { e: bounds, .. },
                xes,
            } if matches!(&**e1, E::Var { id } if xes.len() == 1
                    && matches!(&xes[0], SpecTecIterExp::Dom { x, .. } if x == id))
                && bounds.len() == 1 =>
            {
                // A plain ListN bound variable is intrinsically natural even
                // if it has no separate arithmetic occurrence for the
                // clause-level pre-scan to discover.
                if let E::Var { id } = &bounds[0] {
                    self.numeric.insert(id.clone());
                }
                if !self.can_ndenote(&bounds[0]) {
                    return self.wrap_numeric_in(encode_exp(e)?);
                }
                let SpecTecIterExp::Dom { e: domain, .. } = &xes[0];
                let domain = self.enc(domain, mode, fl)?;
                let bound = self.ndenote(&bounds[0], fl)?;
                self.emit_ev("len", evalrel::len_clauses)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "len",
                    &[domain.clone()],
                    &wrap_nat(bound)?,
                )?));
                Ok(domain)
            }
            // Iteration spines without an evaluator interpretation remain
            // self-contained **syntactic keys**. Call-bearing maps and
            // indexed ListN generators are instead lowered relationally in
            // every position: their per-element premises live inside the
            // evaluator step clause, never hoisted once at rule level.
            // Residual raw spines are identical in judgement and condition
            // positions, and injective since the
            // binder/domain/bound restoration (`encode::shape`, R1-F1).
            // Numeric metavariables still get their spine wrap — applied by
            // substitution over the raw encoding, so a metavar used
            // arithmetically outside the spine carries ONE currency
            // everywhere (the mixed-currency iter-spine fix, R3-F3/R1-F3 —
            // `Step_read/vload-pack-val`'s `M`).
            E::Iter { e1, it, xes }
                if contains_call(e1)
                    || matches!(it, SpecTecIter::ListN { xo, .. }
                        if xes.is_empty() && !xo.is_empty())
                    || (mode == Mode::CallArg && !xes.is_empty()) =>
            {
                self.flatten_iter_map(e1, it, xes, fl)
            }
            E::Iter { .. } => {
                if contains_call(e) {
                    self.iter_embedded_calls += 1;
                }
                self.wrap_numeric_in(encode_exp(e)?)
            }
            // Structural operators: evaluator-flattened in condition mode,
            // coarse (baseline encoding) in judgement mode.
            E::Len { e1 } if mode == Mode::Cond => {
                let inner = self.enc(e1, mode, fl)?;
                let r = self.fresh_var(fl);
                self.numeric.insert(r.clone());
                self.emit_ev("len", evalrel::len_clauses)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "len",
                    &[inner],
                    &wrap_nat(metavar(&r))?,
                )?));
                wrap_nat(metavar(&r))
            }
            E::Uncase { e1, op } if mode == Mode::Cond => {
                let key = mixop_key(op);
                if !self.uncase_key_ok(&key) {
                    let body = encode_exp(e)?;
                    let prem = self.opaque_prem("cond.uncase-ambiguous", body)?;
                    fl.prems.push(prem);
                    let r = self.fresh_var(fl);
                    return Ok(metavar(&r));
                }
                let inner = self.enc(e1, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev(&format!("uncase.{key}"), || evalrel::uncase_clause(&key))?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    &format!("uncase.{key}"),
                    &[inner],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            E::Proj { e1, i } if mode == Mode::Cond && *i >= 0 => {
                let i = *i as usize;
                let inner = self.enc(e1, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev(&format!("proj.{i}"), || evalrel::proj_clauses(i))?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    &format!("proj.{i}"),
                    &[inner],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            E::Dot { e1, at } if mode == Mode::Cond => {
                let key = mixop_key(at);
                let inner = self.enc(e1, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev(&format!("dot.{key}"), || evalrel::dot_clauses(&key))?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    &format!("dot.{key}"),
                    &[inner],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            E::Idx { e1, e2 } if mode == Mode::Cond => {
                let list = self.enc(e1, mode, fl)?;
                let idx = self.enc(e2, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev("len", evalrel::len_clauses)?;
                self.emit_ev("idx", evalrel::idx_clauses)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "idx",
                    &[list, idx],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            E::Slice { e1, e2, e3 } if mode == Mode::Cond => {
                let list = self.enc(e1, mode, fl)?;
                let start = self.enc(e2, mode, fl)?;
                let count = self.enc(e3, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev("len", evalrel::len_clauses)?;
                self.emit_ev("cat", evalrel::cat_clauses)?;
                self.emit_ev("slice", evalrel::slice_clause)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "slice",
                    &[list, start, count],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            E::Unopt { e1 } if mode == Mode::Cond => {
                let inner = self.enc(e1, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev("unopt", evalrel::unopt_clause)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "unopt",
                    &[inner],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            // `Cat` flattens in condition positions AND in rule-conclusion
            // position (`Mode::Concl` — the Wave-G unblocking): a conclusion
            // `R(… val* ++ instr* …)` becomes `R(… r …)` with an `ev.cat`
            // premise, so the derivable instances carry the genuine
            // *flat-list* encoding instead of a coarse `cat` spine that no
            // real configuration matches. Faithful: `ev.cat` is exact at
            // genuine list points, so the conclusion instances are exactly
            // the encodings of the SpecTec instances (the same move as `Dec`
            // RHS result flattening, restricted to `Cat`).
            E::Cat { e1, e2 } if mode != Mode::Judgement => {
                let a = self.enc(e1, mode, fl)?;
                let b = self.enc(e2, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev("cat", evalrel::cat_clauses)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "cat",
                    &[a, b],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            // `Lift` (option→list) evaluates in condition/result positions
            // through the 2-clause `ev.lift` family — this is what lets the
            // `fn.binop_` DIV/REM graph clauses conclude the actual value
            // list (`lift($idiv_ …)`) that `Step_pure/binop-val`/`binop-trap`
            // consume.
            E::Lift { e1 } if mode == Mode::Cond => {
                let inner = self.enc(e1, mode, fl)?;
                let r = self.fresh_var(fl);
                self.emit_ev("lift", evalrel::lift_clauses)?;
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    "lift",
                    &[inner],
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            // Store/struct/list **writes**: `Upd`/`Ext` along a `Dot`/`Idx`
            // access path evaluate through the on-demand `ev.upd.*`/`ev.ext.*`
            // families ([`evalrel::upd_ext_families`] — schematic spine-rebuild
            // clauses, exact at genuine points), so a write produces the
            // *value* the chain consumes: `Dec` RHSs (`$with_table` …, via
            // `expr_result`), conditions comparing/consuming updated stores
            // (`Step_pure/vreplace_lane`'s `$inv_lanes_(…, l[i := …])`), and
            // `Dec`-leg call arguments (`$with_locals`' recursion) — hence
            // BOTH modes (the corpus has no `Upd`/`Ext` in rule conclusions
            // or `Rule` premises, so judgement-position keys are untouched).
            // Children always flatten in `Cond` mode: they feed the `ev.*`
            // premise, not the outer spine, and index/subject reads must
            // evaluate for the write clauses to fire. `Slice` paths decompose
            // the list through exact `ev.cat`/`ev.len` witnesses and rebuild
            // it around the replacement.
            E::Upd { e1, path, e2 } | E::Ext { e1, path, e2 }
                if evalrel::path_segs(path).is_some() =>
            {
                let op = if matches!(e, E::Upd { .. }) {
                    "upd"
                } else {
                    "ext"
                };
                let segs = evalrel::path_segs(path).expect("checked by the guard");
                let mut args = vec![self.enc(e1, Mode::Cond, fl)?];
                let mut idx_exprs = Vec::new();
                evalrel::path_index_exprs(path, &mut idx_exprs);
                for pe in idx_exprs {
                    args.push(self.enc(pe, Mode::Cond, fl)?);
                }
                args.push(self.enc(e2, Mode::Cond, fl)?);
                for (key, cls) in evalrel::upd_ext_families(op, &segs)? {
                    self.emit_ev(&key, || Ok(cls))?;
                }
                let r = self.fresh_var(fl);
                fl.prems.push(LowerPrem::Judgement(ev_graph(
                    &format!("{op}.{}", evalrel::segs_key(&segs)),
                    &args,
                    &metavar(&r),
                )?));
                Ok(metavar(&r))
            }
            // Everything else: the shared coarse encoding, with children
            // recursively flattened (same tags as `encode_exp`).
            E::Str { efs } => {
                let mut acc = con("struct");
                for SpecTecExpField::Field { at, e } in efs {
                    let field = app(
                        con(format!("field.{}", mixop_key(at))),
                        self.enc(e, mode, fl)?,
                    )?;
                    acc = app(acc, field)?;
                }
                Ok(acc)
            }
            E::Opt { eo } => match eo {
                None => Ok(con("opt.none")),
                Some(inner) => app(con("opt.some"), self.enc(inner, mode, fl)?),
            },
            // Everything else: the shared coarse encoding, children
            // recursively flattened. ONE shape source — [`encode::shape`] —
            // so tags and child order can never diverge from `encode_exp`
            // (incl. the injectivity-restored `upd`/`ext` path children).
            other => match encode::shape(other) {
                encode::Shape::Node(tag_str, kids) => {
                    let mut acc = con(tag_str);
                    for c in kids {
                        acc = app(acc, self.enc(c, mode, fl)?)?;
                    }
                    Ok(acc)
                }
                // Leaves / metavars / literals / structs / iterations are all
                // handled above (and `canon` is idempotent) — but stay total.
                _ => encode_exp(other),
            },
        }
    }

    /// Evaluate a call-bearing SpecTec list iteration through a per-site
    /// zipped-map relation.
    ///
    /// For `body(x₁,…,xₖ)` over domains `xs₁,…,xsₖ`, emit:
    ///
    /// ```text
    /// map(rides…, [], …, [], [])
    /// eval(body(x₁,…,xₖ), y) ∧ map(rides…, xs₁,…,xsₖ, ys)
    ///   ⇒ map(rides…, xs₁·x₁,…,xsₖ·xₖ, ys·y)
    /// ```
    ///
    /// The body goes through [`Self::enc`] in condition mode, so nested calls,
    /// projections, conversions, and nested supported maps become ordinary
    /// graph premises. Zipping is exact: unequal domain lengths cannot derive
    /// a result. Unsupported iterator kinds remain explicitly opaque.
    fn flatten_iter_map(
        &mut self,
        body: &SpecTecExp,
        it: &SpecTecIter,
        xes: &[SpecTecIterExp],
        outer: &mut Flattened,
    ) -> Result<Term> {
        let listn = matches!(it, SpecTecIter::ListN { .. });
        if !listn && (!matches!(it, SpecTecIter::List | SpecTecIter::Opt) || xes.is_empty()) {
            let raw = SpecTecExp::Iter {
                e1: Box::new(body.clone()),
                it: it.clone(),
                xes: xes.to_vec(),
            };
            let p = self.opaque_prem("cond.iter-map", encode_exp(&raw)?)?;
            outer.prems.push(p);
            return Ok(metavar(&self.fresh_var(outer)));
        }

        let elems: Vec<String> = xes
            .iter()
            .map(|SpecTecIterExp::Dom { x, .. }| x.clone())
            .collect();
        let index = match it {
            SpecTecIter::ListN { xo, .. } => xo.first().cloned(),
            _ => None,
        };
        if let SpecTecIter::ListN { e: bounds, .. } = it {
            // A ListN bound is a natural by construction. Give every bound
            // metavariable bare-nat currency before lowering either the
            // element body or the bound expression itself.
            for bound in bounds {
                let mut vars = Vec::new();
                encode::collect_metavars(bound, &mut vars);
                self.numeric.extend(vars);
            }
        }
        if let Some(index) = &index {
            // The index has bare-nat currency in arithmetic/evaluator
            // premises and a single `num.nat` wrap in encoded spines.
            self.numeric.insert(index.clone());
        }
        let mut body_vars = Vec::new();
        encode::collect_metavars(body, &mut body_vars);
        let rides: Vec<String> = body_vars
            .into_iter()
            .filter(|v| !elems.contains(v) && index.as_ref() != Some(v))
            .collect();

        // Lower the element computation once; its variables are bound in the
        // snoc clause, not leaked into the enclosing rule.
        let mut inner = Flattened::default();
        let value = self.enc(body, Mode::Cond, &mut inner)?;

        let site = self.fresh;
        self.fresh += 1;
        let op = format!("map.{site}");
        let k = elems.len();

        let ride_terms: Vec<Term> = rides.iter().map(|r| metavar(r)).collect();
        if let SpecTecIter::ListN { e: bounds, .. } = it {
            let Some(bound) = bounds.first() else {
                let p = self.opaque_prem("cond.iter-map", encode_exp(body)?)?;
                outer.prems.push(p);
                return Ok(metavar(&self.fresh_var(outer)));
            };
            if !self.can_ndenote(bound) {
                let p = self.opaque_prem("cond.iter-map", encode_exp(bound)?)?;
                outer.prems.push(p);
                return Ok(metavar(&self.fresh_var(outer)));
            }

            let i = index.unwrap_or_else(|| format!("map#{site}.i"));
            let j = format!("map#{site}.j");
            let ys = format!("map#{site}.ys");
            let xs: Vec<String> = (0..k).map(|n| format!("map#{site}.xs{n}")).collect();
            let mut base_args = ride_terms.clone();
            base_args.extend(std::iter::repeat_n(con("list"), k));
            base_args.push(wrap_nat(mk_nat(0u64))?);
            let base = Clause {
                metavars: rides.clone(),
                prems: vec![],
                concl: ev_graph(&op, &base_args, &con("list"))?,
            };

            let mut prev_args = ride_terms.clone();
            prev_args.extend(xs.iter().map(|x| metavar(x)));
            prev_args.push(wrap_nat(metavar(&i))?);
            let mut next_args = ride_terms;
            for (xs, x) in xs.iter().zip(&elems) {
                next_args.push(app(metavar(xs), metavar(x))?);
            }
            next_args.push(wrap_nat(metavar(&j))?);
            let mut step_prems = vec![LowerPrem::Side(
                metavar(&j).equals(Term::app(Term::succ(), metavar(&i)))?,
            )];
            step_prems.extend(inner.prems);
            step_prems.push(LowerPrem::Judgement(ev_graph(
                &op,
                &prev_args,
                &metavar(&ys),
            )?));
            let mut step_metavars = rides.clone();
            step_metavars.extend(xs);
            step_metavars.extend(elems);
            step_metavars.extend([i, j, ys.clone()]);
            for m in inner.new_metavars {
                if !step_metavars.contains(&m) {
                    step_metavars.push(m);
                }
            }
            let step = Clause {
                metavars: step_metavars,
                prems: step_prems,
                concl: ev_graph(&op, &next_args, &app(metavar(&ys), value)?)?,
            };
            self.emit_ev(&op, || Ok(vec![base, step]))?;

            let mut main_args: Vec<Term> = rides.iter().map(|r| metavar(r)).collect();
            for SpecTecIterExp::Dom { e, .. } in xes {
                main_args.push(self.enc(e, Mode::Cond, outer)?);
            }
            main_args.push(wrap_nat(self.ndenote(bound, outer)?)?);
            let result = self.fresh_var(outer);
            outer.prems.push(LowerPrem::Judgement(ev_graph(
                &op,
                &main_args,
                &metavar(&result),
            )?));
            return Ok(metavar(&result));
        }

        if matches!(it, SpecTecIter::Opt) {
            let mut none_args = ride_terms.clone();
            none_args.extend(std::iter::repeat_n(con("opt.none"), k));
            let none = Clause {
                metavars: rides.clone(),
                prems: vec![],
                concl: ev_graph(&op, &none_args, &con("opt.none"))?,
            };

            let mut some_args = ride_terms;
            for x in &elems {
                some_args.push(app(con("opt.some"), metavar(x))?);
            }
            let mut some_metavars = rides.clone();
            some_metavars.extend(elems);
            for m in inner.new_metavars {
                if !some_metavars.contains(&m) {
                    some_metavars.push(m);
                }
            }
            let some = Clause {
                metavars: some_metavars,
                prems: inner.prems,
                concl: ev_graph(&op, &some_args, &app(con("opt.some"), value)?)?,
            };
            self.emit_ev(&op, || Ok(vec![none, some]))?;

            let mut main_args: Vec<Term> = rides.iter().map(|r| metavar(r)).collect();
            for SpecTecIterExp::Dom { e, .. } in xes {
                main_args.push(self.enc(e, Mode::Cond, outer)?);
            }
            let result = self.fresh_var(outer);
            outer.prems.push(LowerPrem::Judgement(ev_graph(
                &op,
                &main_args,
                &metavar(&result),
            )?));
            return Ok(metavar(&result));
        }

        let mut nil_args = ride_terms.clone();
        nil_args.extend(std::iter::repeat_n(con("list"), k));
        let nil = Clause {
            metavars: rides.clone(),
            prems: vec![],
            concl: ev_graph(&op, &nil_args, &con("list"))?,
        };

        let xs: Vec<String> = (0..k).map(|i| format!("map#{site}.xs{i}")).collect();
        let ys = format!("map#{site}.ys");
        let mut prev_args = ride_terms.clone();
        prev_args.extend(xs.iter().map(|x| metavar(x)));
        let mut next_args = ride_terms;
        for (xs, x) in xs.iter().zip(&elems) {
            next_args.push(app(metavar(xs), metavar(x))?);
        }
        let mut step_prems = inner.prems;
        step_prems.push(LowerPrem::Judgement(ev_graph(
            &op,
            &prev_args,
            &metavar(&ys),
        )?));
        let mut step_metavars = rides.clone();
        step_metavars.extend(xs);
        step_metavars.push(ys.clone());
        step_metavars.extend(elems);
        for m in inner.new_metavars {
            if !step_metavars.contains(&m) {
                step_metavars.push(m);
            }
        }
        let step = Clause {
            metavars: step_metavars,
            prems: step_prems,
            concl: ev_graph(&op, &next_args, &app(metavar(&ys), value)?)?,
        };
        self.emit_ev(&op, || Ok(vec![nil, step]))?;

        let mut main_args: Vec<Term> = rides.iter().map(|r| metavar(r)).collect();
        for SpecTecIterExp::Dom { e, .. } in xes {
            main_args.push(self.enc(e, Mode::Cond, outer)?);
        }
        let result = self.fresh_var(outer);
        outer.prems.push(LowerPrem::Judgement(ev_graph(
            &op,
            &main_args,
            &metavar(&result),
        )?));
        Ok(metavar(&result))
    }

    /// Lower `left ∨ right` into a tiny per-site guard relation with one
    /// clause per branch. This is the Horn-clause representation of a
    /// disjunction: the enclosing rule requires `ev.guard.N(vars…, true)`,
    /// and either branch's premises can derive that judgement.
    fn flatten_disjunction(
        &mut self,
        left: &SpecTecExp,
        right: &SpecTecExp,
        outer: &mut Flattened,
    ) -> Result<()> {
        let mut vars = Vec::new();
        encode::collect_metavars(left, &mut vars);
        encode::collect_metavars(right, &mut vars);

        let mut l = Flattened::default();
        self.cond_into(left, &mut l)?;
        let mut r = Flattened::default();
        self.cond_into(right, &mut r)?;

        let site = self.fresh;
        self.fresh += 1;
        let op = format!("guard.{site}");
        let args: Vec<Term> = vars.iter().map(|v| metavar(v)).collect();
        let mk_branch = |branch: Flattened| {
            let mut metavars = vars.clone();
            for m in branch.new_metavars {
                if !metavars.contains(&m) {
                    metavars.push(m);
                }
            }
            Ok(Clause {
                metavars,
                prems: branch.prems,
                concl: ev_graph(&op, &args, &con("bool.true"))?,
            })
        };
        let clauses = vec![mk_branch(l)?, mk_branch(r)?];
        self.emit_ev(&op, || Ok(clauses))?;
        outer.prems.push(LowerPrem::Judgement(ev_graph(
            &op,
            &args,
            &con("bool.true"),
        )?));
        Ok(())
    }

    /// Wrap every occurrence of each numeric-discipline metavariable in a raw
    /// encoding (`st$v$n ↦ app(st$c$num.nat, st$v$n)`) — the substitution twin
    /// of the `E::Var` wrap in [`Flattener::enc`], for spines encoded
    /// wholesale (iteration nodes). Ground currency is unchanged: a wrapped
    /// occurrence instantiated with the bare numeral `⌜k⌝` is exactly
    /// `encode(Num k)`, the same term a full-encoding instantiation of a
    /// non-numeric metavar lands there.
    fn wrap_numeric_in(&self, t: Term) -> Result<Term> {
        let mut out = t;
        for v in &self.numeric {
            out = subst_free(
                &out,
                &Var::new(metavar_name(v), phi()),
                &wrap_nat(metavar(v))?,
            );
        }
        Ok(out)
    }

    /// Whether an `Uncase` key is safely projectable: it must be unambiguous
    /// (`Some`) within **every** catalogued type that defines it — the 24
    /// within-type duplicate keys refuse (their encodings collide).
    fn uncase_key_ok(&self, key: &str) -> bool {
        let mut any = false;
        for ty in self.cat.owners_of(key) {
            any = true;
            if self.cat.case(ty, key).is_none() {
                return false;
            }
        }
        any
    }

    /// Flatten a call `f(args)` into a `fn.<f>` graph premise with a fresh
    /// result metavariable. Non-expression arguments (constant `Def` ops,
    /// type arguments) are folded into the tag (`fn.<f>$<key>` — the
    /// monomorphisation convention shared with the `Dec` lowering leg).
    fn flatten_call(
        &mut self,
        f: &str,
        as1: &[SpecTecArg],
        mode: Mode,
        fl: &mut Flattened,
    ) -> Result<Term> {
        let name = call_fn_name(f, as1);
        let mut args = Vec::new();
        for a in as1 {
            if let SpecTecArg::Exp { e } = a {
                // A mapped iteration supplied as a function argument denotes
                // its value list, not the raw iterator syntax.  Evaluate that
                // argument through the exact per-site zipped-map relation
                // even when the surrounding call occurs in a Rule premise
                // (`Mode::Judgement`).  This is notably required by
                // `Instrs_ok/seq`:
                //
                //     $with_locals(C, x_1*, (SET t)*)
                //
                // where the function graph consumes the concrete list of
                // `SET t` local types.  Restricting the mode promotion to the
                // iteration argument preserves ordinary judgement-spine
                // encoding while using the already exact List/Opt/ListN map
                // evaluator for the value-producing boundary.
                let arg_mode = if matches!(e, SpecTecExp::Iter { .. }) {
                    Mode::CallArg
                } else {
                    mode
                };
                args.push(self.enc(e, arg_mode, fl)?);
            }
        }
        let r = self.fresh_var(fl);
        fl.prems
            .push(LowerPrem::Judgement(fn_graph(&name, &args, &metavar(&r))?));
        Ok(metavar(&r))
    }

    /// Like [`Self::flatten_call`] but with an explicit result term (used for
    /// boolean calls compared against `true`/`false`, and numeric calls whose
    /// result is a wrapped numeric metavar).
    fn call_with_result(
        &mut self,
        f: &str,
        as1: &[SpecTecArg],
        result: Term,
        fl: &mut Flattened,
    ) -> Result<()> {
        let name = call_fn_name(f, as1);
        let mut args = Vec::new();
        for a in as1 {
            if let SpecTecArg::Exp { e } = a {
                args.push(self.enc(e, Mode::Cond, fl)?);
            }
        }
        fl.prems
            .push(LowerPrem::Judgement(fn_graph(&name, &args, &result)?));
        Ok(())
    }

    // =======================================================================
    // Arithmetic denotation (bare `nat` terms over the numeric discipline)
    // =======================================================================

    /// Whether `ndenote` can render `e` (pure check, no emission).
    fn can_ndenote(&self, e: &SpecTecExp) -> bool {
        use SpecTecExp as E;
        match e {
            E::Num {
                n: SpecTecNum::Nat(_),
            } => true,
            E::Var { id } => self.is_numeric(id),
            E::Bin { op, t, e1, e2 } => {
                is_nat_arith(op, t) && self.can_ndenote(e1) && self.can_ndenote(e2)
            }
            // Evaluated-to-nat nodes (result via a fresh numeric metavar).
            E::Len { .. } | E::Call { .. } => true,
            E::Uncase { op, .. } => self.uncase_key_ok(&mixop_key(op)),
            E::Proj { e1, i } => *i >= 0 && self.can_ndenote_projectee(e1),
            E::Dot { .. } | E::Idx { .. } => true,
            E::Cvt { .. } if shape_nat_cvt(e) => self.cvt_tree_evaluable(e),
            _ => false,
        }
    }

    fn cvt_tree_evaluable(&self, e: &SpecTecExp) -> bool {
        use SpecTecExp as E;
        match e {
            E::Var { id } => self.is_numeric(id) || id.starts_with("call%"),
            E::Num {
                n: SpecTecNum::Nat(_),
            } => true,
            E::Bin { e1, e2, .. } => self.cvt_tree_evaluable(e1) && self.cvt_tree_evaluable(e2),
            E::Cvt { e1, .. } => self.cvt_tree_evaluable(e1),
            E::Len { .. }
            | E::Call { .. }
            | E::Uncase { .. }
            | E::Proj { .. }
            | E::Dot { .. }
            | E::Idx { .. } => true,
            _ => false,
        }
    }

    fn equality_tree_evaluable(&self, e: &SpecTecExp) -> bool {
        use SpecTecExp as E;
        match encode::canon(e) {
            E::Iter { .. } => true,
            cvt @ E::Cvt { .. } => shape_nat_cvt(cvt) && self.cvt_tree_evaluable(cvt),
            other => children(other)
                .into_iter()
                .all(|c| self.equality_tree_evaluable(c)),
        }
    }

    fn can_ndenote_projectee(&self, e: &SpecTecExp) -> bool {
        // The projectee itself is flattened structurally in cond mode; any
        // shape is fine except an ambiguous uncase.
        match e {
            SpecTecExp::Uncase { op, .. } => self.uncase_key_ok(&mixop_key(op)),
            _ => true,
        }
    }

    /// Render `e` as a **bare** `nat` term over the numeric discipline,
    /// hoisting evaluation premises (`ev.*` / `fn.*`) into `fl`.
    fn ndenote(&mut self, e: &SpecTecExp, fl: &mut Flattened) -> Result<Term> {
        use SpecTecExp as E;
        match e {
            E::Num {
                n: SpecTecNum::Nat(u),
            } => Ok(mk_nat(*u)),
            E::Var { id } if self.is_numeric(id) => Ok(metavar(id)),
            // Dec lifting may have replaced a Nat-valued call by a fresh
            // full-encoding witness after the numeric pre-scan. Project its
            // `num.nat` payload relationally instead of changing the already
            // emitted call-result currency.
            E::Var { id } if id.starts_with("call%") => {
                self.emit_ev("unnat", evalrel::unnat_clause)?;
                self.numeric_result("unnat", vec![metavar(id)], fl)
            }
            E::Bin { op, t, e1, e2 } if is_nat_arith(op, t) => {
                let f = nat_arith_fn(op)?;
                let a = self.ndenote(e1, fl)?;
                let b = self.ndenote(e2, fl)?;
                f.apply(a)?.apply(b)
            }
            // Exact positive-rational truncation:
            // nat((nat a / nat b) : rat) = a div b, guarded by b > 0.
            E::Cvt {
                nt1: SpecTecNumTyp::Rat,
                nt2: SpecTecNumTyp::Nat,
                e1,
            } => {
                let E::Bin {
                    op: SpecTecBinOp::Div,
                    t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
                    e1: num,
                    e2: den,
                } = &**e1
                else {
                    return Err(flatten_err("unsupported Rat->Nat conversion"));
                };
                let (
                    E::Cvt {
                        nt1: SpecTecNumTyp::Nat,
                        nt2: SpecTecNumTyp::Rat,
                        e1: num,
                    },
                    E::Cvt {
                        nt1: SpecTecNumTyp::Nat,
                        nt2: SpecTecNumTyp::Rat,
                        e1: den,
                    },
                ) = (&**num, &**den)
                else {
                    return Err(flatten_err("Rat->Nat operands are not natural casts"));
                };
                let a = self.ndenote(num, fl)?;
                let b = self.ndenote(den, fl)?;
                fl.prems.push(LowerPrem::Side(
                    nat::nat_lt().apply(mk_nat(0u64))?.apply(b.clone())?,
                ));
                nat::nat_div().apply(a)?.apply(b)
            }
            // Exact partial Int->Nat subtraction. HOL nat subtraction agrees
            // when the source integer result is nonnegative; attach that
            // definedness condition explicitly.
            E::Cvt {
                nt1: SpecTecNumTyp::Int,
                nt2: SpecTecNumTyp::Nat,
                e1,
            } => {
                let E::Bin {
                    op: SpecTecBinOp::Sub,
                    t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
                    e1: lhs,
                    e2: rhs,
                } = &**e1
                else {
                    return Err(flatten_err("unsupported Int->Nat conversion"));
                };
                let (
                    E::Cvt {
                        nt1: SpecTecNumTyp::Nat,
                        nt2: SpecTecNumTyp::Int,
                        e1: lhs,
                    },
                    E::Cvt {
                        nt1: SpecTecNumTyp::Nat,
                        nt2: SpecTecNumTyp::Int,
                        e1: rhs,
                    },
                ) = (&**lhs, &**rhs)
                else {
                    return Err(flatten_err("Int->Nat subtraction is not over Nat casts"));
                };
                let a = self.ndenote(lhs, fl)?;
                let b = self.ndenote(rhs, fl)?;
                fl.prems.push(LowerPrem::Side(
                    nat::nat_le().apply(b.clone())?.apply(a.clone())?,
                ));
                nat::nat_sub().apply(a)?.apply(b)
            }
            // Evaluated-to-nat nodes: flatten with the result slot in
            // **wrapped** form over a fresh numeric metavar, return it bare.
            // (The `ev.*` clause results are `∀`-general, so a wrapped slot
            // matches exactly when the projected value is a nat encoding.)
            E::Len { e1 } => {
                let inner = self.enc(e1, Mode::Cond, fl)?;
                self.emit_ev("len", evalrel::len_clauses)?;
                self.numeric_result("len", vec![inner], fl)
            }
            E::Uncase { e1, op } => {
                let key = mixop_key(op);
                if !self.uncase_key_ok(&key) {
                    return Err(flatten_err(format!("ambiguous uncase key `{key}`")));
                }
                let inner = self.enc(e1, Mode::Cond, fl)?;
                self.emit_ev(&format!("uncase.{key}"), || evalrel::uncase_clause(&key))?;
                self.numeric_result(&format!("uncase.{key}"), vec![inner], fl)
            }
            E::Proj { e1, i } if *i >= 0 => {
                let i = *i as usize;
                let inner = self.enc(e1, Mode::Cond, fl)?;
                self.emit_ev(&format!("proj.{i}"), || evalrel::proj_clauses(i))?;
                self.numeric_result(&format!("proj.{i}"), vec![inner], fl)
            }
            E::Dot { e1, at } => {
                let key = mixop_key(at);
                let inner = self.enc(e1, Mode::Cond, fl)?;
                self.emit_ev(&format!("dot.{key}"), || evalrel::dot_clauses(&key))?;
                self.numeric_result(&format!("dot.{key}"), vec![inner], fl)
            }
            E::Idx { e1, e2 } => {
                let list = self.enc(e1, Mode::Cond, fl)?;
                let idx = self.enc(e2, Mode::Cond, fl)?;
                self.emit_ev("len", evalrel::len_clauses)?;
                self.emit_ev("idx", evalrel::idx_clauses)?;
                self.numeric_result("idx", vec![list, idx], fl)
            }
            E::Call { x, as1 } => {
                let r = self.fresh_var(fl);
                self.numeric.insert(r.clone());
                self.call_with_result(x, as1, wrap_nat(metavar(&r))?, fl)?;
                Ok(metavar(&r))
            }
            other => Err(flatten_err(format!(
                "not arithmetically denotable: {other:?}"
            ))),
        }
    }

    /// A nonnegative rational expression as a natural numerator/denominator.
    /// Denominator nonzeroness is emitted as an ordinary side condition.
    fn rat_nat(&mut self, e: &SpecTecExp, fl: &mut Flattened) -> Result<(Term, Term)> {
        use SpecTecExp as E;
        match e {
            E::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Rat,
                e1,
            } => Ok((self.ndenote(e1, fl)?, mk_nat(1u64))),
            E::Bin {
                op: SpecTecBinOp::Div,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
                e1,
                e2,
            } => {
                let (an, ad) = self.rat_nat(e1, fl)?;
                let (bn, bd) = self.rat_nat(e2, fl)?;
                fl.prems.push(LowerPrem::Side(
                    nat::nat_lt().apply(mk_nat(0u64))?.apply(bn.clone())?,
                ));
                Ok((
                    nat::nat_mul().apply(an)?.apply(bd)?,
                    nat::nat_mul().apply(ad)?.apply(bn)?,
                ))
            }
            E::Bin {
                op: SpecTecBinOp::Mul,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
                e1,
                e2,
            } => {
                let (an, ad) = self.rat_nat(e1, fl)?;
                let (bn, bd) = self.rat_nat(e2, fl)?;
                Ok((
                    nat::nat_mul().apply(an)?.apply(bn)?,
                    nat::nat_mul().apply(ad)?.apply(bd)?,
                ))
            }
            E::Bin {
                op: SpecTecBinOp::Add,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
                e1,
                e2,
            } => {
                let (an, ad) = self.rat_nat(e1, fl)?;
                let (bn, bd) = self.rat_nat(e2, fl)?;
                let left = nat::nat_mul().apply(an)?.apply(bd.clone())?;
                let right = nat::nat_mul().apply(bn)?.apply(ad.clone())?;
                Ok((
                    nat::nat_add().apply(left)?.apply(right)?,
                    nat::nat_mul().apply(ad)?.apply(bd)?,
                ))
            }
            other => Err(flatten_err(format!(
                "not a nonnegative rational expression: {other:?}"
            ))),
        }
    }

    /// Emit an `ev.<op>` premise whose result slot is a **wrapped** fresh
    /// numeric metavar, returning the bare var (the `ndenote` currency).
    fn numeric_result(&mut self, op: &str, args: Vec<Term>, fl: &mut Flattened) -> Result<Term> {
        let r = self.fresh_var(fl);
        self.numeric.insert(r.clone());
        fl.prems.push(LowerPrem::Judgement(ev_graph(
            op,
            &args,
            &wrap_nat(metavar(&r))?,
        )?));
        Ok(metavar(&r))
    }

    // =======================================================================
    // Boolean side-condition rendering (arithmetic fragment)
    // =======================================================================

    /// Render a whole condition as one real `bool` HOL term over bare numeric
    /// metavars (evaluation premises hoisted), or fail (structural condition).
    fn bool_side(&mut self, e: &SpecTecExp, fl: &mut Flattened) -> Result<Term> {
        use SpecTecExp as E;
        match e {
            E::Bool { b } => Ok(mk_bool(*b)),
            E::Un {
                op: SpecTecUnOp::Not,
                e2,
                ..
            } => self.bool_side(e2, fl)?.not(),
            E::Bin { op, t: _, e1, e2 } => {
                let f: fn(Term, Term) -> Result<Term> = match op {
                    SpecTecBinOp::And => |a, b| a.and(b),
                    SpecTecBinOp::Or => |a, b| a.or(b),
                    SpecTecBinOp::Impl => |a, b| a.imp(b),
                    SpecTecBinOp::Equiv => |a, b| a.iff(b),
                    _ => return Err(flatten_err("bool_side: arithmetic at bool position")),
                };
                let a = self.bool_side(e1, fl)?;
                let b = self.bool_side(e2, fl)?;
                f(a, b)
            }
            E::Cmp { op, t, e1, e2 } => {
                use SpecTecCmpOp as C;
                if matches!(op, C::Eq)
                    && let Some((num, den, rhs)) = signed_div_eq_pos_nat_shape(e1, e2)
                        .or_else(|| signed_div_eq_pos_nat_shape(e2, e1))
                {
                    let a = self.enc(num, Mode::Cond, fl)?;
                    let b = self.enc(den, Mode::Cond, fl)?;
                    let n = self.ndenote(rhs, fl)?;
                    self.emit_ev("signed-div-eq-pos-nat", || {
                        evalrel::signed_div_eq_pos_nat_clauses()
                    })?;
                    fl.prems.push(LowerPrem::Judgement(ev_graph(
                        "signed-div-eq-pos-nat",
                        &[a, b, wrap_nat(n)?],
                        &con("bool.true"),
                    )?));
                    return Ok(mk_bool(true));
                }
                let ordering_nat = matches!(op, C::Lt | C::Gt | C::Le | C::Ge) && is_nat_ty(t);
                let ordering_rat = matches!(op, C::Lt | C::Gt | C::Le | C::Ge)
                    && matches!(t, SpecTecOpTyp::Num(SpecTecNumTyp::Rat));
                let eq_arith = matches!(op, C::Eq | C::Ne) && cmp_is_nat_arith(op, t, e1, e2);
                let equality_rat =
                    matches!(op, C::Eq | C::Ne) && shape_rat_nat(e1) && shape_rat_nat(e2);
                if ordering_rat || equality_rat {
                    let (an, ad) = self.rat_nat(e1, fl)?;
                    let (bn, bd) = self.rat_nat(e2, fl)?;
                    let left = nat::nat_mul().apply(an)?.apply(bd)?;
                    let right = nat::nat_mul().apply(bn)?.apply(ad)?;
                    return match op {
                        C::Lt => nat::nat_lt().apply(left)?.apply(right),
                        C::Le => nat::nat_le().apply(left)?.apply(right),
                        C::Gt => nat::nat_lt().apply(right)?.apply(left),
                        C::Ge => nat::nat_le().apply(right)?.apply(left),
                        C::Eq => left.equals(right),
                        C::Ne => left.equals(right)?.not(),
                    };
                }
                if !(ordering_nat || eq_arith) {
                    return Err(flatten_err("bool_side: non-arithmetic comparison"));
                }
                let a = self.ndenote(e1, fl)?;
                let b = self.ndenote(e2, fl)?;
                match op {
                    C::Eq => a.equals(b),
                    C::Ne => a.equals(b)?.not(),
                    C::Lt => nat::nat_lt().apply(a)?.apply(b),
                    C::Le => nat::nat_le().apply(a)?.apply(b),
                    C::Gt => nat::nat_lt().apply(b)?.apply(a),
                    C::Ge => nat::nat_le().apply(b)?.apply(a),
                }
            }
            other => Err(flatten_err(format!("bool_side: {other:?}"))),
        }
    }

    // =======================================================================
    // Condition flattening
    // =======================================================================

    fn cond_into(&mut self, e: &SpecTecExp, fl: &mut Flattened) -> Result<()> {
        use SpecTecExp as E;
        // 1. Whole-condition arithmetic (covers the value fragment, and
        //    or-/impl-structured negation results with hoisted evaluations).
        {
            let mut probe = Flattened::default();
            let save_fresh = self.fresh;
            let save_numeric = self.numeric.clone();
            match self.bool_side(e, &mut probe) {
                Ok(t) => {
                    fl.prems.extend(probe.prems);
                    fl.new_metavars.extend(probe.new_metavars);
                    fl.prems.push(LowerPrem::Side(t));
                    return Ok(());
                }
                Err(_) => {
                    // Roll back speculative state.
                    self.fresh = save_fresh;
                    self.numeric = save_numeric;
                }
            }
        }
        // 2. Structural forms.
        match e {
            E::Bool { b } => {
                // `true` is vacuous; `false` is an underivable real antecedent.
                if !*b {
                    fl.prems.push(LowerPrem::Side(mk_bool(false)));
                }
                Ok(())
            }
            E::Bin {
                op: SpecTecBinOp::And,
                e1,
                e2,
                ..
            } => {
                self.cond_into(e1, fl)?;
                self.cond_into(e2, fl)
            }
            E::Un {
                op: SpecTecUnOp::Not,
                e2,
                ..
            } => match &**e2 {
                // ¬(bool call): graph premise with result `false`.
                E::Call { x, as1 } => self.call_with_result(x, as1, con("bool.false"), fl),
                inner => match negate(inner) {
                    Ok(neg) => self.cond_into(&neg, fl),
                    Err(_) => {
                        let body = encode_exp(e)?;
                        let p = self.opaque_prem("cond.not", body)?;
                        fl.prems.push(p);
                        Ok(())
                    }
                },
            },
            // A bool-valued call as the whole condition.
            E::Call { x, as1 } => self.call_with_result(x, as1, con("bool.true"), fl),
            // List membership.
            E::Mem { e1, e2 } => {
                let x = self.enc(e1, Mode::Cond, fl)?;
                let xs = self.enc(e2, Mode::Cond, fl)?;
                self.emit_ev("mem", evalrel::mem_clauses)?;
                fl.prems
                    .push(LowerPrem::Judgement(ev_graph("mem", &[x], &xs)?));
                Ok(())
            }
            E::Cmp { op, t, e1, e2 } => match op {
                SpecTecCmpOp::Eq => self.cond_eq(e, e1, e2, fl),
                SpecTecCmpOp::Ne => self.cond_ne(e, e1, e2, fl),
                op if is_nat_ty(t)
                    && coarse_eq_reason(e1).is_none()
                    && coarse_eq_reason(e2).is_none() =>
                {
                    let (lhs, rhs) = match op {
                        SpecTecCmpOp::Lt | SpecTecCmpOp::Le => (e1, e2),
                        SpecTecCmpOp::Gt | SpecTecCmpOp::Ge => (e2, e1),
                        SpecTecCmpOp::Eq | SpecTecCmpOp::Ne => unreachable!(),
                    };
                    let strict = matches!(op, SpecTecCmpOp::Lt | SpecTecCmpOp::Gt);
                    let key = if strict { "nat.lt" } else { "nat.le" };
                    let a = self.enc(lhs, Mode::Cond, fl)?;
                    let b = self.enc(rhs, Mode::Cond, fl)?;
                    self.emit_ev(key, || evalrel::nat_order_clauses(strict))?;
                    fl.prems.push(LowerPrem::Judgement(ev_graph(
                        key,
                        &[a, b],
                        &con("bool.true"),
                    )?));
                    Ok(())
                }
                op if is_int_ty(t) => {
                    let (lhs, rhs) = match op {
                        SpecTecCmpOp::Lt | SpecTecCmpOp::Le => (e1, e2),
                        SpecTecCmpOp::Gt | SpecTecCmpOp::Ge => (e2, e1),
                        SpecTecCmpOp::Eq | SpecTecCmpOp::Ne => unreachable!(),
                    };
                    let strict = matches!(op, SpecTecCmpOp::Lt | SpecTecCmpOp::Gt);
                    let key = if strict { "int.lt" } else { "int.le" };
                    let a = self.enc(lhs, Mode::Cond, fl)?;
                    let b = self.enc(rhs, Mode::Cond, fl)?;
                    self.emit_ev(key, || evalrel::int_order_clauses(strict))?;
                    fl.prems.push(LowerPrem::Judgement(ev_graph(
                        key,
                        &[a, b],
                        &con("bool.true"),
                    )?));
                    Ok(())
                }
                _ => {
                    // Rat/real/float and other non-natural orderings are not
                    // expressible yet.
                    let body = encode_exp(e)?;
                    let p = self.opaque_prem("cond.cmp-nonnat", body)?;
                    fl.prems.push(p);
                    Ok(())
                }
            },
            // A bare boolean metavariable (or projection): result-is-true.
            E::Var { .. } => {
                let t = self.enc(e, Mode::Cond, fl)?;
                fl.prems.push(LowerPrem::Side(t.equals(con("bool.true"))?));
                Ok(())
            }
            // The frame-guard disjunction `xs =/= [] \/ ys =/= []`
            // (`Step/ctxt-instrs`, `Step_pure/trap-instrs`,
            // `Step_read/throw_ref-instrs`): one `ev.nonempty2` premise —
            // derivable exactly when either side is a snoc node, which at
            // genuine list points is exactly the disjunction.
            E::Bin {
                op: SpecTecBinOp::Or,
                e1,
                e2,
                ..
            } if ne_empty_subject(e1).is_some() && ne_empty_subject(e2).is_some() => {
                let (a, b) = (
                    ne_empty_subject(e1).expect("guard"),
                    ne_empty_subject(e2).expect("guard"),
                );
                let ta = self.enc(a, Mode::Cond, fl)?;
                let tb = self.enc(b, Mode::Cond, fl)?;
                self.emit_ev("nonempty2", evalrel::nonempty2_clauses)?;
                fl.prems
                    .push(LowerPrem::Judgement(ev_graph("nonempty2", &[ta], &tb)?));
                Ok(())
            }
            E::Bin {
                op: SpecTecBinOp::Or,
                e1,
                e2,
                ..
            } => self.flatten_disjunction(e1, e2, fl),
            E::Bin {
                op: SpecTecBinOp::Impl,
                e1,
                e2,
                ..
            } => self.flatten_disjunction(&negate(e1).map_err(flatten_err)?, e2, fl),
            E::Bin {
                op: SpecTecBinOp::Equiv,
                t,
                e1,
                e2,
            } => {
                let both = SpecTecExp::Bin {
                    op: SpecTecBinOp::And,
                    t: t.clone(),
                    e1: e1.clone(),
                    e2: e2.clone(),
                };
                let neither = SpecTecExp::Bin {
                    op: SpecTecBinOp::And,
                    t: t.clone(),
                    e1: Box::new(negate(e1).map_err(flatten_err)?),
                    e2: Box::new(negate(e2).map_err(flatten_err)?),
                };
                self.flatten_disjunction(&both, &neither, fl)
            }
            other => {
                let body = encode_exp(other)?;
                let reason = format!("cond.{}", shape_name(other));
                let p = self.opaque_prem(&reason, body)?;
                fl.prems.push(p);
                Ok(())
            }
        }
    }

    /// Structural equality: a `Side` equation between the two flattened
    /// encodings. Sound because the encoding is **injective at every encoded
    /// position** (`encode.rs` module docs — the R1-F1/F2 restoration): the
    /// equation is refl-dischargeable exactly at genuinely-equal instances,
    /// never vacuous over distinct expressions. Sides that would be silently
    /// *undischargeable* at every genuine point — a residual value-dead
    /// operator spine ([`coarse_eq_reason`]) — are censused opaque instead
    /// (R3-F1); iteration-map sides with embedded calls keep their dedicated
    /// `cond.iter-map` bucket.
    fn cond_eq(
        &mut self,
        whole: &SpecTecExp,
        e1: &SpecTecExp,
        e2: &SpecTecExp,
        fl: &mut Flattened,
    ) -> Result<()> {
        // R3-F1: a side containing a value-dead spine cannot be discharged at
        // any genuine ground point — census, don't load a dead equation.
        if let Some(reason) = coarse_eq_reason(e1).or_else(|| coarse_eq_reason(e2))
            && !(reason == "cond.coarse-eq"
                && self.equality_tree_evaluable(e1)
                && self.equality_tree_evaluable(e2))
        {
            let body = encode_exp(whole)?;
            let p = self.opaque_prem(reason, body)?;
            fl.prems.push(p);
            return Ok(());
        }
        let a = self.enc(e1, Mode::Cond, fl)?;
        let b = self.enc(e2, Mode::Cond, fl)?;
        fl.prems.push(LowerPrem::Side(a.equals(b)?));
        Ok(())
    }

    /// Request the compact reusable open-value disequality basis: option
    /// presence and encoded-natural payload inequality. Constructor pairs
    /// stay demand-driven by literal evidence; eagerly crossing every large
    /// variant would add >14k clauses to this corpus.
    fn emit_open_neq_basis(&mut self) -> Result<()> {
        self.emit_ev("neq.option", evalrel::neq_option_clauses)?;
        self.emit_ev("neq.nat", evalrel::neq_nat_clauses)?;
        Ok(())
    }

    /// Structural disequality: on-demand `ev.neq` clauses for the ordered tag
    /// pairs actually required (under-approximate disequality — sound as an
    /// antecedent), or opaque where the shape is beyond that.
    ///
    /// The [`coarse_eq_reason`] guard is **not** needed here (nor on the
    /// negated-`Eq` paths in `else_`/`decs`, which land in this method or
    /// their own pattern machinery): `ev.neq` judgements are derivable only
    /// for genuinely distinct-tag values, so a coarse sub-spine can only make
    /// the antecedent *harder* to discharge, never vacuous.
    fn cond_ne(
        &mut self,
        whole: &SpecTecExp,
        e1: &SpecTecExp,
        e2: &SpecTecExp,
        fl: &mut Flattened,
    ) -> Result<()> {
        use SpecTecExp as E;
        let opq = |s: &mut Self, reason: &str, fl: &mut Flattened| -> Result<()> {
            let body = encode_exp(whole)?;
            let p = s.opaque_prem(reason, body)?;
            fl.prems.push(p);
            Ok(())
        };
        let (s1, s2) = (strip_sub(e1), strip_sub(e2));
        match (s1, s2) {
            // Option presence. At genuine option points `none`'s complement
            // is exactly `some(_)`, including when the open side is the
            // result of a call or an optional mapped iteration.
            (E::Opt { eo: None }, E::Opt { eo: None }) => opq(self, "cond.neq-same-option", fl),
            (E::Opt { eo: None }, _other) | (_other, E::Opt { eo: None }) => {
                self.emit_ev("neq.option", evalrel::neq_option_clauses)?;
                let a = self.enc(e1, Mode::Cond, fl)?;
                let b = self.enc(e2, Mode::Cond, fl)?;
                fl.prems
                    .push(LowerPrem::Judgement(ev_graph("neq", &[a], &b)?));
                Ok(())
            }
            // Two literal constructors.
            (E::Case { op: o1, .. }, E::Case { op: o2, .. }) => {
                let (k1, k2) = (mixop_key(o1), mixop_key(o2));
                if k1 == k2 {
                    return opq(self, "cond.neq-same-tag", fl);
                }
                if self.emit_ev(&format!("neq.{k1}.{k2}"), || evalrel::neq_clause(&k1, &k2))? {
                    self.neq_pairs += 1;
                }
                let a = self.enc(e1, Mode::Cond, fl)?;
                let b = self.enc(e2, Mode::Cond, fl)?;
                fl.prems
                    .push(LowerPrem::Judgement(ev_graph("neq", &[a], &b)?));
                Ok(())
            }
            // Open side vs a literal constructor: emit every genuinely
            // distinct ordered pair over the candidate tags of the
            // constructor's owner type(s). Distinct case *keys* are distinct
            // constructors of any single (well-typed) comparison type — only
            // a same-key pair could be unsound, and those are excluded — so
            // enumerating the union over ambiguous owners just adds sound
            // clauses.
            (E::Case { op, .. }, _other) | (_other, E::Case { op, .. }) => {
                let case_on_left = matches!(s1, E::Case { .. });
                let k = mixop_key(op);
                let mut keys: Vec<String> = self
                    .cat
                    .owners_of(&k)
                    .flat_map(|ty| self.cat.cases_of(ty).map(<[String]>::to_vec))
                    .flatten()
                    .collect();
                keys.sort();
                keys.dedup();
                if keys.is_empty() {
                    return opq(self, "cond.neq-unknown-tag", fl);
                }
                for k2 in keys.iter().filter(|k2| **k2 != k) {
                    let (a, b) = if case_on_left {
                        (k.clone(), k2.clone())
                    } else {
                        (k2.clone(), k.clone())
                    };
                    if self.emit_ev(&format!("neq.{a}.{b}"), || evalrel::neq_clause(&a, &b))? {
                        self.neq_pairs += 1;
                    }
                }
                let a = self.enc(e1, Mode::Cond, fl)?;
                let b = self.enc(e2, Mode::Cond, fl)?;
                fl.prems
                    .push(LowerPrem::Judgement(ev_graph("neq", &[a], &b)?));
                Ok(())
            }
            _ => {
                self.emit_open_neq_basis()?;
                let a = self.enc(e1, Mode::Cond, fl)?;
                let b = self.enc(e2, Mode::Cond, fl)?;
                fl.prems
                    .push(LowerPrem::Judgement(ev_graph("neq", &[a], &b)?));
                Ok(())
            }
        }
    }
}

impl<'a> CondFlattener for Flattener<'a> {
    fn cond(&mut self, cond: &SpecTecExp) -> Result<Flattened> {
        let mut fl = Flattened::default();
        self.cond_into(cond, &mut fl)?;
        Ok(fl)
    }

    fn expr(&mut self, e: &SpecTecExp) -> Result<(Term, Flattened)> {
        let mut fl = Flattened::default();
        let t = self.enc(e, Mode::Judgement, &mut fl)?;
        Ok((t, fl))
    }

    /// Result positions flatten structural operators exactly like condition
    /// positions do (`ev.dot`/`ev.idx`/`ev.len`/… premises with a fresh
    /// result metavariable) — this is what lets store-accessor graph clauses
    /// (`fn.table` …) conclude with the accessed *value* and fire.
    fn expr_result(&mut self, e: &SpecTecExp) -> Result<(Term, Flattened)> {
        let mut fl = Flattened::default();
        let t = self.enc(e, Mode::Cond, &mut fl)?;
        Ok((t, fl))
    }

    /// Reset the per-rule state and pre-scan every given expression for
    /// metavariables used arithmetically, so wrapped/bare occurrences agree
    /// across the whole clause. Callers (rule and `Dec` lowering alike) MUST
    /// call this before `cond`/`expr` for a new rule, and must NOT pass
    /// `Iter`-premise inner expressions (iteration element variables have
    /// full-encoding currency — they must never enter the numeric set).
    fn begin_rule(&mut self, exprs: &[&SpecTecExp]) {
        self.numeric.clear();
        self.opaque_reasons.clear();
        for e in exprs {
            self.scan_numeric(e);
        }
    }

    /// The real flattener wraps numeric metavars itself (in [`Flattener::enc`]
    /// spines) — clause producers must not wrap again.
    fn wraps_numeric(&self) -> bool {
        true
    }

    fn mark_numeric(&mut self, id: &str) {
        self.numeric.insert(id.to_string());
    }

    fn is_numeric(&self, id: &str) -> bool {
        self.numeric.contains(id)
    }

    /// Deduplicated emission into the shared evaluator-clause pool (drained
    /// once by the integration layer) — always returns `[]`.
    fn request_ev(
        &mut self,
        key: &str,
        build: &dyn Fn() -> Result<Vec<Clause>>,
    ) -> Result<Vec<Clause>> {
        self.emit_ev(key, || build())?;
        Ok(Vec::new())
    }
}

/// Encoding mode: judgement spines flatten calls only (baseline coarse
/// encoding otherwise); condition positions additionally flatten structural
/// operators into `ev.*` premises; rule-**conclusion** position flattens
/// `Cat` only (so conclusion instances carry genuine flat-list encodings —
/// the frame-rule unblocking) while every other operator keeps its
/// judgement-position coarseness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    Judgement,
    Cond,
    Concl,
    /// A direct function-argument iteration: retain judgement encoding for
    /// ordinary nodes, but relationally evaluate a mapped iteration to the
    /// value list consumed by the function graph.
    CallArg,
}

// ===========================================================================
// Rule lowering (v2) and the whole-spec census
// ===========================================================================

fn flatten_err(msg: impl Into<String>) -> covalence_core::Error {
    covalence_core::Error::ConnectiveRule(format!("spectec flatten: {}", msg.into()))
}

/// What lowering one rule produced: its clause, the auxiliary clauses defining
/// its iteration star relations (appended **after all rule clauses** in the
/// combined order — see [`spec_rule_clauses`]), and the iteration residue
/// notes (census).
#[derive(Debug)]
pub struct LoweredRuleV2 {
    pub clause: Clause,
    pub star_aux: Vec<Clause>,
    pub iter_notes: Vec<IterNote>,
    /// `ev.sort.*` guard premises attached (the sub-only-metavariable fix —
    /// see [`super::sortguard`]).
    pub sort_guards: usize,
}

/// Lower one (Else-preprocessed) rule of relation `rel_name` into a clause.
/// Total over the premise zoo: `If` via the flattener, `Rule` premises with
/// call-flattened spines, `Let` as a structural equation, `Iter` via
/// [`star::lower_iter_premise`] (per-site star relations — the aux clauses
/// come back in [`LoweredRuleV2::star_aux`]), a remaining `Else` via the
/// opaque hatch. Evaluator clauses accumulate in the flattener
/// ([`Flattener::drain_ev_clauses`]).
///
/// **Metavariable order** (= the clause's `∀`/instantiation order): the
/// conclusion's, then each premise's, first-seen — with each premise's
/// flattener-fresh (`%f<k>`) and star-introduced (domain / ride / `star#`
/// bound) metavariables appended as soon as that premise is lowered.
/// Iteration **element** variables are *not* rule-level metavars (they are
/// quantified inside the aux clauses), and `Iter` inner expressions are
/// excluded from the numeric pre-scan (element vars have full-encoding
/// currency — see the module docs).
pub fn lower_rule_v2(
    rel_name: &str,
    rule: &SpecTecRule,
    fl: &mut Flattener,
) -> Result<LoweredRuleV2> {
    let SpecTecRule::Rule {
        x: rule_name,
        e,
        prs,
        ..
    } = rule;

    // Pre-scan for the numeric discipline (Iter inner exprs excluded).
    fl.begin_rule(&rule_exprs_non_iter(rule));
    // Iteration inner expressions may also mention rule-level arithmetic
    // parameters ("ride-throughs").  Scan those before encoding the
    // conclusion, but remove iteration-local names again: domain elements
    // carry complete encoded values, while a named ListN index is put under
    // the bare-natural discipline only when its star site is lowered below.
    for pr in prs {
        let SpecTecPrem::Iter { pr1, it, xes } = pr else {
            continue;
        };
        let inner = match &**pr1 {
            SpecTecPrem::Rule { e, .. } | SpecTecPrem::If { e } => Some(e),
            SpecTecPrem::Let { e1, e2 } => {
                fl.scan_numeric(e1);
                Some(e2)
            }
            SpecTecPrem::Else | SpecTecPrem::Iter { .. } => None,
        };
        let mut locals: Vec<&str> = xes
            .iter()
            .map(|SpecTecIterExp::Dom { x, .. }| x.as_str())
            .collect();
        if let SpecTecIter::ListN { xo, .. } = it {
            locals.extend(xo.iter().map(String::as_str));
        }
        let already_numeric: Vec<(&str, bool)> = locals
            .iter()
            .map(|id| (*id, fl.numeric.contains(*id)))
            .collect();
        if let Some(inner) = inner {
            fl.scan_numeric(inner);
        }
        for (id, was_numeric) in already_numeric {
            if !was_numeric {
                fl.numeric.remove(id);
            }
        }
    }
    // A `ListN` bound that is a plain `Var` has bare-numeral currency (the
    // star leg wraps it in the istar bound position) — mark it numeric BEFORE
    // encoding the conclusion so every spine occurrence agrees.
    for pr in prs {
        if let SpecTecPrem::Iter {
            it: SpecTecIter::ListN { e: bounds, .. },
            ..
        } = pr
            && let Some(SpecTecExp::Var { id }) = bounds.first()
        {
            fl.mark_numeric(id);
        }
    }

    // Rule metavariables, incrementally (see the order contract above).
    let mut metavars = Vec::new();
    let drain_new = |metavars: &mut Vec<String>, acc: &mut Flattened| {
        for m in std::mem::take(&mut acc.new_metavars) {
            if !metavars.iter().any(|s| s == &m) {
                metavars.push(m);
            }
        }
    };

    let mut acc = Flattened::default();
    let mut star_aux = Vec::new();
    let mut iter_notes = Vec::new();

    // Conclusion (its evaluation premises come first). `Mode::Concl`
    // flattens `Cat` spines through `ev.cat` premises so the conclusion's
    // derivable instances are genuine flat-list encodings (the
    // `Step/ctxt-instrs`-family unblocking); everything else keeps the
    // judgement-position coarse encoding.
    encode::collect_metavars(e, &mut metavars);
    let concl_term = fl.enc(e, Mode::Concl, &mut acc)?;
    let concl = tag(rel_name, concl_term)?;
    drain_new(&mut metavars, &mut acc);

    for (idx, pr) in prs.iter().enumerate() {
        match pr {
            SpecTecPrem::Rule {
                x: pr_rel, e: pr_e, ..
            } => {
                encode::collect_metavars(pr_e, &mut metavars);
                let t = fl.enc(pr_e, Mode::Judgement, &mut acc)?;
                if let Some(source_rel) = pr_rel.strip_prefix(super::else_::NEGATED_RULE_PREFIX) {
                    let query = tag(source_rel, t)?;
                    let request = DecisionRequest::new(source_rel, query, DecisionAnswer::No);
                    let mut decisions = OpaqueDecisions;
                    acc.prems.push(decisions.premise(&request)?);
                    fl.opaque_reasons.push(format!("decision.{source_rel}"));
                } else {
                    acc.prems.push(LowerPrem::Judgement(tag(pr_rel, t)?));
                }
            }
            SpecTecPrem::If { e } => {
                encode::collect_metavars(e, &mut metavars);
                fl.cond_into(e, &mut acc)?;
            }
            SpecTecPrem::Let { e1, e2 } => {
                // `Let` (0 in the corpus) is an equational binding.
                encode::collect_metavars(e1, &mut metavars);
                encode::collect_metavars(e2, &mut metavars);
                fl.cond_eq(e1, e1, e2, &mut acc)?;
            }
            SpecTecPrem::Else => {
                // Preprocessing failed (or was skipped): load-but-never-fire.
                let p = fl.opaque_prem("else", encode_exp(e)?)?;
                acc.prems.push(p);
            }
            SpecTecPrem::Iter { .. } => {
                // A named ListN index is a bare natural inside its auxiliary
                // clause.  Mark it immediately before inner-condition
                // lowering; the star leg then observes it as pre-wrapped and
                // does not apply its fallback syntactic wrapping a second
                // time.  Domain element binders are deliberately untouched:
                // they range over complete encoded values.
                if let SpecTecPrem::Iter {
                    it: SpecTecIter::ListN { xo, .. },
                    ..
                } = pr
                {
                    for id in xo {
                        fl.mark_numeric(id);
                    }
                }
                // The star leg: per-site aux relation + enclosing premises.
                let snapshot = metavars.clone();
                let site = StarSite::of_premise(rel_name, rule_name, idx, pr, &snapshot)
                    .expect("Iter premise viewed as a star site");
                let li = star::lower_iter_premise(&site, fl)?;
                acc.prems.extend(li.prems);
                star_aux.extend(li.aux);
                for m in li.new_metavars {
                    if !metavars.iter().any(|s| s == &m) {
                        metavars.push(m);
                    }
                }
                // A whole-site opaque is flattener-invisible; record it so the
                // rule census stays honest.
                for n in &li.notes {
                    if let IterNote::OpaqueSite(why) = n {
                        fl.opaque_reasons.push(format!("iter.{why}"));
                    }
                }
                iter_notes.extend(li.notes);
            }
        }
        drain_new(&mut metavars, &mut acc);
    }

    debug_assert!(
        metavars
            .iter()
            .filter(|m| !m.starts_with('%') && !m.starts_with("star#"))
            .all(|m| !m.contains('%')),
        "SpecTec metavariable collides with the fresh-var namespace"
    );

    // Sort guards for sub-only metavariables (see `super::sortguard`): a
    // metavariable whose every occurrence was `Sub`-wrapped lost its sort to
    // the canon strip and would derive false facts at well-sorted points
    // (e.g. `Step_pure/local.tee` firing on a non-`val` instruction). The
    // rule leg guards uniformly — one `ev.sort.*` premise per lost sort,
    // appended after the rule's own premises (expansion would break the
    // one-clause-per-rule addressing contract).
    let mut sort_guards = 0usize;
    {
        let mut prem_exprs: Vec<&SpecTecExp> = Vec::new();
        for pr in prs {
            sortguard::prem_exprs(pr, &mut prem_exprs);
        }
        let plan = sortguard::plan(&[e], &prem_exprs, fl.cat, false);
        debug_assert!(plan.expansions.is_empty());
        for g in &plan.guards {
            if !metavars.iter().any(|m| m == &g.var) {
                continue;
            }
            for (key, cls) in sortguard::guard_families(g, fl.cat)? {
                fl.emit_ev(&key, || Ok(cls))?;
            }
            acc.prems
                .push(LowerPrem::Judgement(sortguard::guard_judgement(
                    &g.var, &g.sort, g.kind,
                )?));
            sort_guards += 1;
        }
        for (v, sort) in &plan.unguardable {
            // Inexpressible sort constraint: the standard opaque hatch
            // (0 on the bundled corpus).
            let p = fl.opaque_prem("sort-unguardable", con(format!("sortvar.{v}.{sort}")))?;
            acc.prems.push(p);
        }
    }

    Ok(LoweredRuleV2 {
        clause: Clause {
            metavars,
            prems: acc.prems,
            concl,
        },
        star_aux,
        iter_notes,
        sort_guards,
    })
}

/// Every expression a rule mentions **outside `Iter` premises** (conclusion,
/// then premises in order, including `If` conditions) — the numeric-pre-scan
/// input (element variables must not enter the numeric set).
fn rule_exprs_non_iter(rule: &SpecTecRule) -> Vec<&SpecTecExp> {
    let SpecTecRule::Rule { e, prs, .. } = rule;
    let mut out = vec![e];
    for pr in prs {
        match pr {
            SpecTecPrem::Rule { e, .. } | SpecTecPrem::If { e } => out.push(e),
            SpecTecPrem::Let { e1, e2 } => {
                out.push(e1);
                out.push(e2);
            }
            SpecTecPrem::Else | SpecTecPrem::Iter { .. } => {}
        }
    }
    out
}

/// The whole-spec census: every relation rule of `defs` lowered (all 558 in
/// the bundled dump — the opaque hatch guarantees totality), with exact
/// bucketed reporting.
#[derive(Debug, Default, Clone)]
pub struct CensusReport {
    /// Total relation rules seen (every one yields a clause).
    pub total_rules: usize,
    /// Rules whose clause carries **no** opaque premise.
    pub fully_flattened: usize,
    /// Rules with ≥ 1 opaque premise, bucketed by reason (a rule counts once
    /// per distinct reason).
    pub opaque_rules: BTreeMap<String, usize>,
    /// Opaque premises, bucketed by reason.
    pub opaque_premises: BTreeMap<String, usize>,
    /// Rules the v1 lowering (`Rule`-premises only) already handled.
    pub v1_lowerable: usize,
    /// Rules v1 skipped that now flatten fully.
    pub newly_flattened: usize,
    /// Evaluator clauses emitted (on demand, deduplicated).
    pub evaluator_clauses: usize,
    /// `ev.neq` ordered tag pairs emitted.
    pub neq_pairs: usize,
    /// `Else` premises rewritten into negated sibling guards.
    pub else_rewritten: usize,
    /// `Else` rewrites refused, bucketed by reason.
    pub else_failed: BTreeMap<String, usize>,
    /// Calls left coarsely encoded under `Iter` spines (soft; judgement
    /// positions only — sound, syntactic-key convention).
    pub iter_embedded_calls: usize,
    /// Rules that failed to lower and fell back to a fully-opaque clause.
    pub fallback_rules: usize,
    /// `Iter` premise sites lowered through the star leg.
    pub star_sites: usize,
    /// Star auxiliary clauses synthesized (appended after the rule clauses).
    pub star_aux_clauses: usize,
    /// Star sites whose inner premise was an `If` (condition through the
    /// flattener — residue shows up in the `cond.*` buckets).
    pub star_inner_if: usize,
    /// `ListN` sites whose bound was not a plain `Var` (bound to a fresh
    /// numeric metavar via a flattened `b = <bound>` condition).
    pub star_bound_flattened: usize,
    /// Star sites whose inner `Rule` premise carries coarse element-access
    /// spines (`Idx`/`Dot`/`Len`/`Slice` in judgement position — the
    /// `Extend_store` family, review R3-F2): the aux clauses load and are
    /// sound (syntactic keys), but the access is not evaluated, so the inner
    /// premise only meets ground keys carrying the same raw spine.
    pub star_coarse_inner: usize,
    /// Whole-site opaque star loads (0 on the bundled corpus).
    pub star_opaque_sites: usize,
    /// Rules that acquired ≥1 `ev.sort.*` guard premise (the sub-only
    /// metavariable fix — [`super::sortguard`]).
    pub sort_guarded_rules: usize,
    /// `ev.sort.*` guard premises attached in total.
    pub sort_guard_premises: usize,
}

/// Whether the v1 lowering ([`super::super::relation`]) accepts this rule
/// (every premise a plain `Rule` premise).
fn v1_lowers(rule: &SpecTecRule) -> bool {
    let SpecTecRule::Rule { prs, .. } = rule;
    prs.iter().all(|p| matches!(p, SpecTecPrem::Rule { .. }))
}

/// Lower **every** relation rule in `defs` (`Else`-preprocessed,
/// condition-flattened, star-synthesized — nothing skipped) through a caller
/// supplied [`Flattener`] (whose evaluator pool is NOT drained — the caller
/// owns it, so one pool can dedupe across the rule and `Dec` legs). Returns
/// `(rule_clauses, star_aux_clauses, census)`: **exactly one rule clause per
/// spec rule, in flattened relation/rule order**, with the aux clauses to
/// append after them.
pub fn spec_rule_clauses(
    defs: &[SpecTecDef],
    fl: &mut Flattener,
) -> (Vec<Clause>, Vec<Clause>, CensusReport) {
    let mut clauses = Vec::new();
    let mut star_aux = Vec::new();
    let mut census = CensusReport::default();

    let mut rels = Vec::new();
    collect_rels(defs, &mut rels);
    for def in rels {
        let SpecTecDef::Rel { x, rules, .. } = def else {
            unreachable!()
        };
        for pre in preprocess_else_with_catalogue(rules, fl.cat) {
            census.total_rules += 1;
            if v1_lowers(&pre.rule) {
                census.v1_lowerable += 1;
            }
            match &pre.status {
                ElseStatus::NoElse => {}
                ElseStatus::Rewritten { .. } => census.else_rewritten += 1,
                ElseStatus::Failed(reason) => {
                    *census.else_failed.entry(reason.clone()).or_default() += 1;
                }
            }
            let SpecTecRule::Rule { prs, .. } = &pre.rule;
            census.star_sites += prs
                .iter()
                .filter(|p| matches!(p, SpecTecPrem::Iter { .. }))
                .count();
            let lowered = lower_rule_v2(x, &pre.rule, fl);
            let reasons = fl.take_opaque_reasons();
            match lowered {
                Ok(lr) => {
                    clauses.push(lr.clause);
                    census.star_aux_clauses += lr.star_aux.len();
                    if lr.sort_guards > 0 {
                        census.sort_guarded_rules += 1;
                        census.sort_guard_premises += lr.sort_guards;
                    }
                    star_aux.extend(lr.star_aux);
                    for n in &lr.iter_notes {
                        match n {
                            IterNote::InnerIf => census.star_inner_if += 1,
                            IterNote::BoundFlattened => census.star_bound_flattened += 1,
                            IterNote::CoarseInner => census.star_coarse_inner += 1,
                            IterNote::OpaqueSite(_) => census.star_opaque_sites += 1,
                        }
                    }
                    if reasons.is_empty() {
                        census.fully_flattened += 1;
                        if !v1_lowers(&pre.rule) {
                            census.newly_flattened += 1;
                        }
                    } else {
                        let mut distinct: Vec<&String> = reasons.iter().collect();
                        distinct.sort();
                        distinct.dedup();
                        for r in distinct {
                            *census.opaque_rules.entry(r.clone()).or_default() += 1;
                        }
                        for r in &reasons {
                            *census.opaque_premises.entry(r.clone()).or_default() += 1;
                        }
                    }
                }
                Err(_) => {
                    // Total-load guarantee: a fully-opaque fallback clause.
                    // This push is INFALLIBLE — dropping a clause here would
                    // shift every subsequent clause index and corrupt the
                    // combined set's addressing contract (`total.rs` module
                    // docs). On a secondary encode failure the body falls
                    // back to a constant (the clause is underivable via its
                    // opaque premise either way, so the body is
                    // informational only); the term constructions below
                    // cannot fail on constant inputs, and an impossible
                    // failure is a hard panic, never a silent drop.
                    census.fallback_rules += 1;
                    *census
                        .opaque_rules
                        .entry("rule-error".to_string())
                        .or_default() += 1;
                    let mut metavars = Vec::new();
                    let SpecTecRule::Rule { e, .. } = &pre.rule;
                    encode::collect_metavars(e, &mut metavars);
                    let body = encode_exp(e).unwrap_or_else(|_| con("rule-error"));
                    let clause = Clause {
                        metavars,
                        prems: vec![LowerPrem::Judgement(
                            opaque("rule-error", body.clone())
                                .expect("opaque judgement on a built body"),
                        )],
                        concl: tag(x.as_str(), body).expect("relation tag on a built body"),
                    };
                    clauses.push(clause);
                }
            }
        }
    }
    census.iter_embedded_calls = fl.iter_embedded_calls;
    // Addressing contract, hard-asserted: exactly one clause per spec rule —
    // a mismatch would shift every subsequent `ClauseMeta` (see `total.rs`).
    assert_eq!(
        clauses.len(),
        census.total_rules,
        "spec_rule_clauses: one clause per rule"
    );
    (clauses, star_aux, census)
}

/// Lower **every** relation rule in `defs` into one combined clause list:
/// rule clauses (one per rule, in flattened relation/rule order), then the
/// star aux clauses, then the on-demand evaluator clauses — ready for
/// [`super::rule_set_of`]. For the rules + `Dec` graphs + evaluators combined
/// set, use [`super::total::total_spec_clauses`].
pub fn spec_clauses_v2(defs: &[SpecTecDef]) -> (Vec<Clause>, CensusReport) {
    let cat = CaseCatalogue::new(defs);
    let mut fl = Flattener::new(&cat);
    let (mut clauses, star_aux, mut census) = spec_rule_clauses(defs, &mut fl);
    clauses.extend(star_aux);
    let ev = fl.drain_ev_clauses();
    census.evaluator_clauses = ev.len();
    census.neq_pairs = fl.neq_pairs();
    clauses.extend(ev);
    (clauses, census)
}

fn collect_rels<'a>(defs: &'a [SpecTecDef], out: &mut Vec<&'a SpecTecDef>) {
    for d in defs {
        match d {
            SpecTecDef::Rel { .. } => out.push(d),
            SpecTecDef::Rec { ds } => collect_rels(ds, out),
            _ => {}
        }
    }
}

// ===========================================================================
// Side-theorem helper (ground discharge)
// ===========================================================================

/// Prove an instantiated `Side` antecedent outright: `reduce` to `T` (or to
/// `¬F` for disequations), or `refl` for a syntactic `t = t` equation. Gates,
/// never fabricates — a false or non-computable side errors.
pub fn prove_side(t: &Term) -> Result<Thm> {
    // A syntactic equation `a = a` discharges by refl (the structural-equality
    // conditions over encodings).
    if let Some((a, b)) = t.as_eq()
        && a == b
    {
        return Thm::refl(a.clone());
    }
    let red = t.reduce()?; // ⊢ t = v
    let v = red
        .concl()
        .as_eq()
        .ok_or(covalence_core::Error::NotAnEquation)?
        .1
        .clone();
    if v.as_bool() == Some(true) {
        return red.eqt_elim();
    }
    if v == mk_bool(false).not()? {
        // ⊢ t = ¬F and ⊢ ¬F give ⊢ t.
        let f = mk_bool(false);
        let not_false = Thm::assume(f.clone())?.imp_intro(&f)?.not_intro()?;
        return red.sym()?.eq_mp(not_false);
    }
    Err(flatten_err(format!(
        "side condition reduced to `{v}`, not a tautology"
    )))
}

// ===========================================================================
// Small shared helpers
// ===========================================================================

fn is_nat_arith(op: &SpecTecBinOp, t: &SpecTecOpTyp) -> bool {
    matches!(
        op,
        SpecTecBinOp::Add
            | SpecTecBinOp::Sub
            | SpecTecBinOp::Mul
            | SpecTecBinOp::Div
            | SpecTecBinOp::Mod
            | SpecTecBinOp::Pow
    ) && is_nat_ty(t)
}

fn is_nat_ty(t: &SpecTecOpTyp) -> bool {
    matches!(t, SpecTecOpTyp::Num(SpecTecNumTyp::Nat))
}

fn is_int_ty(t: &SpecTecOpTyp) -> bool {
    matches!(t, SpecTecOpTyp::Num(SpecTecNumTyp::Int))
}

fn nat_arith_fn(op: &SpecTecBinOp) -> Result<Term> {
    Ok(match op {
        SpecTecBinOp::Add => nat::nat_add(),
        SpecTecBinOp::Sub => nat::nat_sub(),
        SpecTecBinOp::Mul => nat::nat_mul(),
        SpecTecBinOp::Div => nat::nat_div(),
        SpecTecBinOp::Mod => nat::nat_mod(),
        SpecTecBinOp::Pow => nat::nat_pow(),
        other => return Err(flatten_err(format!("not nat arithmetic: {other:?}"))),
    })
}

/// Elaborated `Eq`/`Ne` carry `t: Bool` — numeric-ness is decided
/// *structurally*: some side witnesses nat-ness and both sides denote.
fn cmp_is_nat_arith(op: &SpecTecCmpOp, t: &SpecTecOpTyp, e1: &SpecTecExp, e2: &SpecTecExp) -> bool {
    use SpecTecCmpOp as C;
    match op {
        C::Lt | C::Gt | C::Le | C::Ge => is_nat_ty(t),
        C::Eq | C::Ne => {
            (nat_witness(e1) || nat_witness(e2)) && shape_ndenotes(e1) && shape_ndenotes(e2)
        }
    }
}

/// Evidence that an expression is nat-valued.
fn nat_witness(e: &SpecTecExp) -> bool {
    use SpecTecExp as E;
    match e {
        E::Num {
            n: SpecTecNum::Nat(_),
        } => true,
        E::Bin { op, t, .. } => is_nat_arith(op, t),
        E::Len { .. } => true,
        _ => false,
    }
}

/// The *shape* half of `can_ndenote` (variable numeric-ness is decided by the
/// pre-scan, which uses this before the numeric set exists).
fn shape_ndenotes(e: &SpecTecExp) -> bool {
    use SpecTecExp as E;
    match e {
        E::Num {
            n: SpecTecNum::Nat(_),
        }
        | E::Var { .. }
        | E::Len { .. }
        | E::Call { .. }
        | E::Uncase { .. }
        | E::Proj { .. }
        | E::Dot { .. }
        | E::Idx { .. } => true,
        E::Bin { op, t, e1, e2 } => is_nat_arith(op, t) && shape_ndenotes(e1) && shape_ndenotes(e2),
        E::Cvt { .. } => shape_nat_cvt(e),
        _ => false,
    }
}

fn shape_nat_cvt(e: &SpecTecExp) -> bool {
    use SpecTecExp as E;
    match e {
        E::Cvt {
            nt1: SpecTecNumTyp::Rat,
            nt2: SpecTecNumTyp::Nat,
            e1,
        } => matches!(
            &**e1,
            E::Bin {
                op: SpecTecBinOp::Div,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
                e1,
                e2,
            } if matches!(&**e1, E::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Rat,
                e1,
            } if shape_ndenotes(e1))
                && matches!(&**e2, E::Cvt {
                    nt1: SpecTecNumTyp::Nat,
                    nt2: SpecTecNumTyp::Rat,
                    e1,
                } if shape_ndenotes(e1))
        ),
        E::Cvt {
            nt1: SpecTecNumTyp::Int,
            nt2: SpecTecNumTyp::Nat,
            e1,
        } => matches!(
            &**e1,
            E::Bin {
                op: SpecTecBinOp::Sub,
                t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
                e1,
                e2,
            } if matches!(&**e1, E::Cvt {
                nt1: SpecTecNumTyp::Nat,
                nt2: SpecTecNumTyp::Int,
                e1,
            } if shape_ndenotes(e1))
                && matches!(&**e2, E::Cvt {
                    nt1: SpecTecNumTyp::Nat,
                    nt2: SpecTecNumTyp::Int,
                    e1,
                } if shape_ndenotes(e1))
        ),
        _ => false,
    }
}

fn shape_rat_nat(e: &SpecTecExp) -> bool {
    use SpecTecExp as E;
    match e {
        E::Cvt {
            nt1: SpecTecNumTyp::Nat,
            nt2: SpecTecNumTyp::Rat,
            e1,
        } => shape_ndenotes(e1),
        E::Bin {
            op: SpecTecBinOp::Div | SpecTecBinOp::Mul | SpecTecBinOp::Add,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
            e1,
            e2,
        } => shape_rat_nat(e1) && shape_rat_nat(e2),
        _ => false,
    }
}

/// Recognise the exact positive-natural equality fragment
/// `(int a : rat) / (int b : rat) = (nat n : rat)`.
fn signed_div_eq_pos_nat_shape<'a>(
    quotient: &'a SpecTecExp,
    positive_nat: &'a SpecTecExp,
) -> Option<(&'a SpecTecExp, &'a SpecTecExp, &'a SpecTecExp)> {
    use SpecTecExp as E;
    let E::Bin {
        op: SpecTecBinOp::Div,
        t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
        e1,
        e2,
    } = quotient
    else {
        return None;
    };
    let (
        E::Cvt {
            nt1: SpecTecNumTyp::Int,
            nt2: SpecTecNumTyp::Rat,
            e1: numerator,
        },
        E::Cvt {
            nt1: SpecTecNumTyp::Int,
            nt2: SpecTecNumTyp::Rat,
            e1: denominator,
        },
        E::Cvt {
            nt1: SpecTecNumTyp::Nat,
            nt2: SpecTecNumTyp::Rat,
            e1: target,
        },
    ) = (&**e1, &**e2, positive_nat)
    else {
        return None;
    };
    shape_ndenotes(target).then_some((&**numerator, &**denominator, &**target))
}

fn strip_sub(e: &SpecTecExp) -> &SpecTecExp {
    match e {
        SpecTecExp::Sub { e1, .. } => strip_sub(e1),
        other => other,
    }
}

/// If `e` is the disequation `subject =/= []` (empty list literal on the
/// right — the corpus frame-guard shape), the subject; else `None`.
fn ne_empty_subject(e: &SpecTecExp) -> Option<&SpecTecExp> {
    use SpecTecExp as E;
    match e {
        E::Cmp {
            op: SpecTecCmpOp::Ne,
            e1,
            e2,
            ..
        } if matches!(&**e2, E::List { es } if es.is_empty()) => Some(e1),
        _ => None,
    }
}

/// Whether a `Call` occurs anywhere under `e`.
fn contains_call(e: &SpecTecExp) -> bool {
    if matches!(e, SpecTecExp::Call { .. }) {
        return true;
    }
    children(e).into_iter().any(contains_call)
}

/// A residual **value-dead** operator node in an equation side (R3-F1): one
/// the cond-mode encoder leaves as a coarse spine while ground SpecTec values
/// of the same expression encode as plain values — so a `Side` equation
/// containing it could never be discharged at a genuine ground point (and
/// cond-mode flattening of its *children* may inject fresh metavars no
/// judgement-position key carries). Censused (`cond.coarse-eq`) instead of
/// silently loading a dead equation. Slices are no longer in this set: they
/// lower through exact `ev.slice` decomposition.
///
/// Iteration nodes are deliberately **not** flagged: they are encoded
/// wholesale as self-contained syntactic keys, identical in judgement and
/// condition positions and injective since R1-F1, so iter-equations fire
/// spine-keyed (`Step_read/block`'s `t_1*`/`t_2*` constraints) — the scan
/// skips their subtrees too.
fn coarse_eq_reason(e: &SpecTecExp) -> Option<&'static str> {
    use SpecTecExp as E;
    match encode::canon(e) {
        E::Iter { .. } => None,
        E::Cvt { .. } => Some("cond.coarse-eq"),
        other => children(other).into_iter().find_map(coarse_eq_reason),
    }
}

/// All direct child expressions of a node (total; used by scans here and by
/// the star leg's coarse-access census).
pub(crate) fn children(e: &SpecTecExp) -> Vec<&SpecTecExp> {
    use SpecTecExp as E;
    match e {
        E::Var { .. } | E::Bool { .. } | E::Num { .. } | E::Text { .. } => vec![],
        E::Un { e2, .. } => vec![e2],
        E::Bin { e1, e2, .. } | E::Cmp { e1, e2, .. } => vec![e1, e2],
        E::Idx { e1, e2 } | E::Comp { e1, e2 } | E::Mem { e1, e2 } | E::Cat { e1, e2 } => {
            vec![e1, e2]
        }
        E::Slice { e1, e2, e3 } => vec![e1, e2, e3],
        E::Upd { e1, path, e2 } | E::Ext { e1, path, e2 } => {
            let mut out = vec![&**e1, &**e2];
            path_exprs(path, &mut out);
            out
        }
        E::Str { efs } => efs
            .iter()
            .map(|SpecTecExpField::Field { e, .. }| e)
            .collect(),
        E::Dot { e1, .. }
        | E::Len { e1 }
        | E::Proj { e1, .. }
        | E::Case { e1, .. }
        | E::Uncase { e1, .. }
        | E::Unopt { e1 }
        | E::Lift { e1 }
        | E::Cvt { e1, .. }
        | E::Sub { e1, .. } => vec![e1],
        E::Tup { es } | E::List { es } => es.iter().collect(),
        E::Call { as1, .. } => as1
            .iter()
            .filter_map(|a| match a {
                SpecTecArg::Exp { e } => Some(e),
                _ => None,
            })
            .collect(),
        E::Iter { e1, .. } => vec![e1],
        E::Opt { eo } => eo.iter().map(|b| &**b).collect(),
    }
}

fn path_exprs<'e>(p: &'e SpecTecPath, out: &mut Vec<&'e SpecTecExp>) {
    match p {
        SpecTecPath::Root => {}
        SpecTecPath::Idx { p1, e } => {
            out.push(e);
            path_exprs(p1, out);
        }
        SpecTecPath::Slice { p1, e1, e2 } => {
            out.push(e1);
            out.push(e2);
            path_exprs(p1, out);
        }
        SpecTecPath::Dot { p1, .. } => path_exprs(p1, out),
    }
}

fn shape_name(e: &SpecTecExp) -> &'static str {
    use SpecTecExp as E;
    match e {
        E::Var { .. } => "var",
        E::Bool { .. } => "bool",
        E::Num { .. } => "num",
        E::Text { .. } => "text",
        E::Un { .. } => "un",
        E::Bin { .. } => "bin",
        E::Cmp { .. } => "cmp",
        E::Idx { .. } => "idx",
        E::Slice { .. } => "slice",
        E::Upd { .. } => "upd",
        E::Ext { .. } => "ext",
        E::Str { .. } => "str",
        E::Dot { .. } => "dot",
        E::Comp { .. } => "comp",
        E::Mem { .. } => "mem",
        E::Len { .. } => "len",
        E::Tup { .. } => "tup",
        E::Call { .. } => "call",
        E::Iter { .. } => "iter",
        E::Proj { .. } => "proj",
        E::Case { .. } => "case",
        E::Uncase { .. } => "uncase",
        E::Opt { .. } => "opt",
        E::Unopt { .. } => "unopt",
        E::List { .. } => "list",
        E::Lift { .. } => "lift",
        E::Cat { .. } => "cat",
        E::Cvt { .. } => "cvt",
        E::Sub { .. } => "sub",
    }
}

/// The monomorphised graph-relation name of a call: `f` plus one `$<op>`
/// suffix per **`Def`** argument (constant function-name ops, in argument
/// order) — exactly the tag the `Dec` graph-relation leg emits
/// ([`super::decs`] module docs), so call-site premises meet their clauses.
///
/// `Typ` arguments contribute **nothing** (neither spine slot nor tag key):
/// no `Dec` in the corpus dispatches on a type argument (measured 30/30 `Typ`
/// LHS args are plain type variables), so the graph relations are
/// type-generic and dropping is collision-free. `Gram` arguments never occur
/// (a call carrying one gets `dec.gram-arg` opaque residue on the `Dec` side
/// and simply an unclosed tag here — underivable, sound).
fn call_fn_name(f: &str, as1: &[SpecTecArg]) -> String {
    // `$` is the mono-tag separator: an id containing it would make the tag
    // ambiguous (R1-F5).
    debug_assert!(!f.contains('$'), "callee id contains '$': {f}");
    let mut name = f.to_string();
    for a in as1 {
        if let SpecTecArg::Def { x } = a {
            debug_assert!(!x.contains('$'), "Def-arg id contains '$': {x}");
            name.push('$');
            name.push_str(x);
        }
    }
    name
}

#[cfg(test)]
mod tests {
    use super::super::rule_set_of;
    use super::*;

    use crate::metalogic::{self, Premise};
    use crate::wasm::spec::wasm_spec;
    use covalence_spectec::ast::{MixOp, SpecTecDefTyp, SpecTecInst, SpecTecTyp, SpecTecTypCase};

    // ==== AST helpers ====

    fn var(id: &str) -> SpecTecExp {
        SpecTecExp::Var { id: id.into() }
    }
    fn num(u: u64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Nat(u),
        }
    }
    fn int_num(i: i64) -> SpecTecExp {
        SpecTecExp::Num {
            n: SpecTecNum::Int(i),
        }
    }
    fn bool_ty() -> SpecTecOpTyp {
        SpecTecOpTyp::Bool(covalence_spectec::ast::SpecTecBoolTyp::Bool)
    }
    fn eq(a: SpecTecExp, b: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Cmp {
            op: SpecTecCmpOp::Eq,
            t: bool_ty(),
            e1: Box::new(a),
            e2: Box::new(b),
        }
    }
    fn mixop(s: &str) -> MixOp {
        MixOp::new(vec![s.to_string()])
    }
    fn case(name: &str, payload: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Case {
            op: mixop(name),
            e1: Box::new(payload),
        }
    }
    fn tup(es: Vec<SpecTecExp>) -> SpecTecExp {
        SpecTecExp::Tup { es }
    }
    fn rule(name: &str, concl: SpecTecExp, prs: Vec<SpecTecPrem>) -> SpecTecRule {
        SpecTecRule::Rule {
            x: name.into(),
            ps: vec![],
            op: mixop("R"),
            e: concl,
            prs,
        }
    }
    fn if_p(e: SpecTecExp) -> SpecTecPrem {
        SpecTecPrem::If { e }
    }

    /// A tiny catalogue: `t = C(nat, nat) | D()`.
    fn tiny_defs() -> Vec<SpecTecDef> {
        let tcase = |name: &str, payload: SpecTecTyp| SpecTecTypCase::Field {
            op: mixop(name),
            t: payload,
            qs: vec![],
            prs: vec![],
        };
        vec![SpecTecDef::Typ {
            x: "t".into(),
            ps: vec![],
            insts: vec![SpecTecInst::Inst {
                ps: vec![],
                as_: vec![],
                dt: SpecTecDefTyp::Variant {
                    tcs: vec![
                        tcase(
                            "C",
                            SpecTecTyp::Tup {
                                ets: vec![
                                    covalence_spectec::ast::SpecTecTypBind::Bind {
                                        id: "a".into(),
                                        typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
                                    },
                                    covalence_spectec::ast::SpecTecTypBind::Bind {
                                        id: "b".into(),
                                        typ: SpecTecTyp::Num(SpecTecNumTyp::Nat),
                                    },
                                ],
                            },
                        ),
                        tcase("D", SpecTecTyp::Tup { ets: vec![] }),
                    ],
                },
            }],
        }]
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
    }

    /// `n = 0` fires at `n := 0` (bare-numeral currency, wrapped spine) and
    /// REFUSES at `n := 5`.
    #[test]
    fn numeric_condition_fires_and_refuses() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let r = rule("zero", var("n"), vec![if_p(eq(var("n"), num(0)))]);
        let lr = lower_rule_v2("R", &r, &mut fl).unwrap();
        assert!(fl.take_opaque_reasons().is_empty(), "fully flattened");
        assert!(lr.star_aux.is_empty());
        let clauses: Vec<Clause> = std::iter::once(lr.clause)
            .chain(fl.drain_ev_clauses())
            .collect();
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].metavars, vec!["n".to_string()]);
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();

        // n := 0 — the side is `0 = 0`, proved by refl.
        let side = prove_side(&mk_nat(0u64).equals(mk_nat(0u64)).unwrap()).unwrap();
        let der = metalogic::derive_mixed(&rs, 0, n_cl, &[mk_nat(0u64)], vec![Premise::Side(side)])
            .unwrap();
        assert_genuine(&der);
        // The spine carries the WRAPPED numeral (numeric-metavar discipline).
        let expected =
            metalogic::derivable(&rs, &tag("R", wrap_nat(mk_nat(0u64)).unwrap()).unwrap()).unwrap();
        assert_eq!(der.concl(), &expected);

        // n := 5 — the side `5 = 0` is not provable.
        assert!(prove_side(&mk_nat(5u64).equals(mk_nat(0u64)).unwrap()).is_err());
        // …and a bogus side theorem does not compose (kernel refuses).
        let wrong = prove_side(&mk_nat(5u64).equals(mk_nat(5u64)).unwrap()).unwrap();
        assert!(
            metalogic::derive_mixed(&rs, 0, n_cl, &[mk_nat(5u64)], vec![Premise::Side(wrong)])
                .is_err()
        );
    }

    #[test]
    fn rational_order_and_partial_conversions_are_exact_side_conditions() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let nat_to_rat = |e: SpecTecExp| SpecTecExp::Cvt {
            nt1: SpecTecNumTyp::Nat,
            nt2: SpecTecNumTyp::Rat,
            e1: Box::new(e),
        };
        let div = |a: SpecTecExp, b: SpecTecExp| SpecTecExp::Bin {
            op: SpecTecBinOp::Div,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
            e1: Box::new(nat_to_rat(a)),
            e2: Box::new(nat_to_rat(b)),
        };
        let cond = |numerator: u64, denominator: u64, bound: u64| SpecTecExp::Cmp {
            op: SpecTecCmpOp::Le,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Rat),
            e1: Box::new(div(num(numerator), num(denominator))),
            e2: Box::new(nat_to_rat(num(bound))),
        };

        // 32/8 ≤ 5, with the explicit 8>0 definedness premise.
        let mut fl = Flattener::new(&cat);
        let r = rule("rat-ok", case("D", tup(vec![])), vec![if_p(cond(32, 8, 5))]);
        let lr = lower_rule_v2("R", &r, &mut fl).unwrap();
        assert!(fl.take_opaque_reasons().is_empty());
        let side_thms = lr
            .clause
            .prems
            .iter()
            .map(|p| match p {
                LowerPrem::Side(s) => prove_side(s).map(Premise::Side),
                LowerPrem::Judgement(_) => panic!("literal rational comparison needs no graph"),
            })
            .collect::<Result<Vec<_>>>()
            .unwrap();
        let rs = rule_set_of(vec![lr.clause]);
        let d = metalogic::derive_mixed(&rs, 0, 1, &[], side_thms).unwrap();
        assert_genuine(&d);

        // Division by zero is refused by the generated positivity premise.
        let mut fl = Flattener::new(&cat);
        let bad = rule(
            "rat-zero",
            case("D", tup(vec![])),
            vec![if_p(cond(32, 0, 5))],
        );
        let lr = lower_rule_v2("R", &bad, &mut fl).unwrap();
        assert!(
            lr.clause
                .prems
                .iter()
                .any(|p| matches!(p, LowerPrem::Side(s) if prove_side(s).is_err())),
            "zero denominator must make the clause underivable"
        );
    }

    /// Integer ordering is evaluated over the canonical sign/magnitude
    /// encoding instead of being parked behind `opaque.cond.cmp-nonnat`.
    #[test]
    fn integer_order_condition_fires_through_ev() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let cond = SpecTecExp::Cmp {
            op: SpecTecCmpOp::Lt,
            t: SpecTecOpTyp::Num(SpecTecNumTyp::Int),
            e1: Box::new(var("a")),
            e2: Box::new(var("b")),
        };
        let r = rule("int-lt", tup(vec![var("a"), var("b")]), vec![if_p(cond)]);
        let mut clauses = vec![lower_rule_v2("R", &r, &mut fl).unwrap().clause];
        assert!(fl.take_opaque_reasons().is_empty(), "fully flattened");
        clauses.extend(fl.drain_ev_clauses());
        assert_eq!(clauses.len(), 4, "rule + three int.lt clauses");
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();

        // The negative→positive clause is premise-free: -2 < 3.
        let d_lt =
            metalogic::derive_mixed(&rs, 3, n_cl, &[mk_nat(2u64), mk_nat(3u64)], vec![]).unwrap();
        let a = encode_exp(&int_num(-2)).unwrap();
        let b = encode_exp(&int_num(3)).unwrap();
        let d_rule =
            metalogic::derive_mixed(&rs, 0, n_cl, &[a, b], vec![Premise::Derivation(d_lt)])
                .unwrap();
        assert_genuine(&d_rule);

        // Positive magnitudes use the real HOL-natural ordering side.
        let side = nat::nat_lt()
            .apply(mk_nat(2u64))
            .unwrap()
            .apply(mk_nat(3u64))
            .unwrap();
        let side = prove_side(&side).unwrap();
        let d_pos = metalogic::derive_mixed(
            &rs,
            1,
            n_cl,
            &[mk_nat(2u64), mk_nat(3u64)],
            vec![Premise::Side(side)],
        )
        .unwrap();
        assert_genuine(&d_pos);
    }

    /// An `Uncase`/`Proj` condition fires through on-demand `ev.*` clauses.
    #[test]
    fn uncase_proj_condition_fires_through_ev() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        // R(x)  if  (x as C).0 = 1
        let cond = eq(
            SpecTecExp::Proj {
                e1: Box::new(SpecTecExp::Uncase {
                    e1: Box::new(var("x")),
                    op: mixop("C"),
                }),
                i: 0,
            },
            num(1),
        );
        let r = rule("c0", var("x"), vec![if_p(cond)]);
        let mut clauses = vec![lower_rule_v2("R", &r, &mut fl).unwrap().clause];
        assert!(fl.take_opaque_reasons().is_empty(), "fully flattened");
        let ev = fl.drain_ev_clauses();
        assert_eq!(ev.len(), 1 + evalrel::MAX_TUPLE, "uncase + proj clauses");
        clauses.extend(ev);
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();

        // Ground instance: x := C(1, 5).
        let payload = tup(vec![num(1), num(5)]);
        let x_val = case("C", payload.clone());
        let x_enc = encode_exp(&x_val).unwrap();
        let payload_enc = encode_exp(&payload).unwrap();

        // ev.uncase.C — clause 1.
        let der_uncase =
            metalogic::derive_mixed(&rs, 1, n_cl, &[payload_enc.clone()], vec![]).unwrap();
        // ev.proj.0 at arity 2 — clause 1 (rule) + 1 (uncase) + arity offset.
        let proj_idx = 2 + (2 - 1);
        let der_proj = metalogic::derive_mixed(
            &rs,
            proj_idx,
            n_cl,
            &[encode_exp(&num(1)).unwrap(), encode_exp(&num(5)).unwrap()],
            vec![],
        )
        .unwrap();
        // The side `1 = 1`.
        let side = prove_side(&mk_nat(1u64).equals(mk_nat(1u64)).unwrap()).unwrap();

        let der = metalogic::derive_mixed(
            &rs,
            0,
            n_cl,
            &[x_enc.clone(), payload_enc, mk_nat(1u64)],
            vec![
                Premise::Derivation(der_uncase),
                Premise::Derivation(der_proj),
                Premise::Side(side),
            ],
        )
        .unwrap();
        assert_genuine(&der);
        let expected = metalogic::derivable(&rs, &tag("R", x_enc).unwrap()).unwrap();
        assert_eq!(der.concl(), &expected);
    }

    /// A structural equation `x = C()` fires by refl at the genuine instance.
    #[test]
    fn structural_equation_fires_by_refl() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let d_val = case("D", tup(vec![]));
        let r = rule("d0", var("x"), vec![if_p(eq(var("x"), d_val.clone()))]);
        let clauses = vec![lower_rule_v2("R", &r, &mut fl).unwrap().clause];
        assert!(fl.take_opaque_reasons().is_empty());
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();

        let d_enc = encode_exp(&d_val).unwrap();
        // x := D(): the instantiated side is the syntactic `⌜D()⌝ = ⌜D()⌝`.
        let side = prove_side(&d_enc.clone().equals(d_enc.clone()).unwrap()).unwrap();
        let der =
            metalogic::derive_mixed(&rs, 0, n_cl, &[d_enc.clone()], vec![Premise::Side(side)])
                .unwrap();
        assert_genuine(&der);
        assert_eq!(
            der.concl(),
            &metalogic::derivable(&rs, &tag("R", d_enc.clone()).unwrap()).unwrap()
        );

        // x := C(1,5): the side is a non-trivial uninterpreted equation.
        let c_enc = encode_exp(&case("C", tup(vec![num(1), num(5)]))).unwrap();
        assert!(prove_side(&c_enc.equals(d_enc).unwrap()).is_err());
    }

    /// R1-F1 end-to-end regression (the reviewer's scratch shape): a rule
    /// whose condition equates map-iterations over **distinct domains**
    /// (`C(x)*{x<-xs} = C(x)*{x<-ys}`) must NOT load with a vacuous side.
    /// Pre-fix, `encode` dropped the iteration binders+domains, both sides
    /// encoded identically, the side was `t = t`, and the rule derived a
    /// false fact at every well-sorted point. Now the side is a non-trivial
    /// equation: underivable as loaded, underivable at distinct ground
    /// domains, and refl-dischargeable exactly at equal domains (where the
    /// SpecTec condition is genuinely true).
    #[test]
    fn map_equality_over_distinct_domains_is_not_vacuous() {
        use crate::wasm::encode::{metavar_name, phi};
        use covalence_core::Var;
        use covalence_core::subst::subst_free;
        use covalence_spectec::ast::SpecTecIterExp;

        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let case_map = |dom: &str| SpecTecExp::Iter {
            e1: Box::new(case("C", var("x"))),
            it: SpecTecIter::List,
            xes: vec![SpecTecIterExp::Dom {
                x: "x".into(),
                e: var(dom),
            }],
        };
        let r = rule(
            "mapeq",
            tup(vec![var("xs"), var("ys")]),
            vec![if_p(eq(case_map("xs"), case_map("ys")))],
        );
        let lr = lower_rule_v2("R", &r, &mut fl).unwrap();
        assert!(fl.take_opaque_reasons().is_empty(), "loads as a Side");
        let side = lr
            .clause
            .prems
            .iter()
            .find_map(|p| match p {
                LowerPrem::Side(s) => Some(s.clone()),
                _ => None,
            })
            .expect("a Side equation");
        let (a, b) = side.as_eq().expect("an equation");
        assert_ne!(a, b, "R1-F1: the side must not be vacuous at load");
        assert!(prove_side(&side).is_err(), "open side is not dischargeable");

        // Distinct ground domains keep the sides distinct (underivable) …
        let l1 = encode_exp(&SpecTecExp::List { es: vec![num(1)] }).unwrap();
        let l2 = encode_exp(&SpecTecExp::List { es: vec![num(2)] }).unwrap();
        let at = |t: &Term, xs: &Term, ys: &Term| {
            let t = subst_free(t, &Var::new(metavar_name("xs"), phi()), xs);
            subst_free(&t, &Var::new(metavar_name("ys"), phi()), ys)
        };
        assert!(prove_side(&at(&side, &l1, &l2)).is_err());
        // … while equal domains discharge by refl (genuinely-true point).
        assert!(prove_side(&at(&side, &l1, &l1)).is_ok());
    }

    /// R1-F2 end-to-end regression (the reviewer's scratch shape): a rule
    /// whose condition equates updates at **distinct indices**
    /// (`s[0 := 9] = s[1 := 9]`) must not load with a vacuous side — the path
    /// index expressions are part of the encoding now.
    #[test]
    fn upd_equality_over_distinct_indices_is_not_vacuous() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let upd = |i: u64| SpecTecExp::Upd {
            e1: Box::new(var("s")),
            path: Box::new(SpecTecPath::Idx {
                p1: Box::new(SpecTecPath::Root),
                e: num(i),
            }),
            e2: Box::new(num(9)),
        };
        let r = rule("updeq", var("s"), vec![if_p(eq(upd(0), upd(1)))]);
        let lr = lower_rule_v2("R", &r, &mut fl).unwrap();
        assert!(fl.take_opaque_reasons().is_empty(), "loads as a Side");
        let side = lr
            .clause
            .prems
            .iter()
            .find_map(|p| match p {
                LowerPrem::Side(s) => Some(s.clone()),
                _ => None,
            })
            .expect("a Side equation");
        let (a, b) = side.as_eq().expect("an equation");
        assert_ne!(a, b, "R1-F2: the side must not be vacuous at load");
        assert!(prove_side(&side).is_err(), "no instance can discharge it");
    }

    /// A slice equation lowers through the exact `ev.slice` relation rather
    /// than retaining a value-dead structural spine.
    #[test]
    fn slice_equation_uses_exact_evaluator() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let slice = SpecTecExp::Slice {
            e1: Box::new(var("s")),
            e2: Box::new(num(0)),
            e3: Box::new(num(2)),
        };
        let r = rule("sl", var("s"), vec![if_p(eq(slice, var("l")))]);
        let lr = lower_rule_v2("R", &r, &mut fl).unwrap();
        assert!(fl.take_opaque_reasons().is_empty());
        fn contains(t: &Term, name: &str) -> bool {
            t.as_free().is_some_and(|v| v.name() == name)
                || t.as_app()
                    .is_some_and(|(f, a)| contains(f, name) || contains(a, name))
                || t.as_abs().is_some_and(|(_, b)| contains(b, name))
        }
        assert!(lr.clause.prems.iter().any(|p| match p {
            LowerPrem::Judgement(j) => contains(j, "st$c$rel.ev.slice"),
            LowerPrem::Side(_) => false,
        }));
    }

    /// A structural disequality `x =/= D()` fires through an on-demand
    /// `ev.neq` tag-pair clause at `x := C(…)` — and only distinct-tag pairs
    /// exist, so `x := D()` has no derivation.
    #[test]
    fn structural_disequality_fires_through_ev_neq() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let d_val = case("D", tup(vec![]));
        let cond = SpecTecExp::Cmp {
            op: SpecTecCmpOp::Ne,
            t: bool_ty(),
            e1: Box::new(var("x")),
            e2: Box::new(d_val.clone()),
        };
        let mut clauses = vec![
            lower_rule_v2("R", &rule("nd", var("x"), vec![if_p(cond)]), &mut fl)
                .unwrap()
                .clause,
        ];
        assert!(fl.take_opaque_reasons().is_empty(), "fully flattened");
        assert_eq!(fl.neq_pairs(), 1, "one ordered pair (C, D)");
        let ev = fl.drain_ev_clauses();
        assert_eq!(ev.len(), 1);
        clauses.extend(ev);
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();

        // x := C(1,5): derive ev.neq(C(...), D()) via the pair clause.
        let payload = tup(vec![num(1), num(5)]);
        let x_enc = encode_exp(&case("C", payload.clone())).unwrap();
        let payload_enc = encode_exp(&payload).unwrap();
        let d_payload_enc = encode_exp(&tup(vec![])).unwrap();
        let der_neq =
            metalogic::derive_mixed(&rs, 1, n_cl, &[payload_enc, d_payload_enc], vec![]).unwrap();
        let der = metalogic::derive_mixed(
            &rs,
            0,
            n_cl,
            &[x_enc.clone()],
            vec![Premise::Derivation(der_neq)],
        )
        .unwrap();
        assert_genuine(&der);
        assert_eq!(
            der.concl(),
            &metalogic::derivable(&rs, &tag("R", x_enc).unwrap()).unwrap()
        );

        // x := D(): the pair clause is (C, D) — instantiating it with D's
        // payload still yields a C-headed left spine, which cannot match the
        // premise instance `ev.neq(⌜D()⌝, ⌜D()⌝)`; the kernel refuses.
        let d_enc = encode_exp(&d_val).unwrap();
        let wrong =
            metalogic::derive_mixed(&rs, 1, n_cl, &[encode_exp(&tup(vec![])).unwrap()], vec![])
                .unwrap();
        assert!(
            metalogic::derive_mixed(&rs, 0, n_cl, &[d_enc], vec![Premise::Derivation(wrong)])
                .is_err()
        );
    }

    /// `|l| = 2` fires through the `ev.len` snoc recursion, with real-nat
    /// successor terms as the instantiation currency.
    #[test]
    fn len_condition_fires_through_ev_len() {
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let cond = eq(
            SpecTecExp::Len {
                e1: Box::new(var("l")),
            },
            num(2),
        );
        let r = rule("len2", var("l"), vec![if_p(cond)]);
        let mut clauses = vec![lower_rule_v2("R", &r, &mut fl).unwrap().clause];
        assert!(fl.take_opaque_reasons().is_empty());
        clauses.extend(fl.drain_ev_clauses());
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();
        assert_eq!(n_cl, 3, "rule + len base + len step");

        // l := [7, 8] as an encoded snoc spine.
        let e7 = encode_exp(&num(7)).unwrap();
        let e8 = encode_exp(&num(8)).unwrap();
        let l0 = con("list");
        let l1 = app(l0.clone(), e7.clone()).unwrap();
        let l2 = app(l1.clone(), e8.clone()).unwrap();

        // Chain with literal successor witnesses:
        // len([],0); len([7],1); len([7,8],2).
        let zero = mk_nat(0u64);
        let one = mk_nat(1u64);
        let two = mk_nat(2u64);
        let der0 = metalogic::derive_mixed(&rs, 1, n_cl, &[], vec![]).unwrap();
        let side1 = prove_side(
            &one.clone()
                .equals(Term::succ().apply(zero.clone()).unwrap())
                .unwrap(),
        )
        .unwrap();
        let der1 = metalogic::derive_mixed(
            &rs,
            2,
            n_cl,
            &[l0, e7, zero, one.clone()],
            vec![Premise::Side(side1), Premise::Derivation(der0)],
        )
        .unwrap();
        let side2 = prove_side(
            &two.clone()
                .equals(Term::succ().apply(one.clone()).unwrap())
                .unwrap(),
        )
        .unwrap();
        let der2 = metalogic::derive_mixed(
            &rs,
            2,
            n_cl,
            &[l1, e8, one, two.clone()],
            vec![Premise::Side(side2), Premise::Derivation(der1)],
        )
        .unwrap();

        // The rule at l := [7,8], %f0 := 2.
        let side = prove_side(&two.clone().equals(mk_nat(2u64)).unwrap()).unwrap();
        let der = metalogic::derive_mixed(
            &rs,
            0,
            n_cl,
            &[l2.clone(), two],
            vec![Premise::Derivation(der2), Premise::Side(side)],
        )
        .unwrap();
        assert_genuine(&der);
        assert_eq!(
            der.concl(),
            &metalogic::derivable(&rs, &tag("R", l2).unwrap()).unwrap()
        );
    }

    /// A synthetic 3-rule `Else` group: negations of the earlier siblings'
    /// guards are injected, and the `otherwise` rule fires exactly off-guard.
    #[test]
    fn else_group_synthetic_end_to_end() {
        let concl = |k: u64| tup(vec![case("A", tup(vec![var("n")])), num(k)]);
        let rules = vec![
            rule("r1", concl(1), vec![if_p(eq(var("n"), num(0)))]),
            rule(
                "r2",
                concl(2),
                vec![SpecTecPrem::Else, if_p(eq(var("n"), num(1)))],
            ),
            rule("r3", concl(3), vec![SpecTecPrem::Else]),
        ];
        let pre = preprocess_else(&rules);
        assert_eq!(pre[0].status, ElseStatus::NoElse);
        assert_eq!(pre[1].status, ElseStatus::Rewritten { negated: 1 });
        assert_eq!(pre[2].status, ElseStatus::Rewritten { negated: 2 });

        // r3's premises are ¬(n = 0), ¬(n = 1) as Ne conditions.
        let SpecTecRule::Rule { prs, .. } = &pre[2].rule;
        assert_eq!(prs.len(), 2);
        let ne = |k: u64| SpecTecExp::Cmp {
            op: SpecTecCmpOp::Ne,
            t: bool_ty(),
            e1: Box::new(var("n")),
            e2: Box::new(num(k)),
        };
        assert_eq!(prs[0], if_p(ne(0)));
        assert_eq!(prs[1], if_p(ne(1)));

        // Lower r3 and fire it at n := 5; refuse at n := 0.
        let defs = tiny_defs();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let clauses = vec![lower_rule_v2("S", &pre[2].rule, &mut fl).unwrap().clause];
        assert!(fl.take_opaque_reasons().is_empty(), "fully flattened");
        let rs = rule_set_of(clauses);
        let n_cl = rs.n_clauses().unwrap();

        let side =
            |k: u64| prove_side(&mk_nat(5u64).equals(mk_nat(k)).unwrap().not().unwrap()).unwrap();
        let der = metalogic::derive_mixed(
            &rs,
            0,
            n_cl,
            &[mk_nat(5u64)],
            vec![Premise::Side(side(0)), Premise::Side(side(1))],
        )
        .unwrap();
        assert_genuine(&der);
        // Refusal: at n := 0 the first negation `¬(0 = 0)` is unprovable.
        assert!(prove_side(&mk_nat(0u64).equals(mk_nat(0u64)).unwrap().not().unwrap()).is_err());
    }

    /// The real `table.fill` group from the bundled spec: `Else` premises
    /// rewrite into exactly the expected negations of the earlier guards.
    #[test]
    fn else_real_table_fill_group() {
        let defs = wasm_spec();
        let mut rels = Vec::new();
        collect_rels(&defs, &mut rels);
        let step_read = rels
            .iter()
            .find_map(|d| match d {
                SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => Some(rules),
                _ => None,
            })
            .expect("Step_read relation");
        let pre = preprocess_else(step_read);

        let by_name = |name: &str| {
            pre.iter()
                .find(|p| {
                    let SpecTecRule::Rule { x, .. } = &p.rule;
                    x == name
                })
                .unwrap_or_else(|| panic!("rule {name}"))
        };
        let oob = by_name("table.fill-oob");
        let zero = by_name("table.fill-zero");
        let succ = by_name("table.fill-succ");
        assert_eq!(oob.status, ElseStatus::NoElse);
        assert_eq!(zero.status, ElseStatus::Rewritten { negated: 1 });
        assert_eq!(succ.status, ElseStatus::Rewritten { negated: 2 });

        // zero: [¬oob-guard, n = 0]; succ: [¬oob-guard, ¬(n = 0)].
        let SpecTecRule::Rule { prs: oob_prs, .. } = &oob.rule;
        let oob_guard = match &oob_prs[0] {
            SpecTecPrem::If { e } => e.clone(),
            other => panic!("oob guard: {other:?}"),
        };
        let expected_neg = negate(&oob_guard).unwrap();
        let SpecTecRule::Rule { prs: zero_prs, .. } = &zero.rule;
        assert_eq!(zero_prs.len(), 2);
        assert_eq!(zero_prs[0], if_p(expected_neg.clone()));
        // The negation flips `>` to `<=` with identical operands.
        assert!(matches!(
            &expected_neg,
            SpecTecExp::Cmp {
                op: SpecTecCmpOp::Le,
                ..
            }
        ));
        let SpecTecRule::Rule { prs: succ_prs, .. } = &succ.rule;
        assert_eq!(succ_prs.len(), 2);
        assert_eq!(succ_prs[0], if_p(expected_neg));
        assert_eq!(
            succ_prs[1],
            if_p(SpecTecExp::Cmp {
                op: SpecTecCmpOp::Ne,
                t: bool_ty(),
                e1: Box::new(var("n")),
                e2: Box::new(num(0)),
            })
        );

        // And the preprocessed rules flatten fully (no opaque residue).
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        for r in [&zero.rule, &succ.rule] {
            lower_rule_v2("Step_read", r, &mut fl).unwrap();
            let reasons = fl.take_opaque_reasons();
            assert!(reasons.is_empty(), "table.fill residue: {reasons:?}");
        }
    }

    /// The real exception-handler fallback uses the catalogue-backed finite
    /// catch complement and lowers without any opaque Else/pattern residue.
    #[test]
    fn else_real_throw_handler_finite_complement_lowers_cleanly() {
        let defs = wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut rels = Vec::new();
        collect_rels(&defs, &mut rels);
        let step_read = rels
            .iter()
            .find_map(|d| match d {
                SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => Some(rules),
                _ => None,
            })
            .expect("Step_read relation");
        let pre = preprocess_else_with_catalogue(step_read, &cat);
        let next = pre
            .iter()
            .find(|p| {
                matches!(
                    &p.rule,
                    SpecTecRule::Rule { x, .. } if x == "throw_ref-handler-next"
                )
            })
            .expect("throw_ref-handler-next");
        assert_eq!(next.status, ElseStatus::Rewritten { negated: 4 });

        let mut fl = Flattener::new(&cat);
        let lowered = lower_rule_v2("Step_read", &next.rule, &mut fl).expect("lower handler-next");
        let reasons = fl.take_opaque_reasons();
        assert!(reasons.is_empty(), "handler-next residue: {reasons:?}");
        assert!(
            !lowered.clause.prems.is_empty(),
            "the rewritten rule retains its executable guard"
        );
        assert!(
            fl.drain_ev_clauses().len() >= 2,
            "the DNF guard owns its two constructor branches"
        );
    }

    /// A sibling judgement and one condition conjunct may be shared by the
    /// current rule.  For `array.copy-gt`, the preceding `array.copy-le`
    /// clause has `Expand ∧ (i_1 <= i_2) ∧ storage-shape`, while the current
    /// clause already assumes the same `Expand ∧ storage-shape`.  Else
    /// preprocessing must therefore retain those shared premises and add
    /// only the exact complement `i_1 > i_2`.
    #[test]
    fn else_real_array_copy_factors_shared_judgement_and_conjunct() {
        let defs = wasm_spec();
        let mut rels = Vec::new();
        collect_rels(&defs, &mut rels);
        let step_read = rels
            .iter()
            .find_map(|d| match d {
                SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => Some(rules),
                _ => None,
            })
            .expect("Step_read relation");
        let pre = preprocess_else(step_read);
        let gt = pre
            .iter()
            .find(|p| matches!(&p.rule, SpecTecRule::Rule { x, .. } if x == "array.copy-gt"))
            .expect("array.copy-gt");
        assert_eq!(gt.status, ElseStatus::Rewritten { negated: 4 });

        let SpecTecRule::Rule { prs, .. } = &gt.rule;
        assert_eq!(prs.len(), 6, "4 complements + shared Expand + own guard");
        assert_eq!(
            prs.iter()
                .filter(|p| matches!(p, SpecTecPrem::Rule { x, .. } if x == "Expand"))
                .count(),
            1
        );
        assert!(
            prs.iter().any(|p| matches!(
                p,
                SpecTecPrem::If {
                    e: SpecTecExp::Cmp {
                        op: SpecTecCmpOp::Gt,
                        ..
                    }
                }
            )),
            "the le sibling contributes its exact > complement"
        );

        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        lower_rule_v2("Step_read", &gt.rule, &mut fl).unwrap();
        assert!(
            fl.take_opaque_reasons().is_empty(),
            "array.copy-gt is fully fireable"
        );
    }

    /// The packed scalar/vector loads use an exact byte slice whose count is
    /// written as `nat(rat(width) / rat(8))`.  Width ride-throughs in a ListN
    /// premise and its named index must share the numeric currency with the
    /// ordinary non-iterated forms; none of these real rules may fall back to
    /// a value-dead conversion equation.
    #[test]
    fn real_packed_load_slices_flatten_supported_conversions() {
        let defs = wasm_spec();
        let mut rels = Vec::new();
        collect_rels(&defs, &mut rels);
        let rules = rels
            .iter()
            .find_map(|d| match d {
                SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => Some(rules),
                _ => None,
            })
            .expect("Step_read relation");
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        for name in ["load-pack-val", "vload-pack-val", "vload-zero-val"] {
            let rule = rules
                .iter()
                .find(|r| matches!(r, SpecTecRule::Rule { x, .. } if x == name))
                .unwrap_or_else(|| panic!("rule {name}"));
            lower_rule_v2("Step_read", rule, &mut fl).unwrap();
            let reasons = fl.take_opaque_reasons();
            assert!(reasons.is_empty(), "{name} residue: {reasons:?}");
        }
    }

    /// R1-F1 corpus regression: `Step_read/block` was one of the 15 rules
    /// whose `Eq` conditions carried material the pre-fix encoding dropped —
    /// its label arity `n` and the block-type metavariables `t_1*`/`t_2*`/`m`
    /// vanished from the clause entirely (severed constraints, `n` fully
    /// unconstrained). With iteration binders/domains in the encoding they
    /// are `∀`-quantified clause metavariables again, and the rule is
    /// genuinely constrained (no opaque residue).
    #[test]
    fn step_read_block_constraints_restored() {
        let defs = wasm_spec();
        let cat = CaseCatalogue::new(&defs);
        let mut fl = Flattener::new(&cat);
        let mut rels = Vec::new();
        collect_rels(&defs, &mut rels);
        let (rel, r) = rels
            .iter()
            .find_map(|d| match d {
                SpecTecDef::Rel { x, rules, .. } if x == "Step_read" => rules
                    .iter()
                    .find(|r| matches!(r, SpecTecRule::Rule { x, .. } if x == "block"))
                    .map(|r| (x.as_str(), r)),
                _ => None,
            })
            .expect("Step_read/block in the bundled spec");
        let lr = lower_rule_v2(rel, r, &mut fl).unwrap();
        assert!(
            fl.take_opaque_reasons().is_empty(),
            "block flattens fully (genuinely constrained, not censused)"
        );
        for mv in ["n", "m", "t_1*", "t_2*", "val*", "instr*"] {
            assert!(
                lr.clause.metavars.iter().any(|m| m == mv),
                "metavar `{mv}` severed from Step_read/block: {:?}",
                lr.clause.metavars
            );
        }
    }

    /// The whole-spec census: ALL rules load, exact numbers printed, floors
    /// asserted. Run with `--nocapture` for the report.
    #[test]
    fn whole_spec_census() {
        let defs = wasm_spec();
        let (clauses, census) = spec_clauses_v2(&defs);

        println!("=== total-load census (relation rules) ===");
        println!("total rules:        {}", census.total_rules);
        println!("fully flattened:    {}", census.fully_flattened);
        println!(
            "  v1-lowerable {} + newly flattened {}",
            census.v1_lowerable, census.newly_flattened
        );
        println!("evaluator clauses:  {}", census.evaluator_clauses);
        println!("neq pairs:          {}", census.neq_pairs);
        println!(
            "else rewritten:     {} (failed: {:?})",
            census.else_rewritten, census.else_failed
        );
        println!(
            "iter-embedded calls (coarse spines): {}",
            census.iter_embedded_calls
        );
        println!(
            "star sites:         {} ({} aux clauses; inner-if {}, bound-flattened {}, coarse-inner {}, opaque {})",
            census.star_sites,
            census.star_aux_clauses,
            census.star_inner_if,
            census.star_bound_flattened,
            census.star_coarse_inner,
            census.star_opaque_sites
        );
        println!("fallback rules:     {}", census.fallback_rules);
        println!("--- opaque rules by reason ---");
        let mut v: Vec<_> = census.opaque_rules.iter().collect();
        v.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
        for (k, c) in &v {
            println!("  {c:>4}  {k}");
        }
        println!("--- opaque premises by reason ---");
        let mut v: Vec<_> = census.opaque_premises.iter().collect();
        v.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
        for (k, c) in &v {
            println!("  {c:>4}  {k}");
        }
        println!(
            "clauses total: {} ({} rule + {} star aux + {} evaluator)",
            clauses.len(),
            census.total_rules,
            census.star_aux_clauses,
            census.evaluator_clauses
        );

        // TOTAL LOAD: every rule yields a clause.
        assert_eq!(census.total_rules, 558, "the bundled 3.0 dump");
        assert_eq!(
            clauses.len(),
            census.total_rules + census.star_aux_clauses + census.evaluator_clauses,
            "one clause per rule + star aux + evaluator clauses"
        );
        assert_eq!(census.fallback_rules, 0, "no rule fell back to full-opaque");

        // The star leg: every Iter site lowers structurally.
        assert_eq!(census.star_sites, 92, "the corpus Iter-premise sites");
        assert_eq!(census.star_opaque_sites, 0);
        assert_eq!(census.star_aux_clauses, 184, "two aux clauses per site");

        // Coverage floors (raise as legs land — see the design note ladder).
        // Measured 2026-07-19 post encoded-nat ordering: fully flattened
        // 525 (274 v1-lowerable + 251 newly), evaluator clauses 332, neq pairs
        // 139; residue (rules; a rule may carry several): cond.cmp-nonnat 15,
        // else 8, cond.coarse-eq 10, cond.neq-open 1. Slice opacity is zero;
        // six slice expressions expose a nested unsupported conversion and
        // therefore move honestly to `cond.coarse-eq`. The drop from the
        // pre-fix 510 is CORRECT: 12 rules whose `Eq` sides carry value-dead
        // `Slice`/`Cvt` spines were counted flat while their Sides could
        // never be discharged at a genuine point — they are censused now.
        // The evaluator rise (204 → 276) is `ev.sort.*` guard families
        // attaching to metavariables the injective encoding restored to
        // their clauses (previously skipped as not-a-clause-metavar).
        let prev_skipped = census.total_rules - census.v1_lowerable;
        assert_eq!(census.v1_lowerable, 274);
        assert_eq!(prev_skipped, 284);
        assert!(
            census.fully_flattened >= 553,
            "fully flattened = {}",
            census.fully_flattened
        );
        assert!(
            census.newly_flattened >= 279,
            "newly flattened {} of {}",
            census.newly_flattened,
            prev_skipped
        );
        // 35 Else sites; exact factoring handles shared Rule judgements and
        // shared If conjuncts (`array.init_data-num`, `array.copy-gt`), while
        // the catalogue-backed finite catch complement handles
        // `throw_ref-handler-next`. The 5 remaining refusals are genuine
        // sibling-rule-premise cases (four Ref_ok complements plus
        // `array.init_data-zero`, whose predecessor applicability is a
        // Rule-and-If conjunction).
        assert!(
            census.else_rewritten >= 30,
            "else rewritten = {}",
            census.else_rewritten
        );
        assert!(census.evaluator_clauses >= 337);
        assert!(census.neq_pairs >= 135, "neq pairs = {}", census.neq_pairs);
        // R3-F1: the value-dead equation sides are censused, never silent.
        assert!(!census.opaque_rules.contains_key("cond.slice"));
        assert!(!census.opaque_rules.contains_key("cond.coarse-eq"));
    }
}
