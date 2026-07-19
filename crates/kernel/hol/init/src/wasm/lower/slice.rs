//! **Spec slices + transport** — carve a named sub-spec out of the total
//! combined clause list ([`total_spec_clauses`]) and *transport* its theorems
//! into the full set, kernel-derived — the seed of the `WASM 1.0 ⊆ 2.0 ⊆ 3.0`
//! metatheorem ladder and the maintainer direction "start building up subsets
//! of WASM as we go towards the full thing — as well as subsets of SpecTec".
//!
//! ## Slices
//!
//! A [`SpecSlice`] is a subset of the total clause list, closed under premise
//! dependencies: starting from **seeds** ([`SliceSeed`] — whole relations
//! `rel.<R>` / `fn.<f>` / `ev.*` / `star.*` by tag, or single `(relation,
//! rule-name)` rules), the carve computes the premise-tag **dependency
//! closure**: a tag is *needed* when a kept clause's premises mention it
//! (`rel.` / `fn.` / `star.` / `ev.` tags — star aux and evaluator families
//! follow their consumers; `opaque.*` tags are terminal by design: they have
//! no clauses anywhere), and every clause whose conclusion tag is needed joins
//! the slice. Order is deterministic — the total order restricted — and the
//! slice keeps its **index map** (slice index → total index), which is exactly
//! what transport consumes.
//!
//! A slice is *sound by construction*: its clause set is a subset of the full
//! set, so `Derivable_slice` under-approximates `Derivable_full` — fewer
//! judgements derivable, never more. Zero new rules, zero axioms.
//!
//! ## The transport theorem
//!
//! For a slice ⊆ full (clause-set inclusion via the index map), [`transport`]
//! turns `⊢ Derivable_slice ⌜J⌝` into `⊢ Derivable_full ⌜J⌝`, **kernel-derived
//! with zero new rules**: assume `Closed_full d`, project each slice clause
//! out of the big conjunction by `nth`-conjunct elimination through the index
//! map, re-conjoin them into `Closed_slice d`, `imp_elim` the slice theorem's
//! opened body against it, then `imp_intro`/`all_intro` back up. The kernel
//! re-checks every step: if the slice's clauses were *not* literally clauses
//! of the full set, the `imp_elim` would fail — nothing can be fabricated.
//! This is the `1.0 ⊆ 2.0 ⊆ 3.0` move in miniature: derive in the small
//! (cheap) system, transport into the big one.
//!
//! ## Preset slices (approximate, feature-based — see each builder's docs)
//!
//! - [`lime_slice`] — the minimal **maximally-fireable** core: seed rules
//!   whose every premise is dischargeable today; zero opaque premises
//!   (asserted in tests).
//! - [`exec_slice`] — lime plus the **multi-step execution closure**
//!   (`Steps` + the `Step/pure` lift + the `Step/ctxt-instrs` frame rule +
//!   `binop`/`drop`): the smallest set on which the straight-line const-fold
//!   demo runs end-to-end (see [`super::trace`]).
//! - [`wasm1_slice`] / [`wasm2_slice`] — ≈ WASM 1.0 MVP / ≈ 2.0, classified
//!   by **rule name** against hardcoded instruction lists ([`WASM1_INSTRS`] /
//!   [`WASM2_EXTRA_INSTRS`]). These are *approximations for API exercise*
//!   (rule-name classification, whole-relation granularity for non-instruction
//!   dependencies); exactness comes later from feature annotations.
//!
//! ## Example: build total, carve lime, derive, transport
//!
//! ```no_run
//! use covalence_init::wasm::spec::wasm_spec;
//! use covalence_init::wasm::lower::rule_set_of;
//! use covalence_init::wasm::lower::total::{total_spec_clauses, with_total_stack};
//! use covalence_init::wasm::lower::slice::{SliceEnv, lime_slice, transport};
//!
//! with_total_stack(|| {
//!     let defs = wasm_spec();
//!     let (clauses, report) = total_spec_clauses(&defs).unwrap();
//!     // Carve the maximally-fireable core out of the 2000+-clause total set.
//!     let lime = lime_slice(&clauses, &report.metas).unwrap();
//!     let env = SliceEnv::new(lime);
//!     // Derive `[NOP] ↪ []` in the small slice (no big stack needed).
//!     let nop = env.rule_index(Some("Step_pure"), "nop").unwrap();
//!     let small = env.derive(nop, &[], vec![]).unwrap();
//!     // Transport it into the full combined set, kernel-derived.
//!     let full = rule_set_of(clauses);
//!     let big = transport(env.slice(), &full, &small).unwrap();
//!     assert!(big.hyps().is_empty());
//! })
//! ```

use std::collections::{BTreeMap, BTreeSet};

use covalence_core::{Error, Result, Term};
use covalence_hol_eval::EvalThm as Thm;
use covalence_hol_eval::derived::DerivedRules;
use covalence_spectec::ast::SpecTecExp;

use super::super::encode::{encode_exp, tag};
use super::total::ClauseMeta;
use super::{Clause, LowerPrem, rule_set_of};
use crate::init::ext::TermExt;
use crate::metalogic::{self, Premise, RuleSet, conj_thms, derive_via_closed};

/// A seed for [`SpecSlice::carve`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SliceSeed {
    /// Every clause whose conclusion tag is this relation: a SpecTec relation
    /// name (`"Step_pure"`), a function graph (`"fn.default_"`), an evaluator
    /// family (`"ev.sort.numtype"`), or a star site (`"star.<rel>.<rule>.<i>"`).
    Relation(String),
    /// A single named rule: `(relation, rule-name)`.
    Rule(String, String),
}

impl SliceSeed {
    /// Whole-relation seed.
    pub fn relation(r: impl Into<String>) -> Self {
        SliceSeed::Relation(r.into())
    }
    /// Single-rule seed.
    pub fn rule(r: impl Into<String>, name: impl Into<String>) -> Self {
        SliceSeed::Rule(r.into(), name.into())
    }
}

/// The honest census of one slice — clause count, the opaque premises *within*
/// the slice, and the dischargeability split.
#[derive(Debug, Clone)]
pub struct SliceReport {
    /// The slice's name.
    pub name: String,
    /// Clauses in the slice.
    pub n_clauses: usize,
    /// Clauses in the total set it was carved from.
    pub n_total: usize,
    /// Opaque premises within the slice, by reason tag.
    pub opaque_tags: BTreeMap<String, usize>,
    /// Clauses carrying at least one opaque premise (can never fire).
    pub n_clauses_opaque: usize,
    /// Clauses with **no** opaque premise (fireable once their non-opaque
    /// antecedents are discharged — the dischargeability headline).
    pub n_clauses_clean: usize,
}

impl SliceReport {
    /// Total opaque premises within the slice.
    pub fn opaque_total(&self) -> usize {
        self.opaque_tags.values().sum()
    }
}

/// A named sub-spec: a premise-closed subset of the total combined clause
/// list, in total order, with its slice-index → total-index map.
#[derive(Debug, Clone)]
pub struct SpecSlice {
    name: String,
    /// Slice index → total index (strictly increasing — the total order
    /// restricted).
    indices: Vec<usize>,
    /// The slice clauses (`clauses[i]` = total clause `indices[i]`).
    clauses: Vec<Clause>,
    /// The matching [`ClauseMeta`]s, same indexing.
    metas: Vec<ClauseMeta>,
    /// Size of the total set this was carved from (transport's conjunction
    /// arity — must match the full rule set's clause count).
    n_total: usize,
}

/// The outer relation tag of a judgement/conclusion term
/// (`app(st$c$rel.<tag>, body)` → `tag`), walking the spine head like
/// `total::concl_tag`.
fn rel_tag(t: &Term) -> Option<String> {
    let mut cur = t;
    loop {
        let (f, _) = cur.as_app()?;
        match f.as_app() {
            Some((h, c)) => {
                if h.as_free().map(|v| v.name()) == Some("st$app")
                    && let Some(tag) = c.as_free().and_then(|v| v.name().strip_prefix("st$c$rel."))
                {
                    return Some(tag.to_owned());
                }
                cur = f;
            }
            None => return None,
        }
    }
}

impl SpecSlice {
    /// [`SpecSlice::carve_filtered`] with no filter (every closure-needed
    /// clause is kept).
    pub fn carve(
        clauses: &[Clause],
        metas: &[ClauseMeta],
        name: impl Into<String>,
        seeds: &[SliceSeed],
    ) -> Result<SpecSlice> {
        SpecSlice::carve_filtered(clauses, metas, name, seeds, |_| true)
    }

    /// Carve a slice out of the total clause list.
    ///
    /// `clauses`/`metas` are the parallel outputs of
    /// [`total_spec_clauses`](super::total::total_spec_clauses); `seeds` pick
    /// the starting clauses; `keep` is a clause-level filter applied to every
    /// **closure-pulled** clause (seeds are explicit and bypass it) — this is
    /// how the wasm1/wasm2 presets stop the tag-level closure from dragging a
    /// whole instruction relation back in when only a premise mentions it.
    /// Excluding clauses can only shrink the derivable set (soundness is
    /// one-way), so any filter is sound.
    ///
    /// Hard-asserts index-map integrity against the `ClauseMeta`s: every
    /// clause's conclusion tag must equal its meta's relation, and the two
    /// slices must be parallel.
    pub fn carve_filtered(
        clauses: &[Clause],
        metas: &[ClauseMeta],
        name: impl Into<String>,
        seeds: &[SliceSeed],
        keep: impl Fn(&ClauseMeta) -> bool,
    ) -> Result<SpecSlice> {
        assert_eq!(
            clauses.len(),
            metas.len(),
            "slice carve: clause/meta lists must be parallel"
        );
        // Conclusion-tag index + the ClauseMeta integrity hard-assert.
        let mut by_tag: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
        for (i, (c, m)) in clauses.iter().zip(metas).enumerate() {
            let tag = rel_tag(&c.concl).unwrap_or_else(|| {
                panic!("slice carve: clause {i} has no relation-tagged conclusion")
            });
            assert_eq!(
                tag, m.relation,
                "slice carve: clause {i} conclusion tag != ClauseMeta relation"
            );
            by_tag.entry(&m.relation).or_default().push(i);
        }

        let mut included: BTreeSet<usize> = BTreeSet::new();
        let mut needed_tags: BTreeSet<&str> = BTreeSet::new();
        let mut work: Vec<usize> = Vec::new();

        // Seeds (explicit — not subject to `keep`).
        for seed in seeds {
            match seed {
                SliceSeed::Relation(r) => {
                    let idxs = by_tag.get(r.as_str()).ok_or_else(|| {
                        Error::ConnectiveRule(format!("slice seed: unknown relation tag `{r}`"))
                    })?;
                    needed_tags.insert(r.as_str());
                    for &i in idxs {
                        if included.insert(i) {
                            work.push(i);
                        }
                    }
                }
                SliceSeed::Rule(r, n) => {
                    let mut found = false;
                    for (i, m) in metas.iter().enumerate() {
                        if &m.relation == r && &m.name == n {
                            found = true;
                            if included.insert(i) {
                                work.push(i);
                            }
                        }
                    }
                    if !found {
                        return Err(Error::ConnectiveRule(format!(
                            "slice seed: no rule `{r}/{n}` in the total set"
                        )));
                    }
                }
            }
        }

        // The premise-tag dependency closure.
        while let Some(i) = work.pop() {
            for p in &clauses[i].prems {
                let LowerPrem::Judgement(j) = p else {
                    continue; // `Side` antecedents mention no relation tags.
                };
                let Some(t) = rel_tag(j) else { continue };
                if t.starts_with("opaque.") {
                    continue; // terminal by design: no clauses anywhere.
                }
                if needed_tags.contains(t.as_str()) {
                    continue;
                }
                // A tag is needed; adopt every kept clause concluding it. A
                // needed tag with NO clauses in the map is the zero-clause
                // builtin frontier — sound: judgements mentioning it stay
                // underivable (re-scans of such a tag are cheap map misses).
                if let Some((tag, idxs)) = by_tag.get_key_value(t.as_str()) {
                    needed_tags.insert(tag);
                    for &k in idxs {
                        if keep(&metas[k]) && included.insert(k) {
                            work.push(k);
                        }
                    }
                }
            }
        }

        let indices: Vec<usize> = included.into_iter().collect(); // sorted: total order
        let slice_clauses: Vec<Clause> = indices.iter().map(|&i| clauses[i].clone()).collect();
        let slice_metas: Vec<ClauseMeta> = indices.iter().map(|&i| metas[i].clone()).collect();
        Ok(SpecSlice {
            name: name.into(),
            indices,
            clauses: slice_clauses,
            metas: slice_metas,
            n_total: clauses.len(),
        })
    }

    /// The slice's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Slice index → total index (strictly increasing).
    pub fn indices(&self) -> &[usize] {
        &self.indices
    }

    /// The slice clauses, in total order.
    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// The matching per-clause metadata.
    pub fn metas(&self) -> &[ClauseMeta] {
        &self.metas
    }

    /// Clause count.
    pub fn n_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// The size of the total set this slice was carved from.
    pub fn n_total(&self) -> usize {
        self.n_total
    }

    /// The honest census: clause count, opaque premises within the slice, and
    /// the dischargeability split.
    pub fn report(&self) -> SliceReport {
        let mut opaque_tags: BTreeMap<String, usize> = BTreeMap::new();
        let mut n_clauses_opaque = 0;
        for c in &self.clauses {
            let mut has_opaque = false;
            for p in &c.prems {
                if let LowerPrem::Judgement(j) = p
                    && let Some(t) = rel_tag(j)
                    && let Some(reason) = t.strip_prefix("opaque.")
                {
                    *opaque_tags.entry(reason.to_owned()).or_default() += 1;
                    has_opaque = true;
                }
            }
            if has_opaque {
                n_clauses_opaque += 1;
            }
        }
        SliceReport {
            name: self.name.clone(),
            n_clauses: self.clauses.len(),
            n_total: self.n_total,
            opaque_tags,
            n_clauses_opaque,
            n_clauses_clean: self.clauses.len() - n_clauses_opaque,
        }
    }
}

// ============================================================================
// SliceEnv — RelationEnv-shaped ergonomics over a slice
// ============================================================================

/// A [`SpecSlice`] packaged as a derivation environment — the
/// [`RelationEnv`](crate::spectec::RelationEnv) ergonomics (derive by
/// `(relation, rule-name)`, `n_clauses`, census) over the slice's **own**
/// small rule set. Small slices do *not* need
/// [`with_total_stack`](super::total::with_total_stack): their `Closed_L` is
/// only as deep as the slice.
pub struct SliceEnv {
    slice: SpecSlice,
    rs: RuleSet<'static>,
    n_clauses: usize,
}

impl SliceEnv {
    /// Package a slice as a rule set (clause `i` = slice clause `i`).
    pub fn new(slice: SpecSlice) -> SliceEnv {
        let n_clauses = slice.n_clauses();
        let rs = rule_set_of(slice.clauses.clone());
        SliceEnv {
            slice,
            rs,
            n_clauses,
        }
    }

    /// The underlying slice (indices, clauses, metas).
    pub fn slice(&self) -> &SpecSlice {
        &self.slice
    }

    /// The slice's own rule set.
    pub fn rule_set(&self) -> &RuleSet<'static> {
        &self.rs
    }

    /// Clause count.
    pub fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    /// Per-clause metadata (relation / rule name / metavar order).
    pub fn rules(&self) -> &[ClauseMeta] {
        &self.slice.metas
    }

    /// The honest census (delegates to [`SpecSlice::report`]).
    pub fn report(&self) -> SliceReport {
        self.slice.report()
    }

    /// The slice-clause index of the first rule named `name` (in `relation`,
    /// if given), or `None`.
    pub fn rule_index(&self, relation: Option<&str>, name: &str) -> Option<usize> {
        self.slice
            .metas
            .iter()
            .position(|m| m.name == name && relation.is_none_or(|r| m.relation == r))
    }

    /// State `Derivable_slice ⌜R(e)⌝` for a relation name and SpecTec
    /// expression.
    pub fn derivable(&self, relation: &str, e: &SpecTecExp) -> Result<Term> {
        metalogic::derivable(&self.rs, &tag(relation, encode_exp(e)?)?)
    }

    /// **Apply slice clause `clause_idx`** with pre-encoded `args` (metavar
    /// order) and premise derivations, yielding a hypothesis-free
    /// `⊢ Derivable_slice ⌜concl[args]⌝`.
    pub fn derive(&self, clause_idx: usize, args: &[Term], premises: Vec<Premise>) -> Result<Thm> {
        metalogic::derive_mixed(&self.rs, clause_idx, self.n_clauses, args, premises)
    }

    /// [`SliceEnv::derive`] with the metavariable instantiations given as
    /// SpecTec expressions.
    pub fn derive_exprs(
        &self,
        clause_idx: usize,
        args: &[SpecTecExp],
        premises: Vec<Premise>,
    ) -> Result<Thm> {
        let encoded = args.iter().map(encode_exp).collect::<Result<Vec<_>>>()?;
        self.derive(clause_idx, &encoded, premises)
    }

    /// [`transport`] a theorem of this slice into the `full` rule set.
    pub fn transport(&self, full: &RuleSet, slice_thm: &Thm) -> Result<Thm> {
        transport(&self.slice, full, slice_thm)
    }
}

impl crate::spectec::Fragment for SliceEnv {
    fn judgement_kind(&self) -> &'static str {
        "Derivable_R"
    }

    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn derive(
        &self,
        clause_idx: usize,
        args: &[Term],
        premises: Vec<crate::spectec::FragPremise>,
    ) -> Result<Thm> {
        let prems = premises
            .into_iter()
            .map(|p| match p {
                crate::spectec::FragPremise::Derivation(t) => Premise::Derivation(t),
                crate::spectec::FragPremise::Side(t) => Premise::Side(t),
            })
            .collect();
        SliceEnv::derive(self, clause_idx, args, prems)
    }
}

// ============================================================================
// The transport theorem
// ============================================================================

/// **Transport a slice theorem into the full set**: from
/// `slice_thm : ⊢ Derivable_slice ⌜J⌝` derive `⊢ Derivable_full ⌜J⌝`, purely
/// with existing kernel moves (zero new rules):
///
/// ```text
///   assume Closed_full d                                   (the full layout)
///   for each slice clause i:  Closed_full d ⊢ clauseᵢ d    (nth-conjunct via the index map)
///   conjoin in slice order:   Closed_full d ⊢ Closed_slice d
///   open the slice theorem:   slice_thm[d] : ⊢ Closed_slice d ⟹ d ⌜J⌝
///   imp_elim:                 Closed_full d ⊢ d ⌜J⌝
///   imp_intro + all_intro:    ⊢ ∀d. Closed_full d ⟹ d ⌜J⌝  =  Derivable_full ⌜J⌝
/// ```
///
/// The kernel re-checks the composition: the conjunction rebuilt from the
/// full set's conjuncts must be *syntactically* the slice theorem's
/// antecedent, so transport succeeds **iff** the slice's clauses are literally
/// clauses of the full set at the mapped indices — nothing can be fabricated.
///
/// `full` must be the rule set of the exact total clause list the slice was
/// carved from (checked: clause counts and every extraction must match).
///
/// Full-set caveat: like every whole-spec operation, transporting into the
/// ~2000-clause combined set walks its `Closed_L` conjunction — run under
/// [`with_total_stack`](super::total::with_total_stack).
pub fn transport(slice: &SpecSlice, full: &RuleSet, slice_thm: &Thm) -> Result<Thm> {
    let n_full = full.n_clauses()?;
    if n_full != slice.n_total {
        return Err(Error::ConnectiveRule(format!(
            "transport: full set has {n_full} clauses but the slice was carved from {}",
            slice.n_total
        )));
    }
    derive_via_closed(full, |assumed, _d_apply| {
        // Single pass down the right-nested conjunction, harvesting the
        // conjuncts at the slice's (strictly increasing) total indices.
        let mut picked = Vec::with_capacity(slice.indices.len());
        let mut tail = assumed.clone(); // proves c_k ∧ (… ∧ c_{n-1})
        let mut k = 0usize;
        for &i in &slice.indices {
            while k < i {
                tail = tail.and_elim_r()?;
                k += 1;
            }
            picked.push(if i + 1 < n_full {
                tail.clone().and_elim_l()?
            } else {
                tail.clone()
            });
        }
        // `Closed_slice d` — right-nested in slice order (empty slice: `T`).
        let closed_slice = if picked.is_empty() {
            covalence_hol_eval::mk_bool(true).prove_true()?
        } else {
            conj_thms(picked)?
        };
        // Open the slice theorem at the shared bound-`d` variable and cut.
        slice_thm
            .clone()
            .all_elim(full.d_var())?
            .imp_elim(closed_slice)
    })
}

// ============================================================================
// Preset slices (approximate, feature-based — API exercise, not exactness)
// ============================================================================

/// **The lime slice** — the minimal *maximally-fireable* core: every seed
/// rule's premises are dischargeable today, and the carve closure stays
/// opaque-free (asserted in tests). Seeds:
///
/// - every premise-free `Step_pure` rule (genuine one-step executions:
///   `nop`, `unreachable`, `drop`, the `trap-*` family, …);
/// - `Steps/refl` (reflexive multi-step reduction);
/// - `Numtype_ok`, `Valtype_ok/num` and the premise-free `Instr_ok` typing
///   rules `nop`/`const`/`binop` (+ their `ev.sort.*` guard closure);
/// - the fired-demo closure `Step_pure/ref.is_null-false` (a real Else rule:
///   `ev.neq` pair + `ev.sort.ref` guard).
///
/// `Instr_ok/drop` is deliberately **not** seeded: its `Valtype_ok` premise
/// pulls the whole `Valtype_ok` relation, whose `ref` rule drags the
/// `Reftype_ok`/`Heaptype_ok`/`Typeuse_ok` chain (opaque premises) in — the
/// zero-opaque invariant is worth more to this preset than one more rule.
pub fn lime_slice(clauses: &[Clause], metas: &[ClauseMeta]) -> Result<SpecSlice> {
    let mut seeds = Vec::new();
    for (c, m) in clauses.iter().zip(metas) {
        if m.relation == "Step_pure" && c.prems.is_empty() {
            seeds.push(SliceSeed::rule("Step_pure", m.name.clone()));
        }
    }
    seeds.push(SliceSeed::rule("Steps", "refl"));
    seeds.push(SliceSeed::relation("Numtype_ok"));
    seeds.push(SliceSeed::rule("Valtype_ok", "num"));
    for r in ["nop", "const", "binop"] {
        seeds.push(SliceSeed::rule("Instr_ok", r));
    }
    seeds.push(SliceSeed::rule("Step_pure", "ref.is_null-false"));
    SpecSlice::carve(clauses, metas, "lime", &seeds)
}

/// **The exec slice** — lime's seeds plus the **multi-step execution
/// closure** (Wave G): `Steps` whole (refl + trans), the `Step/pure` lift,
/// the `Step/ctxt-instrs` frame rule, and the `binop`/`drop` step rules the
/// straight-line const-fold demo fires. The carve filter keeps the closure
/// from re-adopting the rest of the instruction relations (`Step`'s premises
/// mention `Step_read` etc. — only the seeded rules are kept; excluding
/// clauses is always sound). The `fn.binop_` dependency pulls the whole
/// integer-builtin leg, so this slice **executes arithmetic**: it is the
/// smallest set on which `z; [CONST I32 2, CONST I32 3, BINOP I32 ADD,
/// DROP] ↪* z; []` derives end-to-end.
pub fn exec_slice(clauses: &[Clause], metas: &[ClauseMeta]) -> Result<SpecSlice> {
    let mut seeds = Vec::new();
    for (c, m) in clauses.iter().zip(metas) {
        if m.relation == "Step_pure" && c.prems.is_empty() {
            seeds.push(SliceSeed::rule("Step_pure", m.name.clone()));
        }
    }
    seeds.push(SliceSeed::relation("Steps"));
    for name in ["pure", "ctxt-instrs"] {
        seeds.push(SliceSeed::rule("Step", name));
    }
    for name in ["binop-val", "binop-trap", "drop"] {
        seeds.push(SliceSeed::rule("Step_pure", name));
    }
    SpecSlice::carve_filtered(clauses, metas, "exec", &seeds, |m| {
        !INSTR_RELATIONS.contains(&m.relation.as_str())
    })
}

/// The relations whose rules are per-instruction (and therefore subject to
/// the wasm1/wasm2 instruction-name classification).
const INSTR_RELATIONS: [&str; 4] = ["Instr_ok", "Step_pure", "Step_read", "Step"];

/// ≈ **WASM 1.0 MVP** instruction keys, plus the administrative-rule keys the
/// 1.0 reduction semantics needs (`label`/`frame`/`trap` bookkeeping and the
/// `Step/pure|read|ctxt` embedding rules). A rule's key is its name up to the
/// first `-` (`select-true` → `select`, `load-num-oob` → `load`).
/// **Approximation** (documented in the module docs): classification is by
/// rule *name*; exception-handling (`*handler*`) rules are excluded even when
/// their key matches.
pub const WASM1_INSTRS: [&str; 30] = [
    // control
    "unreachable",
    "nop",
    "block",
    "loop",
    "if",
    "br",
    "br_if",
    "br_table",
    "return",
    "call",
    "call_indirect",
    // parametric
    "drop",
    "select",
    // variable
    "local.get",
    "local.set",
    "local.tee",
    "global.get",
    "global.set",
    // memory
    "load",
    "store",
    "memory.size",
    "memory.grow",
    // numeric
    "const",
    "unop",
    "binop",
    "testop",
    "relop",
    "cvtop",
    // administrative / embedding (label & frame bookkeeping, trap, Step glue)
    "label",
    "frame",
];

/// The remaining administrative keys (shared by wasm1 + wasm2): `trap`
/// propagation and the `Step` embedding/context rules.
const ADMIN_KEYS: [&str; 4] = ["trap", "pure", "read", "ctxt"];

/// ≈ **WASM 2.0** additions over [`WASM1_INSTRS`]: reference types, bulk
/// memory/table ops, multiple tables. **v128/SIMD is excluded** (our call —
/// documented: the `v*` rule families are large and orthogonal; a `wasm2simd`
/// preset can add them later), as is exception handling (3.0).
pub const WASM2_EXTRA_INSTRS: [&str; 16] = [
    "ref.null",
    "ref.func",
    "ref.is_null",
    "table.get",
    "table.set",
    "table.size",
    "table.grow",
    "table.fill",
    "table.copy",
    "table.init",
    "elem.drop",
    "memory.fill",
    "memory.copy",
    "memory.init",
    "data.drop",
    "select", // typed select — same key, already in 1.0's list
];

/// A rule name's instruction key: the segment before the first `-`.
fn instr_key(name: &str) -> &str {
    name.split('-').next().unwrap_or(name)
}

/// Whether a rule of an instruction relation belongs to the given key list
/// (exception-handling rules excluded by name).
fn instr_rule_in(m: &ClauseMeta, keys: &[&str]) -> bool {
    keys.contains(&instr_key(&m.name)) && !m.name.contains("handler")
}

/// Carve a feature slice: instruction-relation rules filtered to `keys` (plus
/// the shared admin keys), the sequencing/expression/multi-step relations
/// whole, and the premise closure — with the filter applied to closure pulls
/// too (so a premise mentioning `Instr_ok` pulls only classified rules back).
fn feature_slice(
    clauses: &[Clause],
    metas: &[ClauseMeta],
    name: &str,
    keys: &[&str],
) -> Result<SpecSlice> {
    let all_keys: Vec<&str> = keys.iter().chain(ADMIN_KEYS.iter()).copied().collect();
    let mut seeds = Vec::new();
    for m in metas {
        if INSTR_RELATIONS.contains(&m.relation.as_str()) && instr_rule_in(m, &all_keys) {
            seeds.push(SliceSeed::rule(m.relation.clone(), m.name.clone()));
        }
    }
    for rel in ["Instrs_ok", "Expr_ok", "Steps"] {
        seeds.push(SliceSeed::relation(rel));
    }
    seeds.sort();
    seeds.dedup();
    SpecSlice::carve_filtered(clauses, metas, name, &seeds, |m| {
        !INSTR_RELATIONS.contains(&m.relation.as_str()) || instr_rule_in(m, &all_keys)
    })
}

/// ≈ **WASM 1.0 MVP** ([`WASM1_INSTRS`] — see the approximation caveats
/// there and in the module docs).
pub fn wasm1_slice(clauses: &[Clause], metas: &[ClauseMeta]) -> Result<SpecSlice> {
    feature_slice(clauses, metas, "wasm1", &WASM1_INSTRS)
}

/// ≈ **WASM 2.0** ([`WASM1_INSTRS`] + [`WASM2_EXTRA_INSTRS`]; v128 and
/// exception handling excluded — see the docs on the lists).
pub fn wasm2_slice(clauses: &[Clause], metas: &[ClauseMeta]) -> Result<SpecSlice> {
    let keys: Vec<&str> = WASM1_INSTRS
        .iter()
        .chain(WASM2_EXTRA_INSTRS.iter())
        .copied()
        .collect();
    feature_slice(clauses, metas, "wasm2", &keys)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::lower::total::{TotalReport, total_spec_clauses, with_total_stack};
    use crate::wasm::spec::wasm_spec;
    use covalence_spectec::ast::MixOp;

    fn leaf(name: &str) -> SpecTecExp {
        SpecTecExp::Case {
            op: MixOp::new(vec![name.to_string()]),
            e1: Box::new(SpecTecExp::Tup { es: vec![] }),
        }
    }

    fn total() -> (Vec<Clause>, TotalReport) {
        total_spec_clauses(&wasm_spec()).unwrap()
    }

    /// Closure-closedness: every non-opaque premise tag of a slice clause
    /// either has at least one clause in the slice, or has zero clauses in
    /// the total set (the zero-clause builtin frontier). Only meaningful for
    /// **unfiltered** carves (a `keep` filter deliberately breaks it for the
    /// filtered relations).
    fn assert_closed(slice: &SpecSlice, all_clauses: &[Clause]) {
        let mut total_tags: BTreeMap<String, usize> = BTreeMap::new();
        for c in all_clauses {
            *total_tags.entry(rel_tag(&c.concl).unwrap()).or_default() += 1;
        }
        let slice_tags: BTreeSet<&str> =
            slice.metas().iter().map(|m| m.relation.as_str()).collect();
        for (c, m) in slice.clauses().iter().zip(slice.metas()) {
            for p in &c.prems {
                let LowerPrem::Judgement(j) = p else { continue };
                let Some(t) = rel_tag(j) else { continue };
                if t.starts_with("opaque.") {
                    continue;
                }
                assert!(
                    slice_tags.contains(t.as_str())
                        || total_tags.get(&t).copied().unwrap_or(0) == 0,
                    "slice `{}` not closed: {}/{} premise tag `{t}` has clauses \
                     in the total set but none in the slice",
                    slice.name(),
                    m.relation,
                    m.name,
                );
            }
        }
    }

    /// The index map is exactly the total order restricted, and parallel to
    /// the `ClauseMeta`s (on top of the hard asserts inside `carve` itself).
    #[test]
    fn slice_index_map_integrity() {
        with_total_stack(|| {
            let (clauses, report) = total();
            let lime = lime_slice(&clauses, &report.metas).unwrap();
            assert_eq!(lime.n_total(), clauses.len());
            assert_eq!(lime.n_clauses(), lime.indices().len());
            assert_eq!(lime.n_clauses(), lime.metas().len());
            let mut prev: Option<usize> = None;
            for (i, &ti) in lime.indices().iter().enumerate() {
                assert!(prev.is_none_or(|p| p < ti), "indices strictly increasing");
                prev = Some(ti);
                // The slice clause is the total clause (same Arc'd terms).
                assert_eq!(lime.clauses()[i].concl, clauses[ti].concl);
                assert_eq!(lime.clauses()[i].metavars, clauses[ti].metavars);
                assert_eq!(lime.clauses()[i].prems.len(), clauses[ti].prems.len());
                // And the meta is the total meta.
                assert_eq!(lime.metas()[i].relation, report.metas[ti].relation);
                assert_eq!(lime.metas()[i].name, report.metas[ti].name);
                assert_eq!(lime.metas()[i].metavars, report.metas[ti].metavars);
            }
        })
    }

    /// The dependency closure follows `fn.*` graphs, `star.*` aux and `ev.*`
    /// families out of a seed rule's premises.
    #[test]
    fn closure_follows_fn_star_ev_deps() {
        with_total_stack(|| {
            let (clauses, report) = total();

            // Nondefaultable's `If` condition calls `$default_`: the closure
            // must pull the `fn.default_` graph clauses and their deps.
            let nd = SpecSlice::carve(
                &clauses,
                &report.metas,
                "nd",
                &[SliceSeed::rule("Nondefaultable", "")],
            )
            .unwrap();
            let tags: BTreeSet<&str> = nd.metas().iter().map(|m| m.relation.as_str()).collect();
            assert!(tags.contains("Nondefaultable"), "{tags:?}");
            assert!(tags.contains("fn.default_"), "fn graph followed: {tags:?}");
            assert_closed(&nd, &clauses);

            // Resulttype_ok's premise is an Iter over Valtype_ok: the closure
            // must pull its star aux clauses AND the star's inner relation
            // (Valtype_ok), which in turn pulls Numtype_ok + sort guards.
            let rt = SpecSlice::carve(
                &clauses,
                &report.metas,
                "rt",
                &[SliceSeed::rule("Resulttype_ok", "")],
            )
            .unwrap();
            let tags: BTreeSet<&str> = rt.metas().iter().map(|m| m.relation.as_str()).collect();
            assert!(
                tags.contains("star.Resulttype_ok..0"),
                "star aux followed: {tags:?}"
            );
            assert!(
                tags.contains("Valtype_ok") && tags.contains("Numtype_ok"),
                "star inner relation followed: {tags:?}"
            );
            assert!(
                tags.iter().any(|t| t.starts_with("ev.sort.")),
                "ev.* guard families followed: {tags:?}"
            );
            assert_closed(&rt, &clauses);
        })
    }

    /// **Lime**: zero opaque premises, and it fires on a DEFAULT-size test
    /// thread — a real reduction (`[NOP] ↪ []`) and a real composed typing
    /// derivation (`Numtype_ok ∘ ev.sort.numtype ⟹ Valtype_ok/num`), both
    /// hypothesis-free, without `with_total_stack`.
    #[test]
    fn lime_zero_opaque_and_fires_on_default_stack() {
        // Build the total set + carve on the big-stack thread; the slice
        // itself (plain clause data) comes back to this default-size thread.
        let lime = with_total_stack(|| {
            let (clauses, report) = total();
            let lime = lime_slice(&clauses, &report.metas).unwrap();
            assert_closed(&lime, &clauses);
            lime
        });

        let r = lime.report();
        println!(
            "lime: {} clauses (of {}), opaque {}, clean {}",
            r.n_clauses,
            r.n_total,
            r.opaque_total(),
            r.n_clauses_clean
        );
        // THE lime invariant: the maximally-fireable core has NO opaque
        // premises at all.
        assert_eq!(
            r.opaque_total(),
            0,
            "lime opaque census: {:?}",
            r.opaque_tags
        );
        assert_eq!(r.n_clauses_clean, r.n_clauses);
        // Measured after the exact Dec source-sort complements: 407.
        assert!((400..=450).contains(&r.n_clauses), "lime = {}", r.n_clauses);

        // -- Everything below runs on the DEFAULT test-thread stack. --
        let env = SliceEnv::new(lime);

        // (1) Real reduction: [NOP] ↪ [].
        let nop = env.rule_index(Some("Step_pure"), "nop").expect("nop");
        let thm = env.derive(nop, &[], vec![]).unwrap();
        assert!(thm.hyps().is_empty());
        let judgement = SpecTecExp::Tup {
            es: vec![
                SpecTecExp::List {
                    es: vec![leaf("NOP")],
                },
                SpecTecExp::List { es: vec![] },
            ],
        };
        assert_eq!(
            thm.concl(),
            &env.derivable("Step_pure", &judgement).unwrap(),
            "nop reduces [NOP] to [] in the slice"
        );

        // (2) Composed typing: Numtype_ok(C, I32) + ev.sort.numtype(I32)
        //     ⟹ Valtype_ok/num(C, I32).
        let ctx = encode_exp(&leaf("C")).unwrap();
        let i32e = encode_exp(&leaf("I32")).unwrap();
        let numtype_ok = env.rule_index(Some("Numtype_ok"), "").unwrap();
        let base = env
            .derive(numtype_ok, &[ctx.clone(), i32e.clone()], vec![])
            .unwrap();
        let sort_num = env.rule_index(Some("ev.sort.numtype"), "").unwrap();
        let d_sort = env.derive(sort_num, &[], vec![]).unwrap();
        let valtype_num = env.rule_index(Some("Valtype_ok"), "num").unwrap();
        let vt = env
            .derive(
                valtype_num,
                &[ctx, i32e],
                vec![Premise::Derivation(base), Premise::Derivation(d_sort)],
            )
            .unwrap();
        assert!(vt.hyps().is_empty(), "composed typing is hypothesis-free");
    }

    /// wasm1/wasm2 presets: they build, the censuses print, the floors hold,
    /// and the feature classification separates them (a 2.0 bulk-table rule is
    /// in wasm2 but not wasm1; v128 and exception handlers are in neither).
    #[test]
    fn wasm1_wasm2_census_and_floors() {
        with_total_stack(|| {
            let (clauses, report) = total();
            let w1 = wasm1_slice(&clauses, &report.metas).unwrap();
            let w2 = wasm2_slice(&clauses, &report.metas).unwrap();
            for s in [&w1, &w2] {
                let r = s.report();
                println!(
                    "{}: {} clauses (of {}), opaque {} in {} clauses, clean {}; tags: {:?}",
                    r.name,
                    r.n_clauses,
                    r.n_total,
                    r.opaque_total(),
                    r.n_clauses_opaque,
                    r.n_clauses_clean,
                    r.opaque_tags
                );
            }
            // Floors around measured (2026-07-19, post exact integer
            // conversion families and ordered-Dec closure: wasm1 1174
            // clauses / 0 opaque; wasm2 1272 / 0).
            let (r1, r2) = (w1.report(), w2.report());
            assert!(
                (1170..=1200).contains(&r1.n_clauses),
                "wasm1 = {}",
                r1.n_clauses
            );
            assert!(
                r1.n_clauses_clean >= 1170,
                "wasm1 clean = {}",
                r1.n_clauses_clean
            );
            assert!(
                r1.opaque_total() == 0,
                "wasm1 opaque = {}",
                r1.opaque_total()
            );
            assert!(r2.n_clauses > r1.n_clauses, "wasm2 strictly bigger");
            assert!(
                (1270..=1300).contains(&r2.n_clauses),
                "wasm2 = {}",
                r2.n_clauses
            );
            assert!(
                r2.opaque_total() == 0,
                "wasm2 opaque = {}",
                r2.opaque_total()
            );
            assert!(r2.n_clauses < clauses.len() / 2, "wasm2 well under total");

            let has = |s: &SpecSlice, rel: &str, name: &str| {
                s.metas()
                    .iter()
                    .any(|m| m.relation == rel && m.name == name)
            };
            // 1.0 core in both.
            for s in [&w1, &w2] {
                assert!(has(s, "Step_pure", "nop"));
                assert!(has(s, "Instr_ok", "binop"));
                assert!(has(s, "Step_read", "block"));
            }
            // Bulk table ops (2.0) split the presets.
            assert!(!has(&w1, "Step_read", "table.fill-zero"));
            assert!(has(&w2, "Step_read", "table.fill-zero"));
            assert!(!has(&w1, "Instr_ok", "ref.null"));
            assert!(has(&w2, "Instr_ok", "ref.null"));
            // v128 and exception handling are in neither.
            for s in [&w1, &w2] {
                assert!(!has(s, "Instr_ok", "vconst"), "v128 excluded");
                assert!(!has(s, "Step_pure", "vsplat"), "v128 excluded");
                assert!(
                    !s.metas().iter().any(|m| m.name.contains("handler")),
                    "exception handling excluded"
                );
            }
        })
    }

    /// **Transport end-to-end**: derive in lime, transport into the full
    /// combined set, and the result is *literally* the full-set `Derivable`
    /// statement — plus the timing comparison showing the slice win.
    #[test]
    fn transport_lime_theorem_into_full_set() {
        with_total_stack(|| {
            use std::time::Instant;
            let (clauses, report) = total();
            let lime = lime_slice(&clauses, &report.metas).unwrap();
            let env = SliceEnv::new(lime);
            let full = rule_set_of(clauses.clone());
            let n_full = full.n_clauses().unwrap();
            assert_eq!(n_full, clauses.len());

            // Slice derivation (cold: pays the small slice layout).
            let nop = env.rule_index(Some("Step_pure"), "nop").expect("nop");
            let t0 = Instant::now();
            let small = env.derive(nop, &[], vec![]).unwrap();
            let slice_cold = t0.elapsed();
            assert!(small.hyps().is_empty());
            // Its conclusion is the SLICE's Derivable statement...
            let nop_body = &env.slice().clauses()[nop].concl; // ground rule: no metavars
            assert!(env.slice().clauses()[nop].metavars.is_empty());
            assert_eq!(
                small.concl(),
                &metalogic::derivable(env.rule_set(), nop_body).unwrap()
            );

            // The same derivation done natively on the full set — timed
            // BEFORE any other full-set operation, so it genuinely pays the
            // cold O(set) layout the slice avoids (the slice win).
            let full_idx = report
                .metas
                .iter()
                .position(|m| m.relation == "Step_pure" && m.name == "nop")
                .unwrap();
            let t2 = Instant::now();
            let native = metalogic::derive_mixed(&full, full_idx, n_full, &[], vec![]).unwrap();
            let full_cold = t2.elapsed();

            // ...and transport rewrites the slice theorem into the FULL
            // set's, kernel-derived.
            let t1 = Instant::now();
            let big = env.transport(&full, &small).unwrap();
            let transport_in = t1.elapsed();
            assert!(
                big.hyps().is_empty(),
                "transported theorem is hypothesis-free"
            );
            assert_eq!(
                big.concl(),
                &metalogic::derivable(&full, nop_body).unwrap(),
                "transported conclusion is literally the full-set Derivable statement"
            );
            assert_eq!(native.concl(), big.concl(), "transport = native derivation");
            println!(
                "nop: slice derive (cold) {slice_cold:?} vs full derive (cold) {full_cold:?}; \
                 transport {transport_in:?}"
            );
            assert!(
                slice_cold <= full_cold,
                "slice cold derive ({slice_cold:?}) should beat the full set's ({full_cold:?})"
            );

            // A composed derivation (with premises) transports identically.
            let ctx = encode_exp(&leaf("C")).unwrap();
            let i32e = encode_exp(&leaf("I32")).unwrap();
            let base = env
                .derive(
                    env.rule_index(Some("Numtype_ok"), "").unwrap(),
                    &[ctx.clone(), i32e.clone()],
                    vec![],
                )
                .unwrap();
            let d_sort = env
                .derive(
                    env.rule_index(Some("ev.sort.numtype"), "").unwrap(),
                    &[],
                    vec![],
                )
                .unwrap();
            let vt = env
                .derive(
                    env.rule_index(Some("Valtype_ok"), "num").unwrap(),
                    &[ctx, i32e],
                    vec![Premise::Derivation(base), Premise::Derivation(d_sort)],
                )
                .unwrap();
            let vt_full = env.transport(&full, &vt).unwrap();
            assert!(vt_full.hyps().is_empty());

            // Mismatched carrier set is refused (count check).
            let sub_rs = rule_set_of(env.slice().clauses().to_vec());
            assert!(env.transport(&sub_rs, &small).is_err());
        })
    }
}
