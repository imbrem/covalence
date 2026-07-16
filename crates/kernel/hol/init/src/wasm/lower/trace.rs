//! **Execution traces** — chain single-`Step` theorems into multi-step
//! `⊢ Derivable ⌜Steps (z; prog) ↪* (z'; prog')⌝` runs through the spec's own
//! reflexive-transitive closure (`Steps/refl` + `Steps/trans` are ordinary
//! clauses of the combined set — nothing new is trusted; the driver only
//! *proposes* instantiations and the kernel re-checks every application, the
//! `construct, don't trust` shape of `k::relation`'s `KReduces` driver).
//!
//! ## What a straight-line trace needs (measured on the lowered set)
//!
//! - **`Steps/refl`** (premise-free) and **`Steps/trans`** (premises = one
//!   `Step` + one `Steps`) both lower clean — the chain skeleton.
//! - **`Step/pure`** / **`Step/read`** — the state-threading lifts of
//!   `Step_pure` / `Step_read` — lower clean (one judgement premise each;
//!   their identity iterations collapse to plain metavariables).
//! - **`Step/ctxt-instrs`** — the `val*`-prefix / `instr_1*`-suffix frame
//!   rule every multi-instruction program needs — lowers fireable since
//!   Wave G: its conclusion `Cat` spines flatten through `ev.cat` premises
//!   (`Mode::Concl`), so derivable instances carry genuine flat-list
//!   encodings, and its `val* =/= [] \/ instr_1* =/= []` guard lowers to the
//!   exact-at-real-points `ev.nonempty2` premise. [`TraceEnv::frame`] wraps
//!   the whole obligation: it evaluates the four concatenations, the
//!   nonempty witness and the `val*` sort guard on ground configurations.
//! - `Step/ctxt-label` / `ctxt-frame` / `ctxt-handler` lower clean too
//!   (single-instruction conclusions, no `Cat`) — traces through nested
//!   labels/frames need no extra machinery beyond premise derivations.
//!
//! The driver is deliberately an **explicit chain API**: the caller derives
//! each single step (through whichever rule applies) and [`TraceEnv::chain`]
//! folds them through `Steps/trans` onto a final `Steps/refl`. Automatic
//! per-step rule *search* over ground configurations (the
//! `k::relation::prove_reduces` matcher pattern) is a follow-on — see
//! `wasm/SKELETONS.md`.

use std::collections::BTreeMap;

use covalence_core::subst::subst_free;
use covalence_core::{Error, Result, Term, Var};
use covalence_hol_eval::EvalThm as Thm;

use super::super::encode::{app, con, metavar_name, phi, tag};
use super::evalrel::ev_graph;
use super::total::ClauseMeta;
use super::{Clause, LowerPrem};
use crate::metalogic::{self, Premise, RuleSet};

fn trace_err(msg: impl Into<String>) -> Error {
    Error::ConnectiveRule(format!("wasm trace: {}", msg.into()))
}

/// A ground configuration `(z; instr*)` in encoded form: the state term and
/// the (flat snoc-spine) instruction list term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    pub z: Term,
    pub instrs: Term,
}

impl Config {
    pub fn new(z: Term, instrs: Term) -> Self {
        Config { z, instrs }
    }

    /// The encoded configuration `case.%;%(tup(z, instr*))` — exactly the
    /// shape `Steps`/`Step` conclusions carry.
    pub fn term(&self) -> Result<Term> {
        app(
            con("case.%;%"),
            app(app(con("tup"), self.z.clone())?, self.instrs.clone())?,
        )
    }
}

/// One certified step of a trace: `⊢ Derivable ⌜Step (from, to)⌝` plus its
/// endpoint configurations (the driver's chaining currency; the kernel
/// re-checks the theorem against the endpoints at every `Steps/trans`).
#[derive(Debug, Clone)]
pub struct TraceStep {
    pub from: Config,
    pub to: Config,
    pub thm: Thm,
}

/// The trace driver over one rule set (the full combined set or any slice
/// containing the `Steps`/`Step` closure): resolved clause indices for the
/// chain skeleton plus ground-evaluation helpers (`ev.cat`, `ev.nonempty2`,
/// `ev.sort.*`) for the frame rule.
pub struct TraceEnv<'a> {
    rs: &'a RuleSet<'static>,
    clauses: &'a [Clause],
    metas: &'a [ClauseMeta],
    n: usize,
    by_rel: BTreeMap<&'a str, Vec<usize>>,
    refl: usize,
    trans: usize,
    pure_: Option<usize>,
    read: Option<usize>,
    ctxt: Option<usize>,
}

impl<'a> TraceEnv<'a> {
    /// Build over parallel `(rule_set, clauses, metas)` — the outputs of
    /// [`total_spec_clauses`](super::total::total_spec_clauses) +
    /// [`rule_set_of`](super::rule_set_of), or a
    /// [`SliceEnv`](super::slice::SliceEnv)'s parts (see
    /// [`TraceEnv::for_slice`]). Requires `Steps/refl` and `Steps/trans` in
    /// the set; the `Step` lifts are optional (their helpers error if absent).
    pub fn new(
        rs: &'a RuleSet<'static>,
        clauses: &'a [Clause],
        metas: &'a [ClauseMeta],
    ) -> Result<Self> {
        assert_eq!(clauses.len(), metas.len(), "clauses/metas must be parallel");
        let n = clauses.len();
        let mut by_rel: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
        for (i, m) in metas.iter().enumerate() {
            by_rel.entry(m.relation.as_str()).or_default().push(i);
        }
        let find = |rel: &str, name: &str| {
            metas
                .iter()
                .position(|m| m.relation == rel && m.name == name)
        };
        let refl = find("Steps", "refl")
            .ok_or_else(|| trace_err("no Steps/refl clause in this rule set"))?;
        let trans = find("Steps", "trans")
            .ok_or_else(|| trace_err("no Steps/trans clause in this rule set"))?;
        Ok(TraceEnv {
            rs,
            clauses,
            metas,
            n,
            by_rel,
            refl,
            trans,
            pure_: find("Step", "pure"),
            read: find("Step", "read"),
            ctxt: find("Step", "ctxt-instrs"),
        })
    }

    /// [`TraceEnv::new`] over a slice environment's own rule set.
    pub fn for_slice(env: &'a super::slice::SliceEnv) -> Result<Self> {
        TraceEnv::new(env.rule_set(), env.slice().clauses(), env.slice().metas())
    }

    /// Apply clause `idx` at `args` (metavar order) with `prems`.
    pub fn derive(&self, idx: usize, args: &[Term], prems: Vec<Premise>) -> Result<Thm> {
        metalogic::derive_mixed(self.rs, idx, self.n, args, prems)
    }

    /// The first clause of `rel` named `name`.
    pub fn rule_index(&self, rel: &str, name: &str) -> Option<usize> {
        self.metas
            .iter()
            .position(|m| m.relation == rel && m.name == name)
    }

    /// The clause at `idx` (for `Side` instantiation via [`side_at`]).
    pub fn clause(&self, idx: usize) -> &Clause {
        &self.clauses[idx]
    }

    /// State `Derivable ⌜J⌝` for this rule set.
    pub fn derivable(&self, body: &Term) -> Result<Term> {
        metalogic::derivable(self.rs, body)
    }

    /// The clause of `rel` whose conclusion instantiates to `expected` at
    /// `args` (the ground-clause lookup the demos use).
    pub fn find_at(&self, rel: &str, args: &[Term], expected: &Term) -> Result<usize> {
        self.by_rel
            .get(rel)
            .into_iter()
            .flatten()
            .copied()
            .find(|&i| {
                self.clauses[i].metavars.len() == args.len()
                    && instantiate(&self.clauses[i], args) == *expected
            })
            .ok_or_else(|| {
                trace_err(format!(
                    "no `{rel}` clause concluding the expected instance"
                ))
            })
    }

    /// The `k`-th clause of relation `rel` (emission order).
    pub fn nth_of(&self, rel: &str, k: usize) -> Result<usize> {
        self.by_rel
            .get(rel)
            .and_then(|v| v.get(k))
            .copied()
            .ok_or_else(|| trace_err(format!("no clause {k} of `{rel}`")))
    }

    /// The `Steps` judgement body `⌜Steps (from, to)⌝` (for stating the
    /// expected trace conclusion via [`metalogic::derivable`]).
    pub fn steps_judgement(&self, from: &Config, to: &Config) -> Result<Term> {
        tag("Steps", app(app(con("tup"), from.term()?)?, to.term()?)?)
    }

    /// `⊢ Derivable ⌜Steps (cfg, cfg)⌝` — the trace terminator.
    pub fn refl(&self, cfg: &Config) -> Result<Thm> {
        self.derive(self.refl, &[cfg.z.clone(), cfg.instrs.clone()], vec![])
    }

    /// Lift a `⊢ Derivable ⌜Step_pure (instr*, instr'*)⌝` theorem into the
    /// state-threading `Step` at state `z` (`Step/pure` — clean, no framing).
    pub fn lift_pure(
        &self,
        z: &Term,
        instrs: &Term,
        instrs2: &Term,
        thm: Thm,
    ) -> Result<TraceStep> {
        let idx = self
            .pure_
            .ok_or_else(|| trace_err("no Step/pure clause in this rule set"))?;
        let args = [z.clone(), instrs.clone(), instrs2.clone()];
        let step = self.derive(idx, &args, vec![Premise::Derivation(thm)])?;
        Ok(TraceStep {
            from: Config::new(z.clone(), instrs.clone()),
            to: Config::new(z.clone(), instrs2.clone()),
            thm: step,
        })
    }

    /// Lift a `⊢ Derivable ⌜Step_read ((z; instr*), instr'*)⌝` theorem into
    /// `Step` (`Step/read` — reads the state, does not change it).
    pub fn lift_read(
        &self,
        z: &Term,
        instrs: &Term,
        instrs2: &Term,
        thm: Thm,
    ) -> Result<TraceStep> {
        let idx = self
            .read
            .ok_or_else(|| trace_err("no Step/read clause in this rule set"))?;
        let args = [z.clone(), instrs.clone(), instrs2.clone()];
        let step = self.derive(idx, &args, vec![Premise::Derivation(thm)])?;
        Ok(TraceStep {
            from: Config::new(z.clone(), instrs.clone()),
            to: Config::new(z.clone(), instrs2.clone()),
            thm: step,
        })
    }

    // =======================================================================
    // Ground evaluation helpers (the frame rule's obligations)
    // =======================================================================

    /// `⊢ Derivable ⌜ev.cat (xs, ys, xs ++ ys)⌝` on ground snoc spines, with
    /// the concatenated term (recursion on `ys`; `[] ++ ys = ys` holds
    /// *syntactically* — both spines share the `list` base).
    pub fn prove_cat(&self, xs: &Term, ys: &Term) -> Result<(Term, Thm)> {
        let base = self.cat_clause(1)?; // cat(xs, [], xs) — 1 metavar
        let step = self.cat_clause(4)?; // cat(xs, ys·y, r·y) — 4 metavars
        if is_nil(ys) {
            let thm = self.derive(base, &[xs.clone()], vec![])?;
            return Ok((xs.clone(), thm));
        }
        let (ys1, y) =
            un_app(ys).ok_or_else(|| trace_err("prove_cat: `ys` is not a ground snoc spine"))?;
        let (r1, inner) = self.prove_cat(xs, ys1)?;
        let r = app(r1.clone(), y.clone())?;
        let args = [xs.clone(), ys1.clone(), y.clone(), r1];
        let thm = self.derive(step, &args, vec![Premise::Derivation(inner)])?;
        Ok((r, thm))
    }

    fn cat_clause(&self, n_metavars: usize) -> Result<usize> {
        self.by_rel
            .get("ev.cat")
            .into_iter()
            .flatten()
            .copied()
            .find(|&i| self.clauses[i].metavars.len() == n_metavars)
            .ok_or_else(|| trace_err("no ev.cat clauses in this rule set (carve them in)"))
    }

    /// `⊢ Derivable ⌜ev.nonempty2 (a, b)⌝` — a or b is a ground snoc node.
    pub fn prove_nonempty2(&self, a: &Term, b: &Term) -> Result<Thm> {
        let idxs = self
            .by_rel
            .get("ev.nonempty2")
            .ok_or_else(|| trace_err("no ev.nonempty2 clauses in this rule set"))?;
        if let Some((l, x)) = un_app(a) {
            // Left clause: nonempty2(l·x, y).
            let idx = *idxs
                .first()
                .ok_or_else(|| trace_err("ev.nonempty2 empty"))?;
            return self.derive(idx, &[l.clone(), x.clone(), b.clone()], vec![]);
        }
        if let Some((l, y)) = un_app(b) {
            let idx = *idxs
                .get(1)
                .ok_or_else(|| trace_err("ev.nonempty2 right clause missing"))?;
            return self.derive(idx, &[a.clone(), l.clone(), y.clone()], vec![]);
        }
        Err(trace_err(
            "prove_nonempty2: both sides are empty/non-spines",
        ))
    }

    /// `⊢ Derivable ⌜ev.sort.val (v)⌝` for a ground value — searches the
    /// guard family's head clauses (ground nullary or one-payload-metavar).
    pub fn prove_sort_val(&self, v: &Term) -> Result<Thm> {
        self.prove_sort("ev.sort.val", v)
    }

    /// Generic ground sort-guard discharge for an `ev.sort.<ty>` family.
    pub fn prove_sort(&self, rel: &str, v: &Term) -> Result<Thm> {
        let target = ev_graph(rel.strip_prefix("ev.").unwrap_or(rel), &[], v)?;
        let idxs = self
            .by_rel
            .get(rel)
            .ok_or_else(|| trace_err(format!("no `{rel}` clauses in this rule set")))?;
        for &i in idxs {
            let c = &self.clauses[i];
            match c.metavars.len() {
                0 if c.concl == target => return self.derive(i, &[], vec![]),
                1 => {
                    if let Some((_head, payload)) = un_app(v)
                        && instantiate(c, std::slice::from_ref(payload)) == target
                    {
                        return self.derive(i, &[payload.clone()], vec![]);
                    }
                }
                _ => {}
            }
        }
        Err(trace_err(format!("no `{rel}` clause matches this value")))
    }

    /// `⊢ Derivable ⌜ev.sort.list.val (vs)⌝` on a ground value list — nil
    /// clause + per-element [`TraceEnv::prove_sort_val`] through the snoc
    /// clause.
    pub fn prove_sort_list_val(&self, vs: &Term) -> Result<Thm> {
        let idxs = self
            .by_rel
            .get("ev.sort.list.val")
            .ok_or_else(|| trace_err("no ev.sort.list.val clauses in this rule set"))?;
        let nil = idxs
            .iter()
            .copied()
            .find(|&i| self.clauses[i].metavars.is_empty())
            .ok_or_else(|| trace_err("ev.sort.list.val nil clause missing"))?;
        let snoc = idxs
            .iter()
            .copied()
            .find(|&i| self.clauses[i].metavars.len() == 2)
            .ok_or_else(|| trace_err("ev.sort.list.val snoc clause missing"))?;
        if is_nil(vs) {
            return self.derive(nil, &[], vec![]);
        }
        let (l, v) =
            un_app(vs).ok_or_else(|| trace_err("prove_sort_list_val: not a ground spine"))?;
        let d_list = self.prove_sort_list_val(l)?;
        let d_elem = self.prove_sort_val(v)?;
        self.derive(
            snoc,
            &[l.clone(), v.clone()],
            vec![Premise::Derivation(d_list), Premise::Derivation(d_elem)],
        )
    }

    // =======================================================================
    // The frame rule and the chain
    // =======================================================================

    /// **Frame a step** into a larger instruction sequence
    /// (`Step/ctxt-instrs`): from `⊢ Step ((z; instr*), (z'; instr'*))`
    /// derive `⊢ Step ((z; val* ++ instr* ++ suffix), (z'; val* ++ instr'* ++
    /// suffix))` on ground `val*`/`suffix` lists (at least one non-empty —
    /// the spec's own guard). All obligations — the four `ev.cat`
    /// evaluations, the `ev.nonempty2` witness and the `val*` sort guard —
    /// are derived here; the returned endpoints carry the genuine flat-list
    /// encodings.
    pub fn frame(&self, vals: &Term, suffix: &Term, step: &TraceStep) -> Result<TraceStep> {
        let idx = self
            .ctxt
            .ok_or_else(|| trace_err("no Step/ctxt-instrs clause in this rule set"))?;
        let (is, is2) = (&step.from.instrs, &step.to.instrs);
        let (r1, d1) = self.prove_cat(is, suffix)?;
        let (r2, d2) = self.prove_cat(vals, &r1)?;
        let (r3, d3) = self.prove_cat(is2, suffix)?;
        let (r4, d4) = self.prove_cat(vals, &r3)?;
        let d_ne = self.prove_nonempty2(vals, suffix)?;
        let d_sort = self.prove_sort_list_val(vals)?;
        let args = [
            step.from.z.clone(),
            vals.clone(),
            is.clone(),
            suffix.clone(),
            step.to.z.clone(),
            is2.clone(),
            r1,
            r2.clone(),
            r3,
            r4.clone(),
        ];
        let thm = self.derive(
            idx,
            &args,
            vec![
                Premise::Derivation(d1),
                Premise::Derivation(d2),
                Premise::Derivation(d3),
                Premise::Derivation(d4),
                Premise::Derivation(step.thm.clone()),
                Premise::Derivation(d_ne),
                Premise::Derivation(d_sort),
            ],
        )?;
        Ok(TraceStep {
            from: Config::new(step.from.z.clone(), r2),
            to: Config::new(step.to.z.clone(), r4),
            thm,
        })
    }

    /// **Chain steps into a trace**: fold certified `Step`s through
    /// `Steps/trans` onto a final `Steps/refl`, yielding
    /// `⊢ Derivable ⌜Steps (steps[0].from, steps[last].to)⌝`
    /// (`steps` must be non-empty and adjacent: each step's `to` is the next
    /// step's `from`; a mismatch fails here — and would fail in the kernel).
    pub fn chain(&self, steps: &[TraceStep]) -> Result<Thm> {
        let last = steps.last().ok_or_else(|| trace_err("empty trace"))?;
        for (i, w) in steps.windows(2).enumerate() {
            if w[0].to != w[1].from {
                return Err(trace_err(format!(
                    "non-adjacent steps: step {i}'s target is not step {}'s source",
                    i + 1
                )));
            }
        }
        let final_cfg = &last.to;
        let mut acc = self.refl(final_cfg)?;
        // Fold back to front: trans(z, instr*, z'', instr''*, z', instr'*)
        // with premises [Step (from -> to), Steps (to -> final)].
        for step in steps.iter().rev() {
            let args = [
                step.from.z.clone(),
                step.from.instrs.clone(),
                final_cfg.z.clone(),
                final_cfg.instrs.clone(),
                step.to.z.clone(),
                step.to.instrs.clone(),
            ];
            acc = self.derive(
                self.trans,
                &args,
                vec![
                    Premise::Derivation(step.thm.clone()),
                    Premise::Derivation(acc),
                ],
            )?;
        }
        Ok(acc)
    }
}

// ===========================================================================
// The straight-line execution demo (shared by tests and `coverage_report`)
// ===========================================================================

/// **The Wave-G acceptance demo**, packaged: execute
///
/// ```text
///   z; [CONST I32 2, CONST I32 3, BINOP I32 ADD, DROP]  ↪*  z; []
/// ```
///
/// hypothesis-free on `env`'s rule set — const-fold through
/// `fn.size ∘ fn.sizenn ∘ fn.iadd_ ∘ fn.binop_ ∘ ev.mem ⟹
/// Step_pure/binop-val`, lift through `Step/pure`, **frame** over the `[DROP]`
/// suffix through `Step/ctxt-instrs` (four `ev.cat`s + `ev.nonempty2` + the
/// `val*` sort guard), then `Step_pure/drop ⟹ Step/pure` on the folded
/// result, and chain both `Step`s through `Steps/trans` onto `Steps/refl`.
///
/// Returns `(trace_thm, from, to, n_steps)` with `from`/`to` the genuine
/// flat-list configuration encodings (`trace_thm` concludes
/// `Derivable ⌜Steps (from, to)⌝` — assert against
/// [`TraceEnv::steps_judgement`]).
pub fn const_fold_drop_trace(env: &TraceEnv, z: &Term) -> Result<(Thm, Config, Config, usize)> {
    use super::flatten::prove_side;
    let nat = |k: u64| covalence_hol_eval::mk_nat(k);
    let i32t = app(con("case.I32"), con("tup"))?;
    let addop = app(con("case.ADD"), con("tup"))?;
    let w32 = app(con("num.nat"), nat(32))?;
    let payload = |k: u64| app(con("tup"), app(con("num.nat"), nat(k))?);
    let iv = |k: u64| app(con("case.%"), payload(k)?);
    let const_i = |k: u64| {
        app(
            con("case.CONST"),
            app(app(con("tup"), i32t.clone())?, iv(k)?)?,
        )
    };
    let dropi = app(con("case.DROP"), con("tup"))?;
    let snoc = |xs: Term, x: Term| app(xs, x);

    // The program and its intermediate states, as flat snoc spines.
    let prog3 = snoc(
        snoc(snoc(con("list"), const_i(2)?)?, const_i(3)?)?,
        app(
            con("case.BINOP"),
            app(app(con("tup"), i32t.clone())?, addop.clone())?,
        )?,
    )?;
    let prog4 = snoc(prog3.clone(), dropi.clone())?;
    let after_fold = snoc(con("list"), const_i(5)?)?;
    let after_fold_drop = snoc(after_fold.clone(), dropi.clone())?;

    // -- Step 1 (Step_pure/binop-val): fold 2 + 3 into 5.
    let fng = |f: &str, args: &[Term], r: &Term| super::fn_graph(f, args, r);
    let d_size = env.derive(
        env.find_at("fn.size", &[], &fng("size", &[i32t.clone()], &w32)?)?,
        &[],
        vec![],
    )?;
    let d_sizenn = env.derive(
        env.nth_of("fn.sizenn", 0)?,
        &[i32t.clone(), w32.clone()],
        vec![Premise::Derivation(d_size)],
    )?;
    let iadd_idx = env.nth_of("fn.iadd_", 0)?;
    let iadd_args = [
        nat(32),
        iv(2)?,
        iv(3)?,
        payload(2)?,
        nat(2),
        payload(3)?,
        nat(3),
        nat(5),
    ];
    let d_unc2 = env.derive(env.nth_of("ev.uncase.%", 0)?, &[payload(2)?], vec![])?;
    let d_prj2 = env.derive(
        env.nth_of("ev.proj.0", 0)?,
        &[app(con("num.nat"), nat(2))?],
        vec![],
    )?;
    let d_unc3 = env.derive(env.nth_of("ev.uncase.%", 0)?, &[payload(3)?], vec![])?;
    let d_prj3 = env.derive(
        env.nth_of("ev.proj.0", 0)?,
        &[app(con("num.nat"), nat(3))?],
        vec![],
    )?;
    let side_add = prove_side(&side_at(env.clause(iadd_idx), &iadd_args, 4)?)?;
    let d_iadd = env.derive(
        iadd_idx,
        &iadd_args,
        vec![
            Premise::Derivation(d_unc2),
            Premise::Derivation(d_prj2),
            Premise::Derivation(d_unc3),
            Premise::Derivation(d_prj3),
            Premise::Side(side_add),
        ],
    )?;
    let binop_add = env.find_at(
        "fn.binop_",
        &[iv(2)?, iv(3)?, w32.clone(), iv(5)?],
        &fng(
            "binop_",
            &[i32t.clone(), addop.clone(), iv(2)?, iv(3)?],
            &snoc(con("list"), iv(5)?)?,
        )?,
    )?;
    let d_badd = env.derive(
        binop_add,
        &[iv(2)?, iv(3)?, w32.clone(), iv(5)?],
        vec![Premise::Derivation(d_sizenn), Premise::Derivation(d_iadd)],
    )?;
    let d_mem = env.derive(env.nth_of("ev.mem", 0)?, &[iv(5)?, con("list")], vec![])?;
    let fold_idx = env
        .rule_index("Step_pure", "binop-val")
        .ok_or_else(|| trace_err("no Step_pure/binop-val"))?;
    let d_fold = env.derive(
        fold_idx,
        &[
            i32t.clone(),
            iv(2)?,
            iv(3)?,
            addop,
            iv(5)?,
            snoc(con("list"), iv(5)?)?,
        ],
        vec![Premise::Derivation(d_badd), Premise::Derivation(d_mem)],
    )?;

    // Lift into `Step` and FRAME over the `[DROP]` suffix: the endpoints are
    // the genuine 4- and 2-instruction flat lists.
    let s1 = env.lift_pure(z, &prog3, &after_fold, d_fold)?;
    let s1 = env.frame(&con("list"), &snoc(con("list"), dropi)?, &s1)?;
    debug_assert_eq!(s1.from.instrs, prog4);
    debug_assert_eq!(s1.to.instrs, after_fold_drop);

    // -- Step 2 (Step_pure/drop): drop the folded constant — whole-sequence,
    //    no framing.
    let drop_idx = env
        .rule_index("Step_pure", "drop")
        .ok_or_else(|| trace_err("no Step_pure/drop"))?;
    let d_sort = env.prove_sort_val(&const_i(5)?)?;
    let d_drop = env.derive(drop_idx, &[const_i(5)?], vec![Premise::Derivation(d_sort)])?;
    let s2 = env.lift_pure(z, &after_fold_drop, &con("list"), d_drop)?;

    // -- The trace: two real steps + refl, folded through Steps/trans.
    let steps = [s1, s2];
    let thm = env.chain(&steps)?;
    Ok((
        thm,
        Config::new(z.clone(), prog4),
        Config::new(z.clone(), con("list")),
        steps.len(),
    ))
}

// ===========================================================================
// Ground-term decomposition
// ===========================================================================

/// Decompose an encoded application node `app(f, x)` (the `st$app` spine of
/// [`super::super::encode::app`]).
fn un_app(t: &Term) -> Option<(&Term, &Term)> {
    let (f, x) = t.as_app()?;
    let (h, g) = f.as_app()?;
    (h.as_free()?.name() == "st$app").then_some((g, x))
}

/// The empty-list encoding `st$c$list`.
fn is_nil(t: &Term) -> bool {
    t.as_free().is_some_and(|v| v.name() == "st$c$list")
}

/// Substitute `args` for the clause's metavariables (in order) in its
/// conclusion — exactly the term `all_elim` instantiation produces.
fn instantiate(c: &Clause, args: &[Term]) -> Term {
    let mut t = c.concl.clone();
    for (mv, a) in c.metavars.iter().zip(args) {
        t = subst_free(&t, &Var::new(metavar_name(mv), phi()), a);
    }
    t
}

/// Instantiate the `k`-th premise of clause `c` at `args` (`Side` premises
/// only — the `prove_side` obligation shape).
pub fn side_at(c: &Clause, args: &[Term], k: usize) -> Result<Term> {
    let LowerPrem::Side(s) = &c.prems[k] else {
        return Err(trace_err(format!("premise {k} is not a Side")));
    };
    let mut t = s.clone();
    for (mv, a) in c.metavars.iter().zip(args) {
        t = subst_free(&t, &Var::new(metavar_name(mv), phi()), a);
    }
    Ok(t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metalogic;
    use crate::wasm::lower::flatten::prove_side;
    use crate::wasm::lower::rule_set_of;
    use crate::wasm::lower::slice::{SliceEnv, exec_slice};
    use crate::wasm::lower::total::{total_spec_clauses, with_total_stack};
    use crate::wasm::spec::wasm_spec;
    use covalence_hol_eval::mk_nat;
    use std::time::Instant;

    fn a(x: Term, y: Term) -> Term {
        app(x, y).unwrap()
    }

    /// A simple ground state: `(struct; struct)` — `Step/pure` threads any
    /// `z` unchanged, so an empty store/frame pair is an honest state term.
    fn ground_z() -> Term {
        a(
            con("case.%;%"),
            a(a(con("tup"), con("struct")), con("struct")),
        )
    }

    /// **THE Wave-G acceptance demo**: a straight-line program executes in
    /// the kernel, hypothesis-free, inside the `exec` slice —
    ///
    /// ```text
    ///   z; [CONST I32 2, CONST I32 3, BINOP I32 ADD, DROP]  ↪*  z; []
    /// ```
    ///
    /// two real `Step`s (const-fold via `Step_pure/binop-val` framed over the
    /// `[DROP]` suffix through `Step/ctxt-instrs`; then `Step_pure/drop`
    /// whole-sequence) chained through `Steps/trans` onto `Steps/refl` — and
    /// the result **transports** into the full combined set via
    /// `slice::transport`. Refusals: a wrong final configuration fails to
    /// chain (kernel premise mismatch), and framing with both context parts
    /// empty fails (the spec's own `=/= []` guard).
    #[test]
    fn straight_line_trace_executes_in_exec_slice_and_transports() {
        // Build the total set + carve on the big-stack thread; the slice
        // itself comes back to this DEFAULT-size test thread — the whole
        // trace (both steps, framing, chaining) derives without
        // `with_total_stack`.
        let (exec, clauses) = with_total_stack(|| {
            let t0 = Instant::now();
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let built_in = t0.elapsed();
            let t1 = Instant::now();
            let exec = exec_slice(&clauses, &report.metas).unwrap();
            println!("total build {built_in:?}, exec carve {:?}", t1.elapsed());
            (exec, clauses)
        });
        let r = exec.report();
        println!(
            "exec slice: {} clauses (of {}), opaque {} in {} clauses (tags: {:?})",
            r.n_clauses,
            r.n_total,
            r.opaque_total(),
            r.n_clauses_opaque,
            r.opaque_tags
        );

        {
            let env = SliceEnv::new(exec);
            let tr = TraceEnv::for_slice(&env).unwrap();
            let z = ground_z();

            let t2 = Instant::now();
            let (thm, from, to, n_steps) = const_fold_drop_trace(&tr, &z).unwrap();
            let trace_in = t2.elapsed();
            assert!(thm.hyps().is_empty(), "trace is hypothesis-free");
            let expected = tr
                .derivable(&tr.steps_judgement(&from, &to).unwrap())
                .unwrap();
            assert_eq!(
                thm.concl(),
                &expected,
                "the trace conclusion IS the Steps statement over the flat program encodings"
            );
            println!(
                "trace: {n_steps} steps + refl chained in {trace_in:?} \
                 ([CONST I32 2, CONST I32 3, BINOP I32 ADD, DROP] ↪* [])"
            );

            // -- Refusal 1: a wrong final configuration cannot chain. Claim
            //    the drop step ends at [CONST I32 6] instead of [] — the
            //    kernel refuses the Steps/trans premise.
            let wrong_cfg = Config::new(
                z.clone(),
                a(
                    con("list"),
                    a(
                        con("case.CONST"),
                        a(
                            a(con("tup"), a(con("case.I32"), con("tup"))),
                            a(
                                con("case.%"),
                                a(con("tup"), a(con("num.nat"), mk_nat(6u64))),
                            ),
                        ),
                    ),
                ),
            );
            // A fake step: genuine theorem, falsified target endpoint.
            let d_sort = tr
                .prove_sort_val(&a(
                    con("case.CONST"),
                    a(
                        a(con("tup"), a(con("case.I32"), con("tup"))),
                        a(
                            con("case.%"),
                            a(con("tup"), a(con("num.nat"), mk_nat(5u64))),
                        ),
                    ),
                ))
                .unwrap();
            let d_drop = tr
                .derive(
                    tr.rule_index("Step_pure", "drop").unwrap(),
                    &[a(
                        con("case.CONST"),
                        a(
                            a(con("tup"), a(con("case.I32"), con("tup"))),
                            a(
                                con("case.%"),
                                a(con("tup"), a(con("num.nat"), mk_nat(5u64))),
                            ),
                        ),
                    )],
                    vec![Premise::Derivation(d_sort)],
                )
                .unwrap();
            let genuine = tr
                .lift_pure(
                    &z,
                    &a(
                        a(
                            con("list"),
                            a(
                                con("case.CONST"),
                                a(
                                    a(con("tup"), a(con("case.I32"), con("tup"))),
                                    a(
                                        con("case.%"),
                                        a(con("tup"), a(con("num.nat"), mk_nat(5u64))),
                                    ),
                                ),
                            ),
                        ),
                        a(con("case.DROP"), con("tup")),
                    ),
                    &con("list"),
                    d_drop,
                )
                .unwrap();
            let faked = TraceStep {
                from: genuine.from.clone(),
                to: wrong_cfg,
                thm: genuine.thm.clone(),
            };
            assert!(
                tr.chain(&[faked]).is_err(),
                "a wrong final state must fail to chain"
            );

            // -- Refusal 2: framing with BOTH context parts empty violates
            //    the spec's `val* =/= [] \/ instr_1* =/= []` guard.
            assert!(
                tr.frame(&con("list"), &con("list"), &genuine).is_err(),
                "empty framing must refuse (ev.nonempty2 underivable)"
            );

            // -- Transport the whole trace into the full 2000+-clause set
            //    (a whole-spec operation: back onto the big-stack thread).
            let judgement = tr.steps_judgement(&from, &to).unwrap();
            let slice = env.slice().clone();
            with_total_stack(move || {
                let full = rule_set_of(clauses);
                let t3 = Instant::now();
                let big = crate::wasm::lower::slice::transport(&slice, &full, &thm).unwrap();
                let transport_in = t3.elapsed();
                assert!(big.hyps().is_empty());
                assert_eq!(
                    big.concl(),
                    &metalogic::derivable(&full, &judgement).unwrap(),
                    "transported trace is literally the full-set Steps statement"
                );
                println!("trace transported into the full set in {transport_in:?}");
            });
        }
    }

    /// **The `ev.lift` payoff (Wave-F2 follow-up)**: DIV const-folds and DIV
    /// by zero TRAPS, both end-to-end through `Step_pure` on the exec slice —
    ///
    /// - `[CONST I32 6, CONST I32 3, BINOP I32 (DIV U)] ~> [CONST I32 2]`:
    ///   the **builtin** `fn.idiv_` clause gives `opt.some(2)`, `ev.lift`
    ///   flattens it to `[2]`, and `Step_pure/binop-val` consumes it;
    /// - `[CONST I32 6, CONST I32 0, BINOP I32 (DIV U)] ~> [TRAP]`: the
    ///   spec's own ground by-zero clause gives `opt.none` (premise-free),
    ///   `ev.lift` flattens it to `[]`, and `Step_pure/binop-trap`'s
    ///   `r = []` side discharges by refl;
    ///
    /// plus the refusal (a wrong quotient's defining side is kernel-refuted).
    /// Both chains were underivable before `ev.lift`: `fn.binop_`'s DIV/REM
    /// conclusions were coarse `lift(r)` spines no rule could consume.
    #[test]
    fn div_const_fold_and_by_zero_trap() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let exec = exec_slice(&clauses, &report.metas).unwrap();
            let env = SliceEnv::new(exec);
            let tr = TraceEnv::for_slice(&env).unwrap();

            let nat = |k: u64| mk_nat(k);
            let i32t = a(con("case.I32"), con("tup"));
            let w32 = a(con("num.nat"), nat(32));
            let payload = |k: u64| a(con("tup"), a(con("num.nat"), nat(k)));
            let iv = |k: u64| a(con("case.%"), payload(k));
            let sx_u = a(con("case.U"), con("tup"));
            let divop = a(con("case.DIV"), a(con("tup"), sx_u.clone()));
            let some = |t: Term| a(con("opt.some"), t);
            let fng =
                |f: &str, args: &[Term], r: &Term| super::super::fn_graph(f, args, r).unwrap();

            // Shared: fn.size(I32) = 32 → fn.sizenn.
            let d_size = tr
                .derive(
                    tr.find_at("fn.size", &[], &fng("size", &[i32t.clone()], &w32))
                        .unwrap(),
                    &[],
                    vec![],
                )
                .unwrap();
            let d_sizenn = tr
                .derive(
                    tr.nth_of("fn.sizenn", 0).unwrap(),
                    &[i32t.clone(), w32.clone()],
                    vec![Premise::Derivation(d_size)],
                )
                .unwrap();

            // ------------------------------------------------------------
            // (a) 6 / 3 = 2 through the BUILTIN idiv_ clause + ev.lift.
            // ------------------------------------------------------------
            let t_a = Instant::now();
            let idiv_target = fng(
                "idiv_",
                &[w32.clone(), sx_u.clone(), iv(6), iv(3)],
                &some(iv(2)),
            );
            let idiv_idx = tr
                .find_at("fn.idiv_", &[nat(6), nat(3), nat(2)], &idiv_target)
                .unwrap();
            let idiv_args = [nat(6), nat(3), nat(2)];
            let sides: Vec<Premise> = (0..tr.clause(idiv_idx).prems.len())
                .map(|k| {
                    Premise::Side(
                        prove_side(&side_at(tr.clause(idiv_idx), &idiv_args, k).unwrap()).unwrap(),
                    )
                })
                .collect();
            let d_idiv = tr.derive(idiv_idx, &idiv_args, sides).unwrap();
            // REFUSAL: 6 / 3 = 3 — some defining side is kernel-refuted.
            let wrong = [nat(6), nat(3), nat(3)];
            assert!(
                (0..tr.clause(idiv_idx).prems.len()).any(|k| {
                    side_at(tr.clause(idiv_idx), &wrong, k)
                        .ok()
                        .is_none_or(|s| prove_side(&s).is_err())
                }),
                "idiv_ must refuse a wrong quotient"
            );

            // ev.lift(some(2), [2]) — the some-clause (1 metavar).
            let lift_some = tr
                .find_at(
                    "ev.lift",
                    &[iv(2)],
                    &ev_graph("lift", &[some(iv(2))], &a(con("list"), iv(2))).unwrap(),
                )
                .unwrap();
            let d_lift = tr.derive(lift_some, &[iv(2)], vec![]).unwrap();

            let binop_div = tr
                .find_at(
                    "fn.binop_",
                    &[
                        sx_u.clone(),
                        iv(6),
                        iv(3),
                        w32.clone(),
                        some(iv(2)),
                        a(con("list"), iv(2)),
                    ],
                    &fng(
                        "binop_",
                        &[i32t.clone(), divop.clone(), iv(6), iv(3)],
                        &a(con("list"), iv(2)),
                    ),
                )
                .unwrap();
            let d_bdiv = tr
                .derive(
                    binop_div,
                    &[
                        sx_u.clone(),
                        iv(6),
                        iv(3),
                        w32.clone(),
                        some(iv(2)),
                        a(con("list"), iv(2)),
                    ],
                    vec![
                        Premise::Derivation(d_sizenn.clone()),
                        Premise::Derivation(d_idiv),
                        Premise::Derivation(d_lift),
                    ],
                )
                .unwrap();
            let d_mem = tr
                .derive(
                    tr.nth_of("ev.mem", 0).unwrap(),
                    &[iv(2), con("list")],
                    vec![],
                )
                .unwrap();
            let fold_idx = tr.rule_index("Step_pure", "binop-val").unwrap();
            let d_div = tr
                .derive(
                    fold_idx,
                    &[
                        i32t.clone(),
                        iv(6),
                        iv(3),
                        divop.clone(),
                        iv(2),
                        a(con("list"), iv(2)),
                    ],
                    vec![Premise::Derivation(d_bdiv), Premise::Derivation(d_mem)],
                )
                .unwrap();
            assert!(d_div.hyps().is_empty());
            println!(
                "(a) [CONST I32 6, CONST I32 3, BINOP I32 (DIV U)] ~> [CONST I32 2] \
                 (builtin idiv_ + ev.lift): {:?}",
                t_a.elapsed()
            );

            // ------------------------------------------------------------
            // (b) 6 / 0 TRAPS through the spec's own by-zero clause.
            // ------------------------------------------------------------
            let t_b = Instant::now();
            let by_zero = tr
                .find_at(
                    "fn.idiv_",
                    &[w32.clone(), iv(6)],
                    &fng(
                        "idiv_",
                        &[w32.clone(), sx_u.clone(), iv(6), iv(0)],
                        &con("opt.none"),
                    ),
                )
                .unwrap();
            let d_zero = tr.derive(by_zero, &[w32.clone(), iv(6)], vec![]).unwrap();
            let lift_none = tr
                .find_at(
                    "ev.lift",
                    &[],
                    &ev_graph("lift", &[con("opt.none")], &con("list")).unwrap(),
                )
                .unwrap();
            let d_lift0 = tr.derive(lift_none, &[], vec![]).unwrap();
            let d_bzero = tr
                .derive(
                    binop_div,
                    &[
                        sx_u.clone(),
                        iv(6),
                        iv(0),
                        w32.clone(),
                        con("opt.none"),
                        con("list"),
                    ],
                    vec![
                        Premise::Derivation(d_sizenn),
                        Premise::Derivation(d_zero),
                        Premise::Derivation(d_lift0),
                    ],
                )
                .unwrap();
            let trap_idx = tr.rule_index("Step_pure", "binop-trap").unwrap();
            let trap_args = [i32t, iv(6), iv(0), divop, con("list")];
            let side_nil =
                prove_side(&side_at(tr.clause(trap_idx), &trap_args, 1).unwrap()).unwrap();
            let d_trap = tr
                .derive(
                    trap_idx,
                    &trap_args,
                    vec![Premise::Derivation(d_bzero), Premise::Side(side_nil)],
                )
                .unwrap();
            assert!(d_trap.hyps().is_empty());
            println!(
                "(b) [CONST I32 6, CONST I32 0, BINOP I32 (DIV U)] ~> [TRAP] \
                 (spec by-zero + ev.lift): {:?}",
                t_b.elapsed()
            );
        })
    }
}
