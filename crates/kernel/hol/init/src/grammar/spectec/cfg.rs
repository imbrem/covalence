//! **Whole-`gram` lowering** — the CFG-stratum bridge, one stratum above the
//! single-symbol [`compile_sym`](super::compile_sym).
//!
//! [`spec_grammar_env`] takes root grammar names, resolves their dependency
//! closure over the bundled WASM 3.0 binary grammars, lowers them (under-
//! approximating; premise/parametric/`ListN` productions skip and report) into
//! a neutral [`covalence_grammar::cfg::Cfg<u8>`], and builds a
//! [`GrammarEnv`](crate::grammar::cfg::GrammarEnv) — the kernel-checked
//! `Derives_E` judgement. [`crate::grammar::cfg::tactic::prove_derives`] then
//! parses concrete bytes into a hypothesis-free `⊢ Derives_E ⌜nt⌝ w`.
//!
//! [`spec_grammar_env_all`] is the **whole-spec** entry point: the universe is
//! *every* bundled grammar (binary `B*` *and* text `T*`), rooted at all of
//! them, in either [`LowerMode`]. Such an env mixes fully-, partially- and
//! un-lowered grammars, so what a proved `Derives_E` theorem *means* varies
//! per non-terminal — [`derives_meaning`] classifies it honestly from the
//! returned [`CfgReport`]. Unlike the `B*`-only closures, the whole-spec `Cfg`
//! is **left-recursive** (the text-format `Thexnum` cycle);
//! [`left_recursion_cycle`] surfaces the finding, and the parsing tactic's
//! guard makes left-recursive descent fail cleanly rather than diverge (at the
//! cost of completeness on those non-terminals).

use covalence_core::Result;
use covalence_grammar::cfg::NtId;
use covalence_spectec::cfg::{
    CfgReport, Coverage, GrammarRoot, LowerMode, lower, lower_recognition, lower_recognition_roots,
};
use covalence_spectec::grammar::{wasm3, wasm3_binary};

use crate::grammar::cfg::GrammarEnv;

/// Build a [`GrammarEnv`] from the dependency closure of `roots` over the
/// bundled WASM 3.0 binary grammars (`covalence_spectec::grammar::wasm3_binary`).
///
/// Returns the env plus the lowering [`CfgReport`] (which productions were
/// skipped and why). Every lowered clause **under-approximates** its SpecTec
/// grammar (`L(Cfg) ⊆ L(SpecTec)`), so a `⊢ Derives_E ⌜nt⌝ w` proved against
/// this env implies membership in the true WASM byte language.
pub fn spec_grammar_env(roots: &[&str]) -> Result<(GrammarEnv, CfgReport)> {
    let grammars = wasm3_binary();
    let (cfg, report) = lower(&grammars, roots);
    let env = GrammarEnv::new(cfg)?;
    Ok((env, report))
}

/// As [`spec_grammar_env`] but using the **recognition-mode** lowering
/// ([`covalence_spectec::cfg::lower_recognition`]) — monomorphising parametric
/// grammars (so LEB128 `BuN`/`BsN`, `Bu32`/`Bu64`, and the `*idx` grammars
/// lower) and over-approximating value-range premises / `ListN` vectors.
///
/// The invariant flips: recognition-mode envs satisfy `L(SpecTec) ⊆ L(Cfg)`, so
/// a `⊢ Derives_E ⌜nt⌝ w` here means "`w` is a well-formed *recognition* of the
/// grammar's byte shape" — NOT that it encodes an in-range value. The
/// [`CfgReport`]'s `premises_dropped` / `listns_widened` / `mono_instances`
/// counters record the approximations. See
/// `notes/vibes/logics/cfg-stratum-design.md` §"M6 — Missing grammars".
pub fn spec_grammar_env_recognition(roots: &[&str]) -> Result<(GrammarEnv, CfgReport)> {
    let grammars = wasm3_binary();
    let (cfg, report) = lower_recognition(&grammars, roots);
    let env = GrammarEnv::new(cfg)?;
    Ok((env, report))
}

/// A kernel grammar environment together with the explicit, identity-bearing
/// roots used to construct it.
pub struct RootedGrammarEnv {
    env: GrammarEnv,
    report: CfgReport,
    roots: Vec<NtId>,
}

impl RootedGrammarEnv {
    /// The kernel-checked CFG environment.
    pub fn env(&self) -> &GrammarEnv {
        &self.env
    }

    /// The lowering coverage/refusal report.
    pub fn report(&self) -> &CfgReport {
        &self.report
    }

    /// Root non-terminals, in the same order as the requested roots.
    pub fn roots(&self) -> &[NtId] {
        &self.roots
    }
}

/// Build a recognition environment for explicit plain or ground-instance
/// roots.
///
/// Unlike [`spec_grammar_env_recognition`], this entry point refuses a generic
/// parameterised root. Each ground instance gets a distinct root judgement,
/// so `BuN(32)` and `BuN(64)`, for example, cannot alias in HOL.
pub fn spec_grammar_env_recognition_roots(roots: &[GrammarRoot]) -> Result<RootedGrammarEnv> {
    let grammars = wasm3();
    let (cfg, report, roots) = lower_recognition_roots(&grammars, roots)
        .map_err(|e| covalence_core::Error::ConnectiveRule(format!("spectec grammar root: {e}")))?;
    Ok(RootedGrammarEnv {
        env: GrammarEnv::new(cfg)?,
        report,
        roots,
    })
}

/// Build the **whole-spec** [`GrammarEnv`]: the universe is *all* bundled
/// WASM 3.0 grammars ([`covalence_spectec::grammar::wasm3`] — the binary `B*`
/// *and* text `T*` corpora), rooted at every grammar name, lowered in the
/// requested [`LowerMode`].
///
/// The result deliberately mixes coverage classes (fully / partially / not
/// lowered grammars all get a non-terminal), so a `⊢ Derives_E ⌜nt⌝ w` over
/// this env does **not** mean the same thing for every `nt` — use
/// [`derives_meaning`] on the returned pair to read off the per-non-terminal
/// guarantee (exact language, membership under-approximation, recognition
/// over-approximation, or none). The per-root functions above keep their
/// tighter single-direction contracts.
///
/// Unlike every `B*`-only closure, the whole-spec `Cfg` is **left-recursive**
/// (the text-format `Thexnum → Thexnum …` cycle) — see
/// [`left_recursion_cycle`]. [`GrammarEnv`] and the kernel judgement are
/// unaffected (soundness never depended on the absence of cycles), and the
/// parsing tactic terminates on left-recursive non-terminals via its
/// in-progress guard, but it is *incomplete* there: some genuinely derivable
/// words may fail to parse.
pub fn spec_grammar_env_all(mode: LowerMode) -> Result<(GrammarEnv, CfgReport)> {
    let grammars = wasm3();
    let roots: Vec<&str> = grammars.iter().map(|g| g.name.as_str()).collect();
    let (cfg, report) = match mode {
        LowerMode::Under => lower(&grammars, &roots),
        LowerMode::Recognition => lower_recognition(&grammars, &roots),
    };
    let env = GrammarEnv::new(cfg)?;
    Ok((env, report))
}

/// One left-recursion finding for a built env, by non-terminal name — `None`
/// when the env is left-recursion-free (every `B*`-only closure), `Some(cycle)`
/// with `cycle.first() == cycle.last()` otherwise (the whole-spec env: the
/// `T*` `Thexnum` cycle). A cycle does not threaten soundness — the kernel
/// judgement is the least fixpoint regardless — but the top-down parsing
/// tactic is incomplete on the non-terminals involved.
pub fn left_recursion_cycle(env: &GrammarEnv) -> Option<Vec<String>> {
    env.cfg().left_recursion().map(|cycle| {
        cycle
            .iter()
            .map(|nt| {
                env.cfg()
                    .nt_name(*nt)
                    .unwrap_or("<out-of-range>")
                    .to_string()
            })
            .collect()
    })
}

/// What a proved `⊢ Derives_E ⌜nt⌝ w` **means**, relative to the true SpecTec
/// language of `nt`'s source grammar, for an env built by
/// [`spec_grammar_env_all`] (or the per-root functions) in `mode` with `report`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerivesMeaning {
    /// Every production of every grammar reachable from this non-terminal
    /// lowered language-preservingly ([`LowerMode::Under`], all-`Full`
    /// closure): `Derives_E ⌜nt⌝` is the **exact** SpecTec language.
    Exact,
    /// `L(env) ⊆ L(SpecTec)` ([`LowerMode::Under`] with skips somewhere in the
    /// reachable closure): a theorem is a true **membership witness**, but the
    /// env cannot derive every member.
    UnderApprox,
    /// `L(SpecTec) ⊆ L(env)` on the reachable closure
    /// ([`LowerMode::Recognition`], all-`Full`): a theorem certifies
    /// **byte-shape recognition** — every true member derives, but so may
    /// out-of-range/over-long encodings (dropped value premises, widened
    /// `ListN`s, LEB128 shapes).
    OverApprox,
    /// No inclusion is guaranteed in either direction (recognition mode with
    /// skipped productions in the reachable closure, an unattributable
    /// non-terminal, or stripped constraint attrs poisoning an under-approx
    /// run). A theorem still certifies derivability *in the lowered `Cfg`*,
    /// just nothing about the SpecTec language.
    Mixed,
    /// The non-terminal has no productions at all: `Derives_E ⌜nt⌝ w` is
    /// never derivable.
    Dead,
}

/// Classify [`DerivesMeaning`] for one non-terminal of `env` (built in `mode`,
/// with lowering `report`).
///
/// The classification is **conservative**: it walks the non-terminals
/// reachable from `nt` through the lowered productions and demands
/// [`Coverage::Full`] of every reached grammar before claiming a direction.
/// Synthetic (`X$…`) and monomorphised-instance (`X@…`) non-terminals
/// attribute to their source grammar `X` via
/// [`CfgReport::coverage_of_nt`] — for instances this may under-claim (e.g.
/// `BuN@32` inherits the generic `BuN`'s class), never over-claim.
pub fn derives_meaning(
    env: &GrammarEnv,
    report: &CfgReport,
    mode: LowerMode,
    nt: NtId,
) -> DerivesMeaning {
    let cfg = env.cfg();
    // One pass over the productions: per-NT adjacency + "has a production".
    let n = cfg.num_nts();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut has_prod = vec![false; n];
    for p in cfg.productions() {
        has_prod[p.lhs.index()] = true;
        for s in &p.segs {
            if let covalence_grammar::cfg::Seg::NonTerm(t) = s {
                edges[p.lhs.index()].push(t.index());
            }
        }
    }
    if !has_prod.get(nt.index()).copied().unwrap_or(false) {
        return DerivesMeaning::Dead;
    }
    // Reachable closure of `nt` over the lowered productions. For an all-`Full`
    // closure this coincides with SpecTec-side reachability (every production
    // of a `Full` grammar lowered, so every spec edge is a `Cfg` edge), which
    // is what the per-direction claims below need.
    let mut seen = vec![false; n];
    let mut stack = vec![nt.index()];
    seen[nt.index()] = true;
    let mut all_full = true;
    while let Some(i) = stack.pop() {
        let name = &cfg.nts()[i].name;
        if report.coverage_of_nt(name) != Some(Coverage::Full) {
            all_full = false;
        }
        for &t in &edges[i] {
            if !seen[t] {
                seen[t] = true;
                stack.push(t);
            }
        }
    }
    match mode {
        // A stripped *constraint* attr widens the language, breaking even the
        // under-approximation invariant; the counter is global, so poison
        // conservatively (pinned zero across the bundled corpus).
        LowerMode::Under if report.attrs_constrained > 0 => DerivesMeaning::Mixed,
        LowerMode::Under if all_full => DerivesMeaning::Exact,
        LowerMode::Under => DerivesMeaning::UnderApprox,
        LowerMode::Recognition if all_full => DerivesMeaning::OverApprox,
        LowerMode::Recognition => DerivesMeaning::Mixed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn breftype_closure_env_builds() {
        // The Attr-stripped Var chain Breftype → Bheaptype → Babsheaptype.
        let (env, _report) = spec_grammar_env(&["Breftype"]).unwrap();
        assert!(env.nt("Breftype").is_some());
        assert!(env.nt("Babsheaptype").is_some());
        // At least the three named grammars became non-terminals.
        assert!(env.cfg().num_nts() >= 3);
    }
}

#[cfg(test)]
mod whole_spec_tests {
    use super::*;

    /// The whole-spec **coverage report** (grammar leg) — the analogue of
    /// `wasm::spec::coverage_report`: build the all-grammar env in both modes,
    /// print the live numbers (`--nocapture`), and pin non-regression floors
    /// just under the measured values so coverage can only climb.
    #[test]
    fn whole_spec_grammar_coverage_report() {
        for (mode, label) in [
            (LowerMode::Under, "under"),
            (LowerMode::Recognition, "recognition"),
        ] {
            let (env, report) = spec_grammar_env_all(mode).unwrap();
            let cycle = left_recursion_cycle(&env);
            println!("--- whole-spec grammar env ({label}) ---");
            println!("{report}");
            println!(
                "env: {} clauses over {} non-terminals; left recursion: {cycle:?}",
                env.n_clauses(),
                env.cfg().num_nts(),
            );

            // The whole universe: every one of the 231 bundled grammars (89
            // B* + 142 T*) is classified, and the T* corpus makes the env
            // left-recursive (the Thexnum cycle) in both modes.
            assert_eq!(report.grammars.len(), 231, "whole 231-grammar universe");
            assert!(cycle.is_some(), "T* corpus is left-recursive ({label})");

            // Non-regression floors (raise as coverage grows) + skip ceilings
            // (lower as buckets shrink). Measured today: Under 1129 prods /
            // 1245 clauses / 280 NTs / 302 skips; Recognition 1221 / 1526 /
            // 385 / 210 (grammar-valued monomorphisation: `Bmodule` + the 14
            // section grammars + the `Blist` chain lower; residue = the 66
            // `T*` context-param grammars + generic `BiN`/`Blist`).
            let (prods_floor, clauses_floor, nts_floor, skip_ceiling) = match mode {
                LowerMode::Under => (1129, 1245, 280, 302),
                LowerMode::Recognition => (1221, 1526, 385, 210),
            };
            assert!(
                report.lowered_prods >= prods_floor,
                "{label}: prods lowered = {}",
                report.lowered_prods
            );
            assert!(
                env.n_clauses() >= clauses_floor,
                "{label}: clauses = {}",
                env.n_clauses()
            );
            assert!(
                env.cfg().num_nts() >= nts_floor,
                "{label}: NTs = {}",
                env.cfg().num_nts()
            );
            assert!(
                report.skipped_total() <= skip_ceiling,
                "{label}: skipped = {} (per-bucket: {:?})",
                report.skipped_total(),
                report.skipped
            );
        }
    }

    /// Per-bucket skip ceilings for the whole-spec runs — the fine-grained
    /// non-regression companion to the totals above.
    #[test]
    fn whole_spec_skip_buckets() {
        use covalence_spectec::cfg::SkipReason;
        let ceilings = |report: &CfgReport, expect: &[(SkipReason, usize)]| {
            for &(reason, ceiling) in expect {
                let got = report.skipped.get(&reason).copied().unwrap_or(0);
                assert!(got <= ceiling, "{reason:?}: {got} > ceiling {ceiling}");
            }
        };
        let (_env, report) = spec_grammar_env_all(LowerMode::Under).unwrap();
        ceilings(
            &report,
            &[
                (SkipReason::ParametricRef, 236),
                (SkipReason::Premise, 47),
                (SkipReason::ListN, 8),
                (SkipReason::IterWithDom, 9),
                (SkipReason::Bridge, 2),
            ],
        );
        let (_env, report) = spec_grammar_env_all(LowerMode::Recognition).unwrap();
        ceilings(
            &report,
            &[
                (SkipReason::ParametricRef, 204),
                (SkipReason::Premise, 4),
                (SkipReason::Bridge, 2),
            ],
        );
    }

    /// [`derives_meaning`] reads the per-non-terminal guarantee off the pair:
    /// exact/under on the under-approx env, recognition/mixed on the
    /// recognition env, dead where nothing lowered.
    #[test]
    fn derives_meaning_classifies_per_nt() {
        let (env, report) = spec_grammar_env_all(LowerMode::Under).unwrap();
        // Babsheaptype: fully regular, self-contained ⇒ the exact language.
        let abs = env.nt("Babsheaptype").unwrap();
        assert_eq!(
            derives_meaning(&env, &report, LowerMode::Under, abs),
            DerivesMeaning::Exact
        );
        // Breftype reaches Bheaptype (Partial: its Bs33 premise branch skips)
        // ⇒ an honest membership under-approximation.
        let refty = env.nt("Breftype").unwrap();
        assert_eq!(
            derives_meaning(&env, &report, LowerMode::Under, refty),
            DerivesMeaning::UnderApprox
        );
        // A parametric grammar lowers nothing under-approximately ⇒ dead.
        let bun = env.nt("BuN").unwrap();
        assert_eq!(
            derives_meaning(&env, &report, LowerMode::Under, bun),
            DerivesMeaning::Dead
        );

        let (env, report) = spec_grammar_env_all(LowerMode::Recognition).unwrap();
        // Full-closure grammar ⇒ a sound recognizer (over-approximation).
        let abs = env.nt("Babsheaptype").unwrap();
        assert_eq!(
            derives_meaning(&env, &report, LowerMode::Recognition, abs),
            DerivesMeaning::OverApprox
        );
        // A monomorphised instance NT attributes (conservatively) to its
        // generic source grammar, which is not Full ⇒ no claimed direction.
        let inst = env.nt("BuN@32").expect("recognition mode mints BuN@32");
        assert_eq!(
            derives_meaning(&env, &report, LowerMode::Recognition, inst),
            DerivesMeaning::Mixed
        );
    }

    /// The left-recursion detector pins the `Thexnum` cycle specifically
    /// (rooted at `Thexnum`, any cycle lies in its closure), and the top-down
    /// tactic **terminates** on the left-recursive non-terminal — cleanly
    /// accepting via span-shrinking descent or rejecting, never diverging.
    #[test]
    fn thexnum_left_recursion_flagged_and_tactic_terminates() {
        use covalence_spectec::cfg::lower_recognition;
        use covalence_spectec::grammar::wasm3;

        let grammars = wasm3();
        let (cfg, report) = lower_recognition(&grammars, &["Thexnum"]);
        let env = GrammarEnv::new(cfg).unwrap();
        let cycle = left_recursion_cycle(&env).expect("Thexnum closure is left-recursive");
        assert!(
            cycle.iter().any(|n| n == "Thexnum"),
            "cycle {cycle:?} names Thexnum"
        );
        println!("Thexnum closure: {report}");
        println!("Thexnum cycle: {cycle:?}");

        // The tactic must terminate on the left-recursive NT for accept and
        // reject inputs alike (the in-progress guard cuts same-span re-entry).
        let nt = env.nt("Thexnum").unwrap();
        for w in [&b"7"[..], b"7a", b""] {
            let res = crate::grammar::cfg::tactic::prove_derives(&env, nt, w);
            println!(
                "prove_derives(Thexnum, {w:?}) -> {:?}",
                res.as_ref().map(|o| o.is_some())
            );
            res.unwrap(); // terminates without a kernel error
        }
    }
}

#[cfg(test)]
mod recog_tests {
    use super::*;
    use covalence_spectec::ast::{SpecTecArg, SpecTecExp, SpecTecNum};

    #[test]
    fn bu32_recognition_env_builds_with_leb128_instance() {
        // Bu32 = BuN(32); recognition mode monomorphises the parametric ref into
        // the instance NT `BuN@32`, lowered to the LEB128 regex terminal.
        let (env, report) = spec_grammar_env_recognition(&["Bu32"]).unwrap();
        assert!(env.nt("Bu32").is_some());
        let names: Vec<&str> = env.cfg().nts().iter().map(|d| d.name.as_str()).collect();
        assert!(
            names.contains(&"BuN@32"),
            "expected a monomorphised BuN@32 instance, got {names:?}"
        );
        // The recognition-mode approximation is recorded honestly.
        assert!(report.mono_instances >= 1);
    }

    #[test]
    fn explicit_ground_instances_have_distinct_hol_roots() {
        let arg = |n| SpecTecArg::Exp {
            e: SpecTecExp::Num {
                n: SpecTecNum::Nat(n),
            },
        };
        let rooted = spec_grammar_env_recognition_roots(&[
            GrammarRoot::Instance {
                name: "BuN".into(),
                args: vec![arg(32)],
            },
            GrammarRoot::Instance {
                name: "BuN".into(),
                args: vec![arg(64)],
            },
        ])
        .unwrap();
        assert_ne!(rooted.roots()[0], rooted.roots()[1]);
        assert!(rooted.env().nt("BuN@32").is_some());
        assert!(rooted.env().nt("BuN@64").is_some());
    }
}
