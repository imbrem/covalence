//! **The bundled WebAssembly spec** — load the real SpecTec AST and inventory /
//! measure coverage against it.
//!
//! [`covalence_spectec::wasm::get_wasm_spectec_ast`] ships the WebAssembly **3.0**
//! specification pre-elaborated as `Vec<SpecTecDef>`. This module is the grounding
//! harness (the analogue of the Metamath `import_hol_mm` / `scan_failures` tests):
//! it classifies the spec and reports how much of it the front end can currently
//! lower, so progress toward *importing the whole spec* is a live, measurable
//! number rather than a guess.
//!
//! There is no separately-bundled WASM 1.0/2.0 AST yet (see `covalence-spectec`'s
//! the generated open-work index); "start with WASM 1" means working the **feature subset** —
//! e.g. a handful of numeric `*_ok` relations — out of the 3.0 dump first.

use covalence_spectec::ast::{SpecTecArg, SpecTecDef, SpecTecExp, SpecTecParam, SpecTecTyp};
use covalence_spectec::wasm::get_wasm_spectec_ast;

use super::{relation, syntax};

/// The bundled WebAssembly 3.0 spec as a flat list of top-level definitions.
pub fn wasm_spec() -> Vec<SpecTecDef> {
    get_wasm_spectec_ast()
}

/// Counts of each kind of definition (recursively, flattening `rec` groups).
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Inventory {
    pub types: usize,
    pub relations: usize,
    pub functions: usize,
    pub grammars: usize,
    pub rec_groups: usize,
}

/// Classify a definition list (descending into `rec` groups).
pub fn inventory(defs: &[SpecTecDef]) -> Inventory {
    fn go(d: &SpecTecDef, inv: &mut Inventory) {
        match d {
            SpecTecDef::Typ { .. } => inv.types += 1,
            SpecTecDef::Rel { .. } => inv.relations += 1,
            SpecTecDef::Dec { .. } => inv.functions += 1,
            SpecTecDef::Gram { .. } => inv.grammars += 1,
            SpecTecDef::Rec { ds } => {
                inv.rec_groups += 1;
                ds.iter().for_each(|x| go(x, inv));
            }
        }
    }
    let mut inv = Inventory::default();
    defs.iter().for_each(|d| go(d, &mut inv));
    inv
}

/// How many whole relations lower with [`relation::rule_set`] (every rule of the
/// relation expressible), out of the total relation count.
pub fn fully_lowered_relations(defs: &[SpecTecDef]) -> (usize, usize) {
    fn rels<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
        match d {
            SpecTecDef::Rel { .. } => out.push(d),
            SpecTecDef::Rec { ds } => ds.iter().for_each(|x| rels(x, out)),
            _ => {}
        }
    }
    let mut all = Vec::new();
    defs.iter().for_each(|d| rels(d, &mut all));
    let total = all.len();
    let ok = all.iter().filter(|d| relation::rule_set(d).is_ok()).count();
    (ok, total)
}

fn typ_defs(defs: &[SpecTecDef]) -> Vec<&SpecTecDef> {
    fn typs<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
        match d {
            SpecTecDef::Typ { .. } => out.push(d),
            SpecTecDef::Rec { ds } => ds.iter().for_each(|x| typs(x, out)),
            _ => {}
        }
    }
    let mut all = Vec::new();
    defs.iter().for_each(|d| typs(d, &mut all));
    all
}

/// The **strict** type-rendering count: how many `Typ` definitions render to a
/// HOL type **standalone** via [`syntax::resolve_def`], out of the total type
/// count. By design this counts every parametric definition as a failure
/// (standalone, it has no arguments to instantiate with) — see
/// [`renderable_types`] for the use-site-aware count.
pub fn rendered_types(defs: &[SpecTecDef]) -> (usize, usize) {
    let all = typ_defs(defs);
    let ctx = syntax::TypeCtx::new(defs);
    let total = all.len();
    let ok = all
        .iter()
        .filter(|d| syntax::resolve_def(d, &ctx).is_ok())
        .count();
    (ok, total)
}

/// The **use-site-aware** type-rendering count: a `Typ` definition counts as
/// renderable if it renders standalone *or* — when parametric — it instantiates
/// when applied to arguments built from its own declared parameters (a fresh
/// metavariable named after each value parameter, so instance dispatch sees the
/// declared supertype; `bool` for each type parameter), which is how real use
/// sites apply it. This is the honest coverage number: most parametric
/// definitions are used *only* applied, so counting them as standalone failures
/// under-reports the front end.
pub fn renderable_types(defs: &[SpecTecDef]) -> (usize, usize) {
    let all = typ_defs(defs);
    let ctx = syntax::TypeCtx::new(defs);
    let total = all.len();
    let ok = all
        .iter()
        .filter(|d| {
            syntax::resolve_def(d, &ctx).is_ok() || instantiates_with_declared_params(d, &ctx)
        })
        .count();
    (ok, total)
}

/// Whether a parametric `Typ` definition resolves when applied to dummy
/// arguments derived from its declared parameters.
fn instantiates_with_declared_params(def: &SpecTecDef, ctx: &syntax::TypeCtx) -> bool {
    let SpecTecDef::Typ { x, ps, .. } = def else {
        return false;
    };
    if ps.is_empty() {
        return false;
    }
    let mut as1 = Vec::with_capacity(ps.len());
    for p in ps {
        match p {
            SpecTecParam::Exp { x: pname, .. } => as1.push(SpecTecArg::Exp {
                e: SpecTecExp::Var { id: pname.clone() },
            }),
            SpecTecParam::Typ { .. } => as1.push(SpecTecArg::Typ {
                t: SpecTecTyp::Bool,
            }),
            // def/grammar parameters aren't modelled — not renderable this way.
            _ => return false,
        }
    }
    let app = SpecTecTyp::Var { x: x.clone(), as1 };
    syntax::resolve_typ(&app, ctx).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wasm_spec_loads_and_has_the_expected_shape() {
        let defs = wasm_spec();
        assert!(!defs.is_empty());
        let inv = inventory(&defs);
        // The 3.0 dump is large and relation-rich; guard the coarse shape so a
        // future dep bump that silently empties it fails loudly.
        assert!(inv.relations >= 100, "relations = {}", inv.relations);
        assert!(inv.types >= 100, "types = {}", inv.types);
        assert!(inv.functions >= 100, "functions = {}", inv.functions);
    }

    /// Instance dispatch on the real spec: `num_(I32)` selects the `Inn`
    /// instance (`num_(Inn) = iN(…) = uN(…) = nat`), `num_(F32)` correctly
    /// refuses (the `fN` parametric-case gap), and the `unop_` family joins
    /// under an indeterminate `numtype` argument.
    #[test]
    fn instance_dispatch_on_the_real_spec() {
        use covalence_spectec::ast::MixOp;
        let defs = wasm_spec();
        let ctx = syntax::TypeCtx::new(&defs);
        let apply = |name: &str, e: SpecTecExp| SpecTecTyp::Var {
            x: name.into(),
            as1: vec![SpecTecArg::Exp { e }],
        };
        let case = |name: &str| SpecTecExp::Case {
            op: MixOp::new(vec![name.into()]),
            e1: Box::new(SpecTecExp::Tup { es: vec![] }),
        };
        let t = syntax::resolve_typ(&apply("num_", case("I32")), &ctx).unwrap();
        assert_eq!(t, covalence_core::Type::nat());
        assert!(syntax::resolve_typ(&apply("num_", case("F32")), &ctx).is_err());
        assert!(
            syntax::resolve_typ(
                &apply(
                    "unop_",
                    SpecTecExp::Var {
                        id: "numtype".into()
                    }
                ),
                &ctx
            )
            .is_ok()
        );
    }

    /// The live **coverage** metric, v2 (the total-load combined set): every
    /// rule and every `Dec` clause of the whole spec loads; the combined
    /// clause list is built and kernel-checked; residue is censused exactly.
    /// Printed with `--nocapture`; floors sit just under measured values so
    /// the numbers can climb without churning the test.
    #[test]
    fn coverage_report() {
        use crate::wasm::lower::total::{total_spec_clauses, with_total_stack};
        with_total_stack(|| {
            let t0 = std::time::Instant::now();
            let defs = wasm_spec();
            let inv = inventory(&defs);
            let (clauses, report) = total_spec_clauses(&defs).expect("total load");
            let lowered_in = t0.elapsed();

            // Kernel check: the whole combined set builds as one RuleSet and
            // every clause term type-checks in the layout.
            let t1 = std::time::Instant::now();
            let rs = crate::wasm::lower::rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();
            let kernel_in = t1.elapsed();

            let (typ_ok, typ_total) = rendered_types(&defs);
            let (rdr_ok, rdr_total) = renderable_types(&defs);
            let catalogue = syntax::CaseCatalogue::new(&defs);

            println!("inventory: {inv:?}");
            println!("=== total-load coverage (combined set) ===");
            println!(
                "rules loaded:       {} / 558 (fully flattened {})",
                report.rules.total_rules, report.rules.fully_flattened
            );
            println!(
                "dec clauses loaded: {} / 804 (clean {}, cond-only {}, opaque {})",
                report.decs.spec_loaded,
                report.decs.spec_clean,
                report.decs.spec_cond_only,
                report.decs.spec_opaque
            );
            println!(
                "star sites:         {} ({} aux clauses)",
                report.rules.star_sites, report.n_star_aux
            );
            println!(
                "combined clauses:   {} = {} rule + {} star + {} dec + {} builtin + {} ev (neq pairs {})",
                report.total_clauses,
                report.n_rule_clauses,
                report.n_star_aux,
                report.n_dec_clauses,
                report.n_builtin_clauses,
                report.n_evaluator_clauses,
                report.neq_pairs
            );
            println!(
                "exact builtins:     {} defining clauses over {} ops ({} of {} zero-clause tags filled; frontier {})",
                report.builtins.clauses,
                report.builtins.ops,
                report.builtins.zero_clause_ops,
                report.decs.builtins,
                report.decs.builtins - report.builtins.zero_clause_ops
            );
            println!(
                "sort fix:           {} guarded rules ({} guard premises); dec: {} expanded copies, {} guard premises",
                report.rules.sort_guarded_rules,
                report.rules.sort_guard_premises,
                report.decs.expanded_clauses,
                report.decs.sort_guards
            );
            let write_clauses = report
                .metas
                .iter()
                .filter(|m| m.relation.starts_with("ev.upd.") || m.relation.starts_with("ev.ext."))
                .count();
            let write_families: std::collections::BTreeSet<&str> = report
                .metas
                .iter()
                .filter(|m| m.relation.starts_with("ev.upd.") || m.relation.starts_with("ev.ext."))
                .map(|m| m.relation.as_str())
                .collect();
            println!(
                "store writes:       {} ev.upd/ev.ext clauses over {} path families",
                write_clauses,
                write_families.len()
            );
            println!(
                "opaque premises:    {} total, by tag:",
                report.opaque_total()
            );
            for (k, c) in &report.opaque_tags {
                println!("  {c:>4}  {k}");
            }
            for site in &report.opaque_sites {
                println!(
                    "         clause {} premise {}  {}/{}  {}",
                    site.clause_index,
                    site.premise_index,
                    site.relation,
                    site.rule_name,
                    site.reason
                );
            }
            println!("lowering: {lowered_in:?}; kernel layout of {n} clauses: {kernel_in:?}");
            println!("types rendered to HOL standalone (leg B, strict): {typ_ok} / {typ_total}");
            println!("types renderable (standalone or at use sites): {rdr_ok} / {rdr_total}");
            println!(
                "case catalogue (total, reified): {} variant types",
                catalogue.n_variants()
            );

            // TOTAL LOAD, exact: every rule and every Dec source clause.
            assert_eq!(report.rules.total_rules, 558);
            assert_eq!(report.decs.spec_loaded, 804);
            assert_eq!(report.rules.star_sites, 92);
            assert_eq!(n, report.total_clauses, "kernel-checked clause count");

            // Floors just under measured (2026-07-17, post Wave-D sort fix +
            // RHS result flattening + Wave-E encoding injectivity R1-F1/F2 +
            // cond.slice/cond.coarse-eq guards R3-F1 + the R4-F1
            // clause-order fix + the Wave-F `ev.upd`/`ev.ext` write
            // families). Both Wave-E fixes LOWER the clean counts
            // and RAISE the opaque census, correctly:
            // - fully flattened 510 -> 502: rules whose `Eq` sides carry
            //   value-dead `Slice`/`Cvt` spines were counted flat while
            //   their Side equations could never be discharged at a genuine
            //   ground point - censused opaque now (cond.slice /
            //   cond.coarse-eq), never silent.
            // - dec clean 691 -> ~656: `Dec` clauses match in order, and 23
            //   functions' later clauses (idiv_/irem_ truncating legs, the
            //   subst_*/free_* catch-alls, utf8, ...) overlapped an earlier
            //   sibling with a divergent RHS; they now carry censused
            //   `dec.order` premises or injected negated-guard conditions.
            // - Wave F RAISES dec clean 659 -> 668 and SHRINKS
            //   `dec.coarse-spine` 58 -> 49: the 9 idx-path `Upd` RHSs
            //   (`$with_local`/`$with_global`/`$with_table`/… store writers)
            //   now conclude with the evaluated updated value; only
            //   `$with_mem`'s slice-path write plus the zip/map iteration
            //   RHSs stay coarse.
            assert!(
                report.rules.fully_flattened >= 553,
                "fully flattened = {}",
                report.rules.fully_flattened
            );
            assert!(
                report.decs.spec_clean >= 802,
                "dec clean = {}",
                report.decs.spec_clean
            );
            assert!(
                report.total_clauses >= 7393,
                "combined clauses = {}",
                report.total_clauses
            );
            // The exact-host-builtin leg is live (Waves F2/Y/Z/AA/AB/AC/AE):
            // defining clauses for 64 operations, incl. first clauses for 53
            // of the 91 zero-clause tags (integer operations, structural
            // rational rounding, typed byte front doors, structural IEEE
            // representation/sign operations, and inverse sequence graphs).
            assert!(
                report.n_builtin_clauses >= 3917,
                "builtin clauses = {}",
                report.n_builtin_clauses
            );
            assert_eq!(report.builtins.ops, 64, "builtin ops covered");
            assert_eq!(
                report.builtins.zero_clause_ops, 53,
                "zero-clause builtin tags filled"
            );
            assert!(
                report.opaque_total() <= 7,
                "opaque premises regressed: {}",
                report.opaque_total()
            );
            assert_eq!(
                report.opaque_sites.len(),
                report.opaque_total(),
                "opaque site inventory is exact"
            );
            let opaque_sites: Vec<_> = report
                .opaque_sites
                .iter()
                .map(|site| {
                    (
                        site.clause_index,
                        site.premise_index,
                        site.relation.as_str(),
                        site.rule_name.as_str(),
                        site.reason.as_str(),
                    )
                })
                .collect();
            assert_eq!(
                opaque_sites,
                [
                    (366, 0, "Step_read", "br_on_cast-fail", "else"),
                    (368, 0, "Step_read", "br_on_cast_fail-fail", "else"),
                    (431, 0, "Step_read", "ref.test-false", "else"),
                    (433, 0, "Step_read", "ref.cast-fail", "else"),
                    (466, 0, "Step_read", "array.init_data-zero", "else"),
                    (1773, 11, "fn.vcvtop__", "", "dec.order"),
                    (1996, 0, "fn.NotImmutReachable", "", "dec.else-nonif-guard",),
                ],
                "opaque source addresses or clause order changed"
            );
            use crate::wasm::lower::total::OpaqueCapability as C;
            assert_eq!(
                report
                    .opaque_sites
                    .iter()
                    .map(|site| site.required_capability.clone())
                    .collect::<Vec<_>>(),
                [
                    C::ReferenceCastApplicability,
                    C::ReferenceCastApplicability,
                    C::ReferenceCastApplicability,
                    C::ReferenceCastApplicability,
                    C::ArrayDataOutOfBoundsApplicability,
                    C::VcvtopExistentialPredecessors,
                    C::ImmutReachableNegation,
                ],
                "opaque proof-capability classification changed"
            );
            // The write families are live (measured: 54 clauses / 27 path
            // families incl. `ev.upd.root.dot.LOCALS.idx` and the
            // `with_mem` slice path. No Dec conclusion may retain a coarse
            // iteration/write spine.
            assert!(
                write_clauses >= 50,
                "ev.upd/ev.ext clauses = {write_clauses}"
            );
            assert!(
                write_families.contains("ev.upd.root.dot.LOCALS.idx")
                    && write_families.contains("ev.upd.root.dot.TABLES.idx.dot.REFS.idx"),
                "expected write families missing: {write_families:?}"
            );
            let coarse = report
                .opaque_tags
                .get("dec.coarse-spine")
                .copied()
                .unwrap_or(0);
            assert_eq!(coarse, 0, "dec.coarse-spine premises");
            // The clause-order complements are present (a collapse to 0
            // would mean divergent-RHS Dec overlaps fire unguarded again),
            // and no premise mentions an unresolved Def-param tag (R4-F2:
            // `fn.f_` premises were silently underivable and uncensused).
            let order = report.opaque_tags.get("dec.order").copied().unwrap_or(0);
            assert_eq!(order, 1, "dec.order premises");
            assert!(
                !report.opaque_tags.keys().any(|k| k == "dec.def-param"),
                "unresolved Def-param callees on the bundled corpus: {:?}",
                report.opaque_tags
            );

            // The sort fix is live (measured 2026-07-17: 197 guarded rules /
            // 265 guard premises; after preserving mapped iterations through
            // the Dec/flattener boundary the Dec leg uses 395 expanded copies
            // + 110 guards (more sites can take the exact finite expansion
            // path instead of a guarded opaque map).
            // Floors just under measured; a collapse to 0 would mean the
            // sortless-metavariable over-approximation is back.
            assert!(
                report.rules.sort_guarded_rules >= 190,
                "sort-guarded rules = {}",
                report.rules.sort_guarded_rules
            );
            assert!(
                report.rules.sort_guard_premises >= 260,
                "sort guard premises = {}",
                report.rules.sort_guard_premises
            );
            assert!(
                report.decs.expanded_clauses >= 360,
                "dec expanded copies = {}",
                report.decs.expanded_clauses
            );
            assert!(
                report.decs.sort_guards >= 100,
                "dec sort guards = {}",
                report.decs.sort_guards
            );

            // Type-leg floors (unchanged).
            assert!(typ_ok >= 100, "types rendered = {typ_ok}");
            assert!(rdr_ok >= typ_ok, "renderable < strict?!");
            assert!(rdr_ok >= 135, "types renderable = {rdr_ok}");
            // The reified catalogue is total over every variant type in the spec:
            // 111 plain variant defs + 9 variant-bodied multi-instance families
            // (`unop_` … `vcvtop__`; the alias-bodied `num_`/`lane_`/`lit_` have no
            // cases of their own).
            assert_eq!(catalogue.n_variants(), 120, "catalogue variant count");

            // The trace demo (Wave G): the exec slice EXECUTES a straight-line
            // program — two real Steps (const-fold framed over the [DROP]
            // suffix via Step/ctxt-instrs, then drop) chained through
            // Steps/trans onto Steps/refl. Numbers printed; the only floor is
            // that it derives (stable).
            use crate::wasm::encode::{app as eapp, con as econ};
            use crate::wasm::lower::slice::{SliceEnv, exec_slice};
            use crate::wasm::lower::trace::{TraceEnv, const_fold_drop_trace};
            let t2 = std::time::Instant::now();
            let exec = exec_slice(&clauses, &report.metas).expect("exec slice");
            let er = exec.report();
            let env = SliceEnv::new(exec);
            let tr = TraceEnv::for_slice(&env).expect("trace env");
            let z = eapp(
                econ("case.%;%"),
                eapp(eapp(econ("tup"), econ("struct")).unwrap(), econ("struct")).unwrap(),
            )
            .unwrap();
            let (trace_thm, from, to, n_steps) =
                const_fold_drop_trace(&tr, &z).expect("the straight-line trace derives");
            let trace_in = t2.elapsed();
            assert!(trace_thm.hyps().is_empty(), "trace is hypothesis-free");
            let expected = tr
                .derivable(&tr.steps_judgement(&from, &to).unwrap())
                .unwrap();
            assert_eq!(
                trace_thm.concl(),
                &expected,
                "trace concludes Steps(prog, [])"
            );
            println!(
                "trace demo:         {n_steps} steps + refl — z; [CONST I32 2, CONST I32 3, \
                 BINOP I32 ADD, DROP] ↪* z; [] on the `exec` slice ({} clauses) in {trace_in:?}",
                er.n_clauses
            );
        })
    }

    /// The v1 lowering path still works (kept for comparison — see
    /// [`relation::spec_rule_set`]); its floors are frozen, not raised.
    #[test]
    fn coverage_report_v1() {
        let defs = wasm_spec();
        let (rs, report) = relation::spec_rule_set(&defs);
        let clauses = rs.n_clauses().unwrap();
        let (full_ok, full_total) = fully_lowered_relations(&defs);
        println!(
            "v1 rule set: {} clauses ({} lowered / {} skipped); whole relations {full_ok}/{full_total}",
            clauses, report.lowered, report.skipped
        );
        assert!(report.lowered >= 250, "rules lowered = {}", report.lowered);
        assert_eq!(clauses, report.lowered);
        assert!(full_ok >= 60, "whole relations lowered = {full_ok}");
    }
}
