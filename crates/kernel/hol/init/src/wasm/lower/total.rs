//! **The combined whole-spec rule set** — every definition of the bundled
//! WASM 3.0 SpecTec dump as ONE kernel-checked clause list: all 558 relation
//! rules (Else-preprocessed, condition-flattened, iteration-starred), all
//! `Dec` equation clauses as `fn.*` graph relations (monomorphised
//! combinators included), the per-site `star.*` aux clauses, and the
//! on-demand `ev.*` evaluator clauses — **deduplicated across legs** (one
//! shared [`Flattener`] pool keyed by tag, so e.g. `ev.cat` is emitted once
//! whether a rule condition or a `Dec` `Cat` split asked for it).
//!
//! ## Clause-order contract (load-bearing for addressing)
//!
//! ```text
//!   [0 .. n_rule_clauses)                          — one clause per spec rule,
//!                                                    flattened relation/rule order
//!   [.. + n_star_aux)                              — star aux clauses, per-rule
//!                                                    groups in rule order
//!   [.. + n_dec_clauses)                           — fn.* graph clauses, Dec order
//!                                                    (mono instances in discovery order)
//!   [.. + n_builtin_clauses)                       — integer-builtin defining clauses
//!                                                    ([`super::builtins`]: op families in
//!                                                    OPS order, widths ascending)
//!   [.. + n_evaluator_clauses)                     — ev.* clauses, first-demand order
//! ```
//!
//! [`TotalReport::metas`] carries one [`ClauseMeta`] per clause in exactly
//! this order — `(relation, rule-name, metavar order)` for rule clauses; for
//! aux/graph/evaluator clauses the relation is the conclusion's tag
//! (`star.<rel>.<rule>.<idx>` / `fn.<f>[$<op>…]` / `ev.<op>[.…]`) and the
//! name is empty. `crate::spectec::RelationEnv::spec` serves this set through
//! the Fragment API.
//!
//! Soundness frame as everywhere in this tree: loading is total and
//! *under*-approximating — inexpressible premises stay as underivable
//! `opaque.*` antecedents, censused in [`TotalReport::opaque_tags`] (no
//! silent truncation).

use std::collections::BTreeMap;

use covalence_core::{Result, Term};
use covalence_spectec::ast::{SpecTecDef, SpecTecRule};

use super::super::syntax::CaseCatalogue;
use super::builtins::{BuiltinReport, builtin_clauses};
use super::decs::{FnCensus, opaque_reason, spec_fn_clauses};
use super::flatten::{CensusReport, Flattener, spec_rule_clauses};
use super::{Clause, LowerPrem, rule_set_of};
use crate::metalogic::RuleSet;

/// Per-clause addressing metadata for the combined set (see the module-doc
/// order contract).
#[derive(Debug, Clone)]
pub struct ClauseMeta {
    /// The relation tag: the SpecTec relation name for rule clauses; the
    /// conclusion tag (`star.*` / `fn.*` / `ev.*`) for aux clauses.
    pub relation: String,
    /// The rule's name for rule clauses (`""` for unnamed rules and for all
    /// aux clauses).
    pub name: String,
    /// The clause's metavariable ids in `∀`/instantiation order (the
    /// authoritative post-lowering order, including flattener-fresh vars).
    pub metavars: Vec<String>,
}

/// The one report for the combined set (headline numbers first; the per-leg
/// censuses ride along in full).
#[derive(Debug, Clone)]
pub struct TotalReport {
    /// The rule-lowering census (all 558 rules).
    pub rules: CensusReport,
    /// The `Dec` graph-relation census (all 804 source clauses).
    pub decs: FnCensus,
    /// Rule clauses (== `rules.total_rules`).
    pub n_rule_clauses: usize,
    /// Star aux clauses.
    pub n_star_aux: usize,
    /// `fn.*` graph clauses emitted (source + extra mono copies).
    pub n_dec_clauses: usize,
    /// Integer-builtin defining clauses ([`super::builtins`]).
    pub n_builtin_clauses: usize,
    /// The builtin leg's own census (ops covered / zero-clause tags filled).
    pub builtins: BuiltinReport,
    /// Evaluator clauses (deduplicated across the rule and Dec legs).
    pub n_evaluator_clauses: usize,
    /// `ev.neq` ordered tag pairs among them.
    pub neq_pairs: usize,
    /// Total combined clause count.
    pub total_clauses: usize,
    /// Opaque premises actually present in the combined clause list, by
    /// reason tag with counts — the exact honest-residue census.
    pub opaque_tags: BTreeMap<String, usize>,
    /// Per-clause addressing metadata, in clause order.
    pub metas: Vec<ClauseMeta>,
}

impl TotalReport {
    /// Total opaque premises in the combined set.
    pub fn opaque_total(&self) -> usize {
        self.opaque_tags.values().sum()
    }
}

/// The conclusion's relation tag (`st$c$rel.<tag>` at the head of its spine).
fn concl_tag(t: &Term) -> Option<String> {
    let mut cur = t;
    loop {
        let (f, _) = cur.as_app()?;
        match f.as_app() {
            Some((h, c)) => {
                if h.as_free().map(|v| v.name()) == Some("st$app")
                    && let Some(v) = c.as_free()
                    && let Some(tag) = v.name().strip_prefix("st$c$rel.")
                {
                    return Some(tag.to_owned());
                }
                cur = f;
            }
            None => return None,
        }
    }
}

/// Every `Rel` in `defs`, descending into `Rec` groups (flattened order —
/// must match `spec_rule_clauses`'s traversal).
fn relations(defs: &[SpecTecDef]) -> Vec<&SpecTecDef> {
    let mut out = Vec::new();
    fn go<'a>(d: &'a SpecTecDef, out: &mut Vec<&'a SpecTecDef>) {
        match d {
            SpecTecDef::Rel { .. } => out.push(d),
            SpecTecDef::Rec { ds } => ds.iter().for_each(|x| go(x, out)),
            _ => {}
        }
    }
    defs.iter().for_each(|d| go(d, &mut out));
    out
}

/// **The total load**: one combined clause list over `defs` (see the
/// module docs for content and order), with the [`TotalReport`].
pub fn total_spec_clauses(defs: &[SpecTecDef]) -> Result<(Vec<Clause>, TotalReport)> {
    let cat = CaseCatalogue::new(defs);
    let mut fl = Flattener::new(&cat);

    // Leg 1: relation rules (+ star aux, collected separately).
    let (rule_clauses, star_aux, rules_census) = spec_rule_clauses(defs, &mut fl);
    // R3-F5: no two Iter sites may share a star relation (a tag collision
    // would merge their aux clauses and over-approximate both sites).
    super::star::assert_unique_star_tags(&star_aux);
    // Leg 2: Dec graph relations, same flattener (shared ev pool → `ev.cat`
    // etc. are emitted at most once across both legs).
    let (dec_clauses, dec_census) = spec_fn_clauses(defs, &mut fl)?;
    // Leg 3: the integer-builtin defining clauses (Side-only, no ev deps).
    let (builtin, builtin_report) = builtin_clauses()?;
    // Leg 4: the evaluator pool, drained once.
    let ev_clauses = fl.drain_ev_clauses();
    let neq_pairs = fl.neq_pairs();

    // Rule metas (relation/rule names in the exact lowering order; the
    // metavar order comes from the lowered clause itself).
    let mut metas = Vec::new();
    for def in relations(defs) {
        let SpecTecDef::Rel { x, rules, .. } = def else {
            unreachable!()
        };
        for rule in rules {
            let SpecTecRule::Rule { x: name, .. } = rule;
            let idx = metas.len();
            metas.push(ClauseMeta {
                relation: x.clone(),
                name: name.clone(),
                metavars: rule_clauses[idx].metavars.clone(),
            });
        }
    }
    // Hard assert: the metas walk (spec order) and the lowering (same
    // traversal) must agree exactly — a mismatch means clause addressing is
    // corrupt for every subsequent index.
    assert_eq!(metas.len(), rule_clauses.len(), "ClauseMeta addressing");
    for c in star_aux
        .iter()
        .chain(&dec_clauses)
        .chain(&builtin)
        .chain(&ev_clauses)
    {
        metas.push(ClauseMeta {
            relation: concl_tag(&c.concl).unwrap_or_default(),
            name: String::new(),
            metavars: c.metavars.clone(),
        });
    }

    // Assemble in the contract order.
    let (n_rule_clauses, n_star_aux, n_dec_clauses, n_builtin_clauses, n_evaluator_clauses) = (
        rule_clauses.len(),
        star_aux.len(),
        dec_clauses.len(),
        builtin.len(),
        ev_clauses.len(),
    );
    let mut clauses = rule_clauses;
    clauses.extend(star_aux);
    clauses.extend(dec_clauses);
    clauses.extend(builtin);
    clauses.extend(ev_clauses);

    // The honest-residue census: every opaque premise in the final list.
    let mut opaque_tags = BTreeMap::new();
    for c in &clauses {
        for p in &c.prems {
            if let LowerPrem::Judgement(j) = p
                && let Some(reason) = opaque_reason(j)
            {
                *opaque_tags.entry(reason).or_default() += 1;
            }
        }
    }

    let report = TotalReport {
        rules: rules_census,
        decs: dec_census,
        n_rule_clauses,
        n_star_aux,
        n_dec_clauses,
        n_builtin_clauses,
        builtins: builtin_report,
        n_evaluator_clauses,
        neq_pairs,
        total_clauses: clauses.len(),
        opaque_tags,
        metas,
    };
    Ok((clauses, report))
}

/// [`total_spec_clauses`] packaged as a memoized [`RuleSet`] (clause `i` =
/// combined clause `i` — the order contract above).
pub fn total_rule_set(defs: &[SpecTecDef]) -> Result<(RuleSet<'static>, TotalReport)> {
    let (clauses, report) = total_spec_clauses(defs)?;
    Ok((rule_set_of(clauses), report))
}

/// Run `f` on a thread with a 64 MiB stack and propagate its result (and
/// panics).
///
/// The combined set's `Closed_L` is a right-nested conjunction of ~2500
/// clauses and kernel term operations recurse structurally, so laying it out
/// or deriving against it needs ~16 MiB of stack in debug builds — more than
/// default test-thread stacks. Drive whole-spec work through this until the
/// kernel walks go iterative (the known term-arena / verified-WASM
/// construction direction; see the design note's scale risk).
pub fn with_total_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    let handle = std::thread::Builder::new()
        .name("wasm-total-load".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn total-load thread");
    match handle.join() {
        Ok(v) => v,
        Err(e) => std::panic::resume_unwind(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init::ext::TermExt;
    use crate::metalogic::{self, Premise};
    use crate::wasm::encode::{app, con, encode_exp, metavar_name, phi};
    use crate::wasm::lower::flatten::prove_side;
    use crate::wasm::spec::wasm_spec;
    use covalence_core::Var;
    use covalence_core::subst::subst_free;
    use covalence_hol_eval::EvalThm as Thm;
    use covalence_spectec::ast::{MixOp, SpecTecExp};

    fn case(name: &str, payload: SpecTecExp) -> SpecTecExp {
        SpecTecExp::Case {
            op: MixOp::new(vec![name.to_string()]),
            e1: Box::new(payload),
        }
    }
    fn leaf(name: &str) -> SpecTecExp {
        case(name, SpecTecExp::Tup { es: vec![] })
    }

    /// The exact term `all_elim` instantiation produces: substitute `args`
    /// for the clause's metavariables (in order) in its conclusion.
    fn instantiate(c: &Clause, args: &[Term]) -> Term {
        assert_eq!(c.metavars.len(), args.len(), "arity");
        let mut t = c.concl.clone();
        for (mv, a) in c.metavars.iter().zip(args) {
            t = subst_free(&t, &Var::new(metavar_name(mv), phi()), a);
        }
        t
    }

    fn assert_genuine(thm: &Thm) {
        assert!(thm.hyps().is_empty(), "hypothesis-free");
    }

    /// If a clause's conclusion is `ev.neq(case.<k1>(%p), case.<k2>(%q))`,
    /// return `(k1, k2)`.
    fn neq_pair_keys(c: &Clause) -> Option<(String, String)> {
        let case_key = |t: &Term| -> Option<String> {
            let (f, _payload) = t.as_app()?;
            let (h, con) = f.as_app()?;
            if h.as_free()?.name() != "st$app" {
                return None;
            }
            con.as_free()?
                .name()
                .strip_prefix("st$c$case.")
                .map(str::to_owned)
        };
        // concl = app(rel.ev.neq, app(app(evargs.1, arg), result))
        let (_, spine) = c.concl.as_app()?;
        let (f, result) = spine.as_app()?;
        let (_, arg_spine) = f.as_app()?;
        let (_, arg) = arg_spine.as_app()?;
        Some((case_key(arg)?, case_key(result)?))
    }

    /// **The cross-leg end-to-end acceptance demos** (design note: the
    /// combined set is a concrete API): three real spec rules fire on the
    /// full ~1800-clause combined set, each crossing leg boundaries —
    ///
    /// - (a) `Nondefaultable` — an `If` condition calling the
    ///   equation-defined Dec `$default_`, discharged through its `fn.*`
    ///   graph clause (the `REF ht` = `eps` equation) plus a refl side;
    /// - (b) `Step_pure/ref.is_null-false` — a real **Else** rule: the
    ///   negated sibling guard `ref =/= REF.NULL_ADDR` fires through an
    ///   on-demand `ev.neq` tag-pair clause;
    /// - (c) `Resulttype_ok` — a real **Iter(Rule)** premise fires through
    ///   its synthesized star relation on a 2-element result type, with the
    ///   element judgements built by the `Valtype_ok/num ∘ Numtype_ok`
    ///   chain (three relations + the star, one derivation).
    ///
    /// Wall-times are printed (cache-cold first derive pays the one-time
    /// layout; the rest are warm) — the scale smoke test.
    #[test]
    fn combined_set_cross_leg_derivations() {
        with_total_stack(|| {
            let t0 = std::time::Instant::now();
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();
            assert_eq!(n, report.total_clauses);
            println!("combined set built + kernel-checked in {:?}", t0.elapsed());

            let find = |rel: &str, name: &str| {
                report
                    .metas
                    .iter()
                    .position(|m| m.relation == rel && m.name == name)
                    .unwrap_or_else(|| panic!("no clause for {rel}/{name}"))
            };
            let derive = |idx: usize, args: &[Term], prems: Vec<Premise>| {
                metalogic::derive_mixed(&rs, idx, n, args, prems)
            };
            let check = |thm: &Thm, idx: usize, args: &[Term]| {
                assert_genuine(thm);
                let expected =
                    metalogic::derivable(&rs, &instantiate(&clauses[idx], args)).unwrap();
                assert_eq!(thm.concl(), &expected, "clause {idx} conclusion");
            };

            // ------------------------------------------------------------
            // (a) Nondefaultable(REF ANY): If-condition calls $default_.
            //     `⊢ t NONDEFAULTABLE -- if $default_(t) = eps` — premises
            //     [fn.default_(t, r), Side(r = eps)]; the Dec's `REF ht`
            //     clause (RHS eps) discharges the graph premise.
            // ------------------------------------------------------------
            let t_a = std::time::Instant::now();
            // t := REF (no NULL) ANY — encode via the shared encoder.
            let ref_any = case(
                "REF",
                SpecTecExp::Tup {
                    es: vec![SpecTecExp::Opt { eo: None }, leaf("ANY")],
                },
            );
            let ref_enc = encode_exp(&ref_any).unwrap();
            let eps = con("opt.none");
            // The fn.default_ clause whose result is eps (metavars [ht]).
            let expected_dec =
                super::super::fn_graph("default_", &[ref_enc.clone()], &eps).unwrap();
            let any_enc = encode_exp(&leaf("ANY")).unwrap();
            let dec_idx = (0..n)
                .filter(|i| report.metas[*i].relation == "fn.default_")
                .find(|i| {
                    report.metas[*i].metavars.len() == 1
                        && instantiate(&clauses[*i], &[any_enc.clone()]) == expected_dec
                })
                .expect("the `default_(REF ht) = eps` graph clause");
            let d_dec = derive(dec_idx, &[any_enc.clone()], vec![]).unwrap();
            check(&d_dec, dec_idx, &[any_enc]);

            let nd = find("Nondefaultable", "");
            let side = prove_side(&eps.clone().equals(eps.clone()).unwrap()).unwrap();
            let args = [ref_enc, eps];
            let d_nd = derive(
                nd,
                &args,
                vec![Premise::Derivation(d_dec), Premise::Side(side)],
            )
            .unwrap();
            check(&d_nd, nd, &args);
            println!(
                "(a) Nondefaultable(REF ANY) via fn.default_: {:?}",
                t_a.elapsed()
            );

            // ------------------------------------------------------------
            // (b) Step_pure/ref.is_null-false: a real Else rule. Its single
            //     premise is the negated sibling guard `ref =/= REF.NULL_ADDR`
            //     as an ev.neq judgement; fire it at ref := REF.FUNC_ADDR-
            //     style value through the tag-pair clause.
            // ------------------------------------------------------------
            let t_b = std::time::Instant::now();
            let pairs: Vec<(usize, String)> = (0..n)
                .filter(|i| report.metas[*i].relation == "ev.neq")
                .filter_map(|i| {
                    let (k1, k2) = neq_pair_keys(&clauses[i])?;
                    (k2 == "REF.NULL_ADDR").then_some((i, k1))
                })
                .collect();
            let (pair_idx, k1) = pairs
                .iter()
                .find(|(_, k)| k == "REF.FUNC_ADDR")
                .or_else(|| pairs.first())
                .cloned()
                .expect("an ev.neq pair clause against REF.NULL_ADDR");
            let ref_val = app(con(format!("case.{k1}")), con("tup")).unwrap();
            let null_payload = con("tup"); // REF.NULL_ADDR's payload is the unit tup
            let pair_args = [con("tup"), null_payload];
            let d_neq = derive(pair_idx, &pair_args, vec![]).unwrap();
            check(&d_neq, pair_idx, &pair_args);

            // The rule's `ref` metavariable is sub-only (`ref <: instr`), so
            // the clause carries an `ev.sort.ref` guard: derive membership at
            // the `case.<k1>` head clause (payload ∀-open).
            let sort_idx = (0..n)
                .filter(|i| report.metas[*i].relation == "ev.sort.ref")
                .find(|i| {
                    let c = &clauses[*i];
                    c.metavars.len() == 1
                        && instantiate(c, &[con("tup")])
                            == crate::wasm::lower::evalrel::ev_graph("sort.ref", &[], &ref_val)
                                .unwrap()
                })
                .expect("the ev.sort.ref clause for the chosen ref head");
            let d_sort = derive(sort_idx, &[con("tup")], vec![]).unwrap();
            check(&d_sort, sort_idx, &[con("tup")]);

            let isnull = find("Step_pure", "ref.is_null-false");
            let args = [ref_val];
            let d_isnull = derive(
                isnull,
                &args,
                vec![Premise::Derivation(d_neq), Premise::Derivation(d_sort)],
            )
            .unwrap();
            check(&d_isnull, isnull, &args);
            println!(
                "(b) Step_pure/ref.is_null-false (Else) via ev.neq.{k1}.REF.NULL_ADDR: {:?}",
                t_b.elapsed()
            );

            // ------------------------------------------------------------
            // (c) Resulttype_ok on [I32, I32]: the Iter(Rule) premise fires
            //     through its star relation; elements are genuine
            //     Valtype_ok/num ∘ Numtype_ok derivations.
            // ------------------------------------------------------------
            let t_c = std::time::Instant::now();
            let ctx = encode_exp(&leaf("C")).unwrap();
            let i32e = encode_exp(&leaf("I32")).unwrap();

            let numtype_ok = find("Numtype_ok", "");
            let base_args = [ctx.clone(), i32e.clone()];
            let d_num = derive(numtype_ok, &base_args, vec![]).unwrap();
            check(&d_num, numtype_ok, &base_args);
            // `Valtype_ok/num`'s `numtype` is sub-only (`numtype <: valtype`)
            // — its clause carries an exact `ev.sort.numtype` guard; the I32
            // membership clause is ground (nullary case, no metavars).
            let sort_num_idx = (0..n)
                .filter(|i| report.metas[*i].relation == "ev.sort.numtype")
                .find(|i| {
                    clauses[*i].metavars.is_empty()
                        && clauses[*i].concl
                            == crate::wasm::lower::evalrel::ev_graph("sort.numtype", &[], &i32e)
                                .unwrap()
                })
                .expect("the ev.sort.numtype clause for I32");
            let d_sort_num = derive(sort_num_idx, &[], vec![]).unwrap();
            check(&d_sort_num, sort_num_idx, &[]);
            let valtype_num = find("Valtype_ok", "num");
            let d_vt = derive(
                valtype_num,
                &[ctx.clone(), i32e.clone()],
                vec![Premise::Derivation(d_num), Premise::Derivation(d_sort_num)],
            )
            .unwrap();
            check(&d_vt, valtype_num, &[ctx.clone(), i32e.clone()]);

            // Star chain: nil, then two snocs consuming the element proof.
            let rt = find("Resulttype_ok", "");
            let star_tag = format!("star.Resulttype_ok.{}.0", report.metas[rt].name);
            let star_idxs: Vec<usize> = (0..n)
                .filter(|i| report.metas[*i].relation == star_tag)
                .collect();
            let (nil_idx, snoc_idx) = (star_idxs[0], star_idxs[1]);
            let d_star0 = derive(nil_idx, &[ctx.clone()], vec![]).unwrap();
            check(&d_star0, nil_idx, &[ctx.clone()]);
            let l0 = con("list");
            let snoc1_args = [ctx.clone(), l0.clone(), i32e.clone()];
            let d_star1 = derive(
                snoc_idx,
                &snoc1_args,
                vec![
                    Premise::Derivation(d_vt.clone()),
                    Premise::Derivation(d_star0),
                ],
            )
            .unwrap();
            check(&d_star1, snoc_idx, &snoc1_args);
            let l1 = app(l0, i32e.clone()).unwrap();
            let snoc2_args = [ctx.clone(), l1.clone(), i32e.clone()];
            let d_star2 = derive(
                snoc_idx,
                &snoc2_args,
                vec![Premise::Derivation(d_vt), Premise::Derivation(d_star1)],
            )
            .unwrap();
            check(&d_star2, snoc_idx, &snoc2_args);
            let l2 = app(l1, i32e).unwrap();

            let main_args = [ctx, l2];
            let d_rt = derive(rt, &main_args, vec![Premise::Derivation(d_star2)]).unwrap();
            check(&d_rt, rt, &main_args);
            println!(
                "(c) Resulttype_ok([I32, I32]) via its star relation: {:?}",
                t_c.elapsed()
            );
        })
    }

    /// **The const-fold payoff demo** (the integer-builtin leg,
    /// [`super::super::builtins`]): real `Step_pure/binop-val` reduction steps
    /// fire end-to-end, hypothesis-free, on the full combined set —
    ///
    /// - `[CONST I32 2, CONST I32 3, BINOP I32 ADD] ~> [CONST I32 5]`
    ///   through `fn.size ∘ fn.sizenn ∘ fn.iadd_` (the spec's own `iadd_`
    ///   equation, its `(2 + 3) mod 2^32` side kernel-computed) `∘
    ///   fn.binop_ ∘ ev.mem`;
    /// - `[CONST I32 5, CONST I32 3, BINOP I32 SUB] ~> [CONST I32 2]`
    ///   through the **builtin leg's** `fn.isub_` defining clause (the
    ///   spec's `isub_` equation concludes a value-dead `Cvt` spine, so this
    ///   chain was underivable before the leg landed);
    ///
    /// plus the **refusals**: the wrong results (`6` for the ADD, `3` for
    /// the SUB) fail — their defining `Side` antecedents are kernel-refuted,
    /// and no other clause of the graph can conclude them (clause-level
    /// exhaustive refusal is the builtin module's oracle tests).
    #[test]
    fn binop_const_fold_fires_and_refuses() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();

            let derive = |idx: usize, args: &[Term], prems: Vec<Premise>| {
                metalogic::derive_mixed(&rs, idx, n, args, prems)
                    .unwrap_or_else(|e| panic!("clause {idx} at {args:?}: {e}"))
            };
            let check = |thm: &Thm, idx: usize, args: &[Term]| {
                assert_genuine(thm);
                let expected =
                    metalogic::derivable(&rs, &instantiate(&clauses[idx], args)).unwrap();
                assert_eq!(thm.concl(), &expected, "clause {idx} conclusion");
            };
            let nth_of = |rel: &str, k: usize| {
                (0..n)
                    .filter(|i| report.metas[*i].relation == rel)
                    .nth(k)
                    .unwrap_or_else(|| panic!("no clause {k} of {rel}"))
            };
            let find_rule = |rel: &str, name: &str| {
                report
                    .metas
                    .iter()
                    .position(|m| m.relation == rel && m.name == name)
                    .unwrap_or_else(|| panic!("no clause for {rel}/{name}"))
            };
            // The clause of `rel` whose conclusion instantiates to `expected`
            // at `args`.
            let find_at = |rel: &str, args: &[Term], expected: &Term| {
                (0..n)
                    .filter(|i| report.metas[*i].relation == rel)
                    .find(|i| {
                        clauses[*i].metavars.len() == args.len()
                            && instantiate(&clauses[*i], args) == *expected
                    })
                    .unwrap_or_else(|| panic!("no {rel} clause concluding {expected:?}"))
            };
            // The `k`-th premise of clause `idx`, instantiated at `args`
            // (Side premises only — the prove_side obligation).
            let side_at = |idx: usize, args: &[Term], k: usize| {
                let c = &clauses[idx];
                let LowerPrem::Side(s) = &c.prems[k] else {
                    panic!("premise {k} of clause {idx} is not a Side")
                };
                let mut t = s.clone();
                for (mv, a) in c.metavars.iter().zip(args) {
                    t = subst_free(&t, &Var::new(metavar_name(mv), phi()), a);
                }
                t
            };

            let a = |x: Term, y: Term| app(x, y).unwrap();
            let nat = |k: u64| covalence_hol_eval::mk_nat(k);
            let i32t = a(con("case.I32"), con("tup"));
            let addop = a(con("case.ADD"), con("tup"));
            let subop = a(con("case.SUB"), con("tup"));
            let andop = a(con("case.AND"), con("tup"));
            let w32 = a(con("num.nat"), nat(32));
            let payload = |k: u64| a(con("tup"), a(con("num.nat"), nat(k)));
            let iv = |k: u64| a(con("case.%"), payload(k));
            let fng =
                |f: &str, args: &[Term], r: &Term| super::super::fn_graph(f, args, r).unwrap();

            // -- fn.size(I32) = 32 (ground) → fn.sizenn(I32) = 32.
            let size_idx = find_at("fn.size", &[], &fng("size", &[i32t.clone()], &w32));
            let d_size = derive(size_idx, &[], vec![]);
            let sizenn_idx = nth_of("fn.sizenn", 0);
            let sizenn_args = [i32t.clone(), w32.clone()];
            let d_sizenn = derive(sizenn_idx, &sizenn_args, vec![Premise::Derivation(d_size)]);
            check(&d_sizenn, sizenn_idx, &sizenn_args);

            // ============================================================
            // (a) ADD: fn.iadd_(32, %(2), %(3), %(5)) via the spec clause
            //     (metavars [N, i_1, i_2, uncase₁, proj₁, uncase₂, proj₂, r];
            //     numeric currency: bare numerals).
            // ============================================================
            let t_a = std::time::Instant::now();
            let iadd_idx = nth_of("fn.iadd_", 0);
            assert_eq!(
                (0..n)
                    .filter(|i| report.metas[*i].relation == "fn.iadd_")
                    .count(),
                1,
                "fn.iadd_ has exactly one clause (refusal is complete)"
            );
            let iadd_args = [
                nat(32),
                iv(2),
                iv(3),
                payload(2),
                nat(2),
                payload(3),
                nat(3),
                nat(5),
            ];
            let d_unc2 = derive(nth_of("ev.uncase.%", 0), &[payload(2)], vec![]);
            let d_prj2 = derive(nth_of("ev.proj.0", 0), &[a(con("num.nat"), nat(2))], vec![]);
            let d_unc3 = derive(nth_of("ev.uncase.%", 0), &[payload(3)], vec![]);
            let d_prj3 = derive(nth_of("ev.proj.0", 0), &[a(con("num.nat"), nat(3))], vec![]);
            // The defining side, kernel-computed: 5 = (2 + 3) mod 2^32.
            let side_add = prove_side(&side_at(iadd_idx, &iadd_args, 4)).unwrap();
            let d_iadd = derive(
                iadd_idx,
                &iadd_args,
                vec![
                    Premise::Derivation(d_unc2.clone()),
                    Premise::Derivation(d_prj2.clone()),
                    Premise::Derivation(d_unc3),
                    Premise::Derivation(d_prj3.clone()),
                    Premise::Side(side_add),
                ],
            );
            check(&d_iadd, iadd_idx, &iadd_args);
            // REFUSAL: 6 ≠ (2 + 3) mod 2^32 — the side is kernel-refuted.
            let mut wrong = iadd_args.clone();
            wrong[7] = nat(6);
            assert!(
                prove_side(&side_at(iadd_idx, &wrong, 4)).is_err(),
                "iadd_ side must refuse r = 6"
            );

            // fn.binop_(I32, ADD, %(2), %(3), [%(5)]) — the per-case ADD/I32
            // graph clause (metavars [i_1, i_2, size, result]).
            let binop_add = find_at(
                "fn.binop_",
                &[iv(2), iv(3), w32.clone(), iv(5)],
                &fng(
                    "binop_",
                    &[i32t.clone(), addop.clone(), iv(2), iv(3)],
                    &a(con("list"), iv(5)),
                ),
            );
            let add_args = [iv(2), iv(3), w32.clone(), iv(5)];
            let d_badd = derive(
                binop_add,
                &add_args,
                vec![
                    Premise::Derivation(d_sizenn.clone()),
                    Premise::Derivation(d_iadd),
                ],
            );
            check(&d_badd, binop_add, &add_args);

            // ev.mem(%(5), [%(5)]) and the rule itself.
            let mem_idx = nth_of("ev.mem", 0);
            let d_mem5 = derive(mem_idx, &[iv(5), con("list")], vec![]);
            let rule_idx = find_rule("Step_pure", "binop-val");
            let rule_args = [
                i32t.clone(),
                iv(2),
                iv(3),
                addop,
                iv(5),
                a(con("list"), iv(5)),
            ];
            let d_add = derive(
                rule_idx,
                &rule_args,
                vec![Premise::Derivation(d_badd), Premise::Derivation(d_mem5)],
            );
            check(&d_add, rule_idx, &rule_args);
            println!(
                "(a) [CONST I32 2, CONST I32 3, BINOP I32 ADD] ~> [CONST I32 5]: {:?}",
                t_a.elapsed()
            );

            // ============================================================
            // (b) SUB through the BUILTIN leg: fn.isub_(32, %(5), %(3), %(2))
            //     — the spec's isub_ clause concludes a Cvt spine, so only
            //     the builtin defining clause can produce the value.
            // ============================================================
            let t_b = std::time::Instant::now();
            let isub_target = fng("isub_", &[w32.clone(), iv(5), iv(3)], &iv(2));
            let isub_idx = find_at("fn.isub_", &[nat(5), nat(3), nat(2)], &isub_target);
            let isub_args = [nat(5), nat(3), nat(2)];
            let sides: Vec<Premise> = (0..clauses[isub_idx].prems.len())
                .map(|k| Premise::Side(prove_side(&side_at(isub_idx, &isub_args, k)).unwrap()))
                .collect();
            let d_isub = derive(isub_idx, &isub_args, sides);
            check(&d_isub, isub_idx, &isub_args);
            // REFUSAL: r = 3 — the defining side (2 = (5 + 2^32 − 3) mod 2^32
            // becomes 3 = …) is kernel-refuted.
            let wrong = [nat(5), nat(3), nat(3)];
            assert!(
                prove_side(&side_at(isub_idx, &wrong, 2)).is_err(),
                "isub_ side must refuse r = 3"
            );

            let binop_sub = find_at(
                "fn.binop_",
                &[iv(5), iv(3), w32.clone(), iv(2)],
                &fng(
                    "binop_",
                    &[i32t.clone(), subop.clone(), iv(5), iv(3)],
                    &a(con("list"), iv(2)),
                ),
            );
            let sub_args = [iv(5), iv(3), w32.clone(), iv(2)];
            let d_bsub = derive(
                binop_sub,
                &sub_args,
                vec![
                    Premise::Derivation(d_sizenn.clone()),
                    Premise::Derivation(d_isub),
                ],
            );
            check(&d_bsub, binop_sub, &sub_args);

            let d_mem2 = derive(mem_idx, &[iv(2), con("list")], vec![]);
            let rule_args = [
                i32t.clone(),
                iv(5),
                iv(3),
                subop,
                iv(2),
                a(con("list"), iv(2)),
            ];
            let d_sub = derive(
                rule_idx,
                &rule_args,
                vec![Premise::Derivation(d_bsub), Premise::Derivation(d_mem2)],
            );
            check(&d_sub, rule_idx, &rule_args);
            println!(
                "(b) [CONST I32 5, CONST I32 3, BINOP I32 SUB] ~> [CONST I32 2] \
                (builtin isub_): {:?}",
                t_b.elapsed()
            );

            // ============================================================
            // (c) AND through the exact bit-structure builtin clause.
            //     This is a genuine full combined-set execution, not just a
            //     standalone graph check: fn.iand_ feeds fn.binop_, whose
            //     result discharges Step_pure/binop-val.
            // ============================================================
            let t_c = std::time::Instant::now();
            let expected = 0x00f0u64;
            let iand_target = fng(
                "iand_",
                &[w32.clone(), iv(0x0ff0), iv(0x00ff)],
                &iv(expected),
            );
            let iand_args = [nat(0x0ff0), nat(0x00ff), nat(expected)];
            let iand_idx = find_at("fn.iand_", &iand_args, &iand_target);
            let sides: Vec<Premise> = (0..clauses[iand_idx].prems.len())
                .map(|k| Premise::Side(prove_side(&side_at(iand_idx, &iand_args, k)).unwrap()))
                .collect();
            let d_iand = derive(iand_idx, &iand_args, sides);
            check(&d_iand, iand_idx, &iand_args);
            let wrong = [nat(0x0ff0), nat(0x00ff), nat(expected + 1)];
            assert!(
                prove_side(&side_at(iand_idx, &wrong, 3)).is_err(),
                "iand_ defining equality must refuse the wrong result"
            );

            let binop_and = find_at(
                "fn.binop_",
                &[iv(0x0ff0), iv(0x00ff), w32.clone(), iv(expected)],
                &fng(
                    "binop_",
                    &[i32t.clone(), andop.clone(), iv(0x0ff0), iv(0x00ff)],
                    &a(con("list"), iv(expected)),
                ),
            );
            let and_args = [iv(0x0ff0), iv(0x00ff), w32, iv(expected)];
            let d_band = derive(
                binop_and,
                &and_args,
                vec![Premise::Derivation(d_sizenn), Premise::Derivation(d_iand)],
            );
            check(&d_band, binop_and, &and_args);
            let d_mem = derive(mem_idx, &[iv(expected), con("list")], vec![]);
            let rule_args = [
                i32t,
                iv(0x0ff0),
                iv(0x00ff),
                andop,
                iv(expected),
                a(con("list"), iv(expected)),
            ];
            let d_and = derive(
                rule_idx,
                &rule_args,
                vec![Premise::Derivation(d_band), Premise::Derivation(d_mem)],
            );
            check(&d_and, rule_idx, &rule_args);
            println!(
                "(c) [CONST I32 0x0ff0, CONST I32 0x00ff, BINOP I32 AND] \
                 ~> [CONST I32 0x00f0] (builtin iand_): {:?}",
                t_c.elapsed()
            );
        })
    }

    /// **The store-accessor / `table.fill`-family demo** (Wave-D Fix 2
    /// acceptance): `Step_read/table.fill-zero` — a real **Else** rule whose
    /// negated sibling guard reads the store through the accessor chain
    /// `$table(z, x).REFS` — derives end-to-end, hypothesis-free, on the
    /// combined set. This was impossible before result-position flattening:
    /// `fn.table`'s conclusion was a coarse `idx`/`dot` spine, so the
    /// downstream `ev.dot.REFS`/`ev.len` premises could never fire. Now
    /// `fn.table(z, x, r)` constrains `r` through `fn.sof`/`fn.fof` +
    /// `ev.dot`/`ev.idx` premises, and the whole chain grounds out on a
    /// concrete two-struct store. The rule also exercises Fix 1: its `at` and
    /// `val` metavariables are sub-only (`addrtype <: numtype`,
    /// `val <: instr`), discharged through `ev.sort.*` guard clauses.
    #[test]
    fn table_fill_zero_fires_through_store_accessors() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();

            let derive = |idx: usize, args: &[Term], prems: Vec<Premise>| {
                metalogic::derive_mixed(&rs, idx, n, args, prems)
                    .unwrap_or_else(|e| panic!("clause {idx} at {args:?}: {e}"))
            };
            let check = |thm: &Thm, idx: usize, args: &[Term]| {
                assert_genuine(thm);
                let expected =
                    metalogic::derivable(&rs, &instantiate(&clauses[idx], args)).unwrap();
                assert_eq!(thm.concl(), &expected, "clause {idx} conclusion");
            };
            // The k-th clause of an aux relation (emission order: e.g.
            // `ev.dot.*` = [hit, skip], `ev.idx` = [last, skip],
            // `ev.len` = [base, step], `ev.proj.0` = arity 1..).
            let nth_of = |rel: &str, k: usize| {
                (0..n)
                    .filter(|i| report.metas[*i].relation == rel)
                    .nth(k)
                    .unwrap_or_else(|| panic!("no clause {k} of {rel}"))
            };
            let find = |rel: &str, name: &str| {
                report
                    .metas
                    .iter()
                    .position(|m| m.relation == rel && m.name == name)
                    .unwrap_or_else(|| panic!("no clause for {rel}/{name}"))
            };

            // -- Ground store: z = (store; frame) with one empty-REFS table.
            let a = |x: Term, y: Term| app(x, y).unwrap();
            let w0 = a(con("num.nat"), covalence_hol_eval::mk_nat(0u64)); // ⌜0⌝ wrapped
            let i32e = a(con("case.I32"), con("tup"));
            let idx0 = a(con("case.%"), a(con("tup"), w0.clone())); // x = i = (0)
            let val = a(
                con("case.CONST"),
                a(a(con("tup"), i32e.clone()), idx0.clone()),
            ); // CONST I32 (0) — any well-headed val works for the guard
            let ti = a(con("struct"), a(con("field.REFS"), con("list"))); // REFS = []
            let store = a(
                con("struct"),
                a(con("field.TABLES"), a(con("list"), ti.clone())),
            );
            let minst = a(
                con("struct"),
                a(con("field.TABLES"), a(con("list"), w0.clone())),
            );
            let frame = a(con("struct"), a(con("field.MODULE"), minst.clone()));
            let z = a(
                con("case.%;%"),
                a(a(con("tup"), store.clone()), frame.clone()),
            );

            // -- The accessor chain: fn.table(z, (0), ti).
            let d_store = derive(
                nth_of("fn.store", 0),
                &[store.clone(), frame.clone()],
                vec![],
            );
            let d_frame = derive(
                nth_of("fn.frame", 0),
                &[store.clone(), frame.clone()],
                vec![],
            );
            let d_sof = derive(
                nth_of("fn.sof", 0),
                &[z.clone(), store.clone()],
                vec![Premise::Derivation(d_store)],
            );
            let d_fof = derive(
                nth_of("fn.fof", 0),
                &[z.clone(), frame.clone()],
                vec![Premise::Derivation(d_frame)],
            );
            // ev.dot hits (first clause of each family).
            let tables_s = a(con("list"), ti.clone());
            let tables_m = a(con("list"), w0.clone());
            let d_dot_ts = derive(
                nth_of("ev.dot.TABLES", 0),
                &[con("struct"), tables_s.clone()],
                vec![],
            );
            let d_dot_mod = derive(
                nth_of("ev.dot.MODULE", 0),
                &[con("struct"), minst.clone()],
                vec![],
            );
            let d_dot_tm = derive(
                nth_of("ev.dot.TABLES", 0),
                &[con("struct"), tables_m.clone()],
                vec![],
            );
            // idx wrapper: uncase + proj.
            let payload = a(con("tup"), w0.clone());
            let d_uncase = derive(nth_of("ev.uncase.%", 0), &[payload.clone()], vec![]);
            let d_proj = derive(nth_of("ev.proj.0", 0), &[w0.clone()], vec![]);
            // ev.len base + the two ev.idx lookups (index 0 of 1-element lists).
            let d_len0 = derive(nth_of("ev.len", 0), &[], vec![]);
            let zero = covalence_hol_eval::mk_nat(0u64);
            let d_idx_m = derive(
                nth_of("ev.idx", 0),
                &[con("list"), w0.clone(), zero.clone()],
                vec![Premise::Derivation(d_len0.clone())],
            );
            let d_idx_s = derive(
                nth_of("ev.idx", 0),
                &[con("list"), ti.clone(), zero.clone()],
                vec![Premise::Derivation(d_len0.clone())],
            );
            let table_idx = nth_of("fn.table", 0);
            let table_args = [
                z.clone(),
                idx0.clone(),
                store.clone(),
                frame.clone(),
                tables_s.clone(),
                minst.clone(),
                tables_m.clone(),
                payload.clone(),
                w0.clone(),
                w0.clone(),
                ti.clone(),
            ];
            let d_table = derive(
                table_idx,
                &table_args,
                vec![
                    Premise::Derivation(d_sof),
                    Premise::Derivation(d_fof),
                    Premise::Derivation(d_dot_ts),
                    Premise::Derivation(d_dot_mod),
                    Premise::Derivation(d_dot_tm),
                    Premise::Derivation(d_uncase.clone()),
                    Premise::Derivation(d_proj.clone()),
                    Premise::Derivation(d_idx_m),
                    Premise::Derivation(d_idx_s),
                ],
            );
            check(&d_table, table_idx, &table_args);
            println!("fn.table(z, (0)) = ti fires through the accessor chain");

            // -- ti.REFS = [] and |[]| = 0.
            let d_refs = derive(
                nth_of("ev.dot.REFS", 0),
                &[con("struct"), con("list")],
                vec![],
            );

            // -- Sort guards: at := I32 (exact nullary clause), val (CONST head).
            let sort_at = (0..n)
                .filter(|i| report.metas[*i].relation == "ev.sort.addrtype")
                .find(|i| {
                    clauses[*i].metavars.is_empty()
                        && clauses[*i].concl
                            == crate::wasm::lower::evalrel::ev_graph("sort.addrtype", &[], &i32e)
                                .unwrap()
                })
                .expect("ev.sort.addrtype I32 clause");
            let d_sort_at = derive(sort_at, &[], vec![]);
            let val_payload = a(a(con("tup"), i32e.clone()), idx0.clone());
            let sort_val = (0..n)
                .filter(|i| report.metas[*i].relation == "ev.sort.val")
                .find(|i| {
                    clauses[*i].metavars.len() == 1
                        && instantiate(&clauses[*i], &[val_payload.clone()])
                            == crate::wasm::lower::evalrel::ev_graph("sort.val", &[], &val).unwrap()
                })
                .expect("ev.sort.val CONST clause");
            let d_sort_val = derive(sort_val, &[val_payload.clone()], vec![]);

            // -- Sides: 0 + 0 ≤ 0 (the negated oob guard) and n = 0.
            let add00 = crate::init::nat::nat_add()
                .apply(zero.clone())
                .unwrap()
                .apply(zero.clone())
                .unwrap();
            let le = crate::init::nat::nat_le()
                .apply(add00)
                .unwrap()
                .apply(zero.clone())
                .unwrap();
            let side_le = prove_side(&le).unwrap();
            let side_n0 = prove_side(&zero.clone().equals(zero.clone()).unwrap()).unwrap();

            // -- The rule itself.
            let rule_idx = find("Step_read", "table.fill-zero");
            let rule_args = [
                z,
                i32e,
                idx0.clone(),
                val,
                zero.clone(),
                idx0,
                payload,
                zero.clone(),
                ti,
                con("list"),
                zero,
            ];
            let d = derive(
                rule_idx,
                &rule_args,
                vec![
                    Premise::Derivation(d_uncase),
                    Premise::Derivation(d_proj),
                    Premise::Derivation(d_table),
                    Premise::Derivation(d_refs),
                    Premise::Derivation(d_len0),
                    Premise::Side(side_le),
                    Premise::Side(side_n0),
                    Premise::Derivation(d_sort_at),
                    Premise::Derivation(d_sort_val),
                ],
            );
            check(&d, rule_idx, &rule_args);
            println!("Step_read/table.fill-zero fires end-to-end, hypothesis-free");
        })
    }

    /// **The store-write demo** (Wave-F `ev.upd`/`ev.ext` acceptance): store
    /// *writes* evaluate on the combined set —
    ///
    /// - (a) `fn.with_table` computes an actual **updated-store encoding** on
    ///   a concrete state (`$with_table(z, (0), 0, r') = (store′; frame)`
    ///   with `store′.TABLES[0].REFS = [r′]`) through the 4-segment
    ///   `ev.upd.root.dot.TABLES.idx.dot.REFS.idx` family, and an
    ///   out-of-bounds write REFUSES (the `ev.len` premise cannot be met);
    /// - (b) `Step/local.set` — a real store-**writing** Step rule — derives
    ///   end-to-end, hypothesis-free: the conclusion's `$with_local(z, x,
    ///   val)` graph premise grounds through
    ///   `ev.upd.root.dot.LOCALS.idx`, so the step's target state is the
    ///   genuinely-updated encoding, ready for a consuming chain.
    ///
    /// Before the write families, every `Upd`/`Ext` RHS was a coarse spine
    /// (`dec.coarse-spine`): sound, never fireable — no writing step could
    /// ground.
    #[test]
    fn store_writes_fire_end_to_end() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();

            let derive = |idx: usize, args: &[Term], prems: Vec<Premise>| {
                metalogic::derive_mixed(&rs, idx, n, args, prems)
                    .unwrap_or_else(|e| panic!("clause {idx} at {args:?}: {e}"))
            };
            let check = |thm: &Thm, idx: usize, args: &[Term]| {
                assert_genuine(thm);
                let expected =
                    metalogic::derivable(&rs, &instantiate(&clauses[idx], args)).unwrap();
                assert_eq!(thm.concl(), &expected, "clause {idx} conclusion");
            };
            let nth_of = |rel: &str, k: usize| {
                (0..n)
                    .filter(|i| report.metas[*i].relation == rel)
                    .nth(k)
                    .unwrap_or_else(|| panic!("no clause {k} of {rel}"))
            };
            let find = |rel: &str, name: &str| {
                report
                    .metas
                    .iter()
                    .position(|m| m.relation == rel && m.name == name)
                    .unwrap_or_else(|| panic!("no clause for {rel}/{name}"))
            };

            // -- Ground state: one table with one ref; one empty local slot.
            let a = |x: Term, y: Term| app(x, y).unwrap();
            let zero = covalence_hol_eval::mk_nat(0u64);
            let w0 = a(con("num.nat"), zero.clone()); // ⌜0⌝ wrapped
            let i32e = a(con("case.I32"), con("tup"));
            let payload = a(con("tup"), w0.clone());
            let idx0 = a(con("case.%"), payload.clone()); // x = (0)
            let r_old = a(con("case.REF.NULL"), a(con("tup"), con("opt.none")));
            let r_new = a(con("case.REF.HOST_ADDR"), a(con("tup"), w0.clone()));
            let ti = a(
                con("struct"),
                a(con("field.REFS"), a(con("list"), r_old.clone())),
            ); // REFS = [r_old]
            let ti2 = a(
                con("struct"),
                a(con("field.REFS"), a(con("list"), r_new.clone())),
            ); // REFS = [r_new]
            let mk_store = |t: &Term| {
                a(
                    con("struct"),
                    a(con("field.TABLES"), a(con("list"), t.clone())),
                )
            };
            let (store, store2) = (mk_store(&ti), mk_store(&ti2));
            let minst = a(
                con("struct"),
                a(con("field.TABLES"), a(con("list"), w0.clone())),
            );
            let frame = a(con("struct"), a(con("field.MODULE"), minst.clone()));
            let mk_z =
                |s: &Term, f: &Term| a(con("case.%;%"), a(a(con("tup"), s.clone()), f.clone()));
            let z = mk_z(&store, &frame);

            // -- Shared plumbing: sof/fof, the idx wrapper, list lengths.
            let d_store = derive(
                nth_of("fn.store", 0),
                &[store.clone(), frame.clone()],
                vec![],
            );
            let d_frame = derive(
                nth_of("fn.frame", 0),
                &[store.clone(), frame.clone()],
                vec![],
            );
            let d_sof = derive(
                nth_of("fn.sof", 0),
                &[z.clone(), store.clone()],
                vec![Premise::Derivation(d_store)],
            );
            let d_fof = derive(
                nth_of("fn.fof", 0),
                &[z.clone(), frame.clone()],
                vec![Premise::Derivation(d_frame)],
            );
            let d_dot_mod = derive(
                nth_of("ev.dot.MODULE", 0),
                &[con("struct"), minst.clone()],
                vec![],
            );
            let tables_m = a(con("list"), w0.clone());
            let d_dot_tm = derive(
                nth_of("ev.dot.TABLES", 0),
                &[con("struct"), tables_m.clone()],
                vec![],
            );
            let d_uncase = derive(nth_of("ev.uncase.%", 0), &[payload.clone()], vec![]);
            let d_proj = derive(nth_of("ev.proj.0", 0), &[w0.clone()], vec![]);
            let d_len0 = derive(nth_of("ev.len", 0), &[], vec![]);
            let d_idx_m = derive(
                nth_of("ev.idx", 0),
                &[con("list"), w0.clone(), zero.clone()],
                vec![Premise::Derivation(d_len0.clone())],
            );

            // ------------------------------------------------------------
            // (a) fn.with_table(z, (0), 0, r_new) = (store2; frame): the
            //     4-segment write chain, innermost-out.
            // ------------------------------------------------------------
            // upd.root.idx: [r_old][0 := r_new] = [r_new].
            let d_w_refs = derive(
                nth_of("ev.upd.root.idx", 0),
                &[con("list"), r_old.clone(), zero.clone(), r_new.clone()],
                vec![Premise::Derivation(d_len0.clone())],
            );
            // upd.root.dot.REFS.idx: ti[.REFS[0] := r_new] = ti2.
            let d_w_ti = derive(
                nth_of("ev.upd.root.dot.REFS.idx", 0),
                &[
                    con("struct"),
                    a(con("list"), r_old.clone()),
                    zero.clone(),
                    r_new.clone(),
                    a(con("list"), r_new.clone()),
                ],
                vec![Premise::Derivation(d_w_refs)],
            );
            // upd.root.idx.dot.REFS.idx: [ti][0].REFS[0] := r_new = [ti2].
            let d_w_tables = derive(
                nth_of("ev.upd.root.idx.dot.REFS.idx", 0),
                &[
                    con("list"),
                    ti.clone(),
                    zero.clone(),
                    zero.clone(),
                    r_new.clone(),
                    ti2.clone(),
                ],
                vec![
                    Premise::Derivation(d_len0.clone()),
                    Premise::Derivation(d_w_ti),
                ],
            );
            // upd.root.dot.TABLES.idx.dot.REFS.idx: store[...] = store2.
            let d_w_store = derive(
                nth_of("ev.upd.root.dot.TABLES.idx.dot.REFS.idx", 0),
                &[
                    con("struct"),
                    a(con("list"), ti.clone()),
                    zero.clone(),
                    zero.clone(),
                    r_new.clone(),
                    a(con("list"), ti2.clone()),
                ],
                vec![Premise::Derivation(d_w_tables)],
            );
            check(
                &d_w_store,
                nth_of("ev.upd.root.dot.TABLES.idx.dot.REFS.idx", 0),
                &[
                    con("struct"),
                    a(con("list"), ti.clone()),
                    zero.clone(),
                    zero.clone(),
                    r_new.clone(),
                    a(con("list"), ti2.clone()),
                ],
            );

            let wt_idx = nth_of("fn.with_table", 0);
            let wt_args = [
                z.clone(),
                idx0.clone(),
                w0.clone(), // i (bare metavar slot: full wrapped encoding)
                r_new.clone(),
                store.clone(),    // $sof(z)
                frame.clone(),    // $fof(z) (tup component)
                frame.clone(),    // $fof(z) (path read)
                minst.clone(),    // .MODULE
                tables_m.clone(), // .TABLES (module)
                payload.clone(),  // uncase x
                w0.clone(),       // proj.0
                w0.clone(),       // module TABLES[x] = table address 0
                store2.clone(),   // the ev.upd result — the WRITTEN store
            ];
            let d_wt = derive(
                wt_idx,
                &wt_args,
                vec![
                    Premise::Derivation(d_sof.clone()),
                    Premise::Derivation(d_fof.clone()),
                    Premise::Derivation(d_fof.clone()),
                    Premise::Derivation(d_dot_mod.clone()),
                    Premise::Derivation(d_dot_tm.clone()),
                    Premise::Derivation(d_uncase.clone()),
                    Premise::Derivation(d_proj.clone()),
                    Premise::Derivation(d_idx_m.clone()),
                    Premise::Derivation(d_w_store),
                ],
            );
            check(&d_wt, wt_idx, &wt_args);
            println!("(a) fn.with_table computes the updated-store encoding");

            // REFUSE: writing table index 1 of the 1-element TABLES list is
            // out of bounds — the level's hit clause demands `len([], 1)`.
            let one = covalence_hol_eval::mk_nat(1u64);
            assert!(
                metalogic::derive_mixed(
                    &rs,
                    nth_of("ev.upd.root.idx.dot.REFS.idx", 0),
                    n,
                    &[
                        con("list"),
                        ti.clone(),
                        one,
                        zero.clone(),
                        r_new.clone(),
                        ti2.clone(),
                    ],
                    vec![
                        Premise::Derivation(d_len0.clone()),
                        Premise::Derivation(
                            metalogic::derive_mixed(
                                &rs,
                                nth_of("ev.upd.root.dot.REFS.idx", 0),
                                n,
                                &[
                                    con("struct"),
                                    a(con("list"), r_old.clone()),
                                    zero.clone(),
                                    r_new.clone(),
                                    a(con("list"), r_new.clone()),
                                ],
                                vec![Premise::Derivation(
                                    metalogic::derive_mixed(
                                        &rs,
                                        nth_of("ev.upd.root.idx", 0),
                                        n,
                                        &[con("list"), r_old.clone(), zero.clone(), r_new.clone()],
                                        vec![Premise::Derivation(d_len0.clone())],
                                    )
                                    .unwrap(),
                                )],
                            )
                            .unwrap(),
                        ),
                    ],
                )
                .is_err(),
                "an out-of-bounds table write must refuse"
            );
            println!("    …and an out-of-bounds write refuses");

            // ------------------------------------------------------------
            // (b) Step/local.set: a real WRITING step, end-to-end.
            // ------------------------------------------------------------
            // State for the write: an empty local slot.
            let frame_l = a(
                con("struct"),
                a(con("field.LOCALS"), a(con("list"), con("opt.none"))),
            );
            let store_l = con("struct"); // sof(z) is only projected, never read into
            let z_l = mk_z(&store_l, &frame_l);
            let val = a(
                con("case.CONST"),
                a(a(con("tup"), i32e.clone()), idx0.clone()),
            );
            let val_opt = a(con("opt.some"), val.clone());
            let frame_l2 = a(
                con("struct"),
                a(con("field.LOCALS"), a(con("list"), val_opt.clone())),
            );
            let z_l2 = mk_z(&store_l, &frame_l2);

            let d_store_l = derive(
                nth_of("fn.store", 0),
                &[store_l.clone(), frame_l.clone()],
                vec![],
            );
            let d_frame_l = derive(
                nth_of("fn.frame", 0),
                &[store_l.clone(), frame_l.clone()],
                vec![],
            );
            let d_sof_l = derive(
                nth_of("fn.sof", 0),
                &[z_l.clone(), store_l.clone()],
                vec![Premise::Derivation(d_store_l)],
            );
            let d_fof_l = derive(
                nth_of("fn.fof", 0),
                &[z_l.clone(), frame_l.clone()],
                vec![Premise::Derivation(d_frame_l)],
            );
            // The write: frame_l[.LOCALS[0] := ?(val)] = frame_l2.
            let d_w_slot = derive(
                nth_of("ev.upd.root.idx", 0),
                &[con("list"), con("opt.none"), zero.clone(), val_opt.clone()],
                vec![Premise::Derivation(d_len0.clone())],
            );
            let d_w_frame = derive(
                nth_of("ev.upd.root.dot.LOCALS.idx", 0),
                &[
                    con("struct"),
                    a(con("list"), con("opt.none")),
                    zero.clone(),
                    val_opt.clone(),
                    a(con("list"), val_opt.clone()),
                ],
                vec![Premise::Derivation(d_w_slot)],
            );
            let wl_idx = nth_of("fn.with_local", 0);
            let wl_args = [
                z_l.clone(),
                idx0.clone(),
                val.clone(),
                store_l.clone(),
                frame_l.clone(),
                payload.clone(),
                w0.clone(),
                frame_l2.clone(),
            ];
            let d_wl = derive(
                wl_idx,
                &wl_args,
                vec![
                    Premise::Derivation(d_sof_l),
                    Premise::Derivation(d_fof_l),
                    Premise::Derivation(d_uncase.clone()),
                    Premise::Derivation(d_proj.clone()),
                    Premise::Derivation(d_w_frame),
                ],
            );
            check(&d_wl, wl_idx, &wl_args);
            println!("(b) fn.with_local(z, (0), val) = (store; frame') fires");

            // The sort guard for the rule's sub-only `val` (CONST head).
            let val_payload = a(a(con("tup"), i32e.clone()), idx0.clone());
            let sort_val = (0..n)
                .filter(|i| report.metas[*i].relation == "ev.sort.val")
                .find(|i| {
                    clauses[*i].metavars.len() == 1
                        && instantiate(&clauses[*i], &[val_payload.clone()])
                            == crate::wasm::lower::evalrel::ev_graph("sort.val", &[], &val).unwrap()
                })
                .expect("ev.sort.val CONST clause");
            let d_sort_val = derive(sort_val, &[val_payload.clone()], vec![]);

            let rule_idx = find("Step", "local.set");
            let rule_args = [z_l, val, idx0, z_l2];
            let d_step = derive(
                rule_idx,
                &rule_args,
                vec![Premise::Derivation(d_wl), Premise::Derivation(d_sort_val)],
            );
            check(&d_step, rule_idx, &rule_args);
            println!("Step/local.set WRITES the store end-to-end, hypothesis-free");
        })
    }

    /// A real WASM-spec integer helper now fires through the shared integer
    /// ordering evaluator: `$sat_u_(32, -1) = 0` takes the first saturation
    /// clause because `-1 < int(0)`.
    #[test]
    fn sat_u_negative_fires_through_integer_order() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();
            let derive = |idx: usize, args: &[Term], prems: Vec<Premise>| {
                metalogic::derive_mixed(&rs, idx, n, args, prems)
            };

            let mag0 = covalence_hol_eval::mk_nat(0u64);
            let mag1 = covalence_hol_eval::mk_nat(1u64);
            let n32 =
                crate::wasm::lower::evalrel::wrap_nat(covalence_hol_eval::mk_nat(32u64)).unwrap();
            let neg1 = crate::wasm::lower::evalrel::wrap_int(1, mag1.clone()).unwrap();
            let int0 = crate::wasm::lower::evalrel::wrap_int(0, mag0.clone()).unwrap();
            let nat0 = crate::wasm::lower::evalrel::wrap_nat(mag0.clone()).unwrap();

            let ev_goal = crate::wasm::lower::evalrel::ev_graph(
                "int.lt",
                &[neg1.clone(), int0],
                &con("bool.true"),
            )
            .unwrap();
            let ev_idx = (0..n)
                .filter(|&i| report.metas[i].relation == "ev.int.lt")
                .find(|&i| {
                    clauses[i].metavars.len() == 2
                        && instantiate(&clauses[i], &[mag1.clone(), mag0.clone()]) == ev_goal
                })
                .expect("negative < non-negative evaluator clause");
            let d_lt = derive(ev_idx, &[mag1, mag0], vec![]).unwrap();
            assert_genuine(&d_lt);

            let sat_goal =
                super::super::fn_graph("sat_u_", &[n32.clone(), neg1.clone()], &nat0).unwrap();
            let sat_idx = (0..n)
                .filter(|&i| report.metas[i].relation == "fn.sat_u_")
                .find(|&i| {
                    clauses[i].metavars.len() == 2
                        && instantiate(&clauses[i], &[n32.clone(), neg1.clone()]) == sat_goal
                })
                .expect("sat_u negative clause");
            assert_eq!(clauses[sat_idx].prems.len(), 1);
            let d_sat = derive(sat_idx, &[n32, neg1], vec![Premise::Derivation(d_lt)]).unwrap();
            assert_genuine(&d_sat);
            assert_eq!(
                d_sat.concl(),
                &metalogic::derivable(&rs, &sat_goal).unwrap()
            );
        })
    }

    /// The bundled `$free_block` definition maps `$free_instr` over its
    /// instruction list before folding with `$free_list`. Its empty-list map
    /// case is now an ordinary derivable evaluator judgement, not an
    /// `opaque.cond.iter-map` blocker.
    #[test]
    fn free_block_empty_map_is_derivable() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();

            let map_tag = (0..n)
                .filter(|&i| report.metas[i].relation == "fn.free_block")
                .flat_map(|i| clauses[i].prems.iter())
                .find_map(|p| {
                    let LowerPrem::Judgement(j) = p else {
                        return None;
                    };
                    concl_tag(j).filter(|tag| tag.starts_with("ev.map."))
                })
                .expect("free_block carries a mapped free_instr premise");
            let base = (0..n)
                .find(|&i| {
                    report.metas[i].relation == map_tag
                        && clauses[i].prems.is_empty()
                        && clauses[i].metavars.is_empty()
                })
                .expect("free_block map nil clause");
            let d_map = metalogic::derive_mixed(&rs, base, n, &[], vec![]).unwrap();
            assert_genuine(&d_map);

            let op = map_tag.strip_prefix("ev.").unwrap();
            let expected =
                crate::wasm::lower::evalrel::ev_graph(op, &[con("list")], &con("list")).unwrap();
            assert_eq!(
                d_map.concl(),
                &metalogic::derivable(&rs, &expected).unwrap()
            );
        })
    }

    /// `Step_pure/vsplat` uses a `ListN(M)` map of `$lpacknum_`. At `M = 0`
    /// its generated list is kernel-derived as empty, exercising the indexed
    /// map base case from a real SIMD reduction rule.
    #[test]
    fn vsplat_zero_length_map_is_derivable() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();

            let map_tag = (0..n)
                .filter(|&i| {
                    report.metas[i].relation == "Step_pure" && report.metas[i].name == "vsplat"
                })
                .flat_map(|i| clauses[i].prems.iter())
                .find_map(|p| {
                    let LowerPrem::Judgement(j) = p else {
                        return None;
                    };
                    concl_tag(j).filter(|tag| tag.starts_with("ev.map."))
                })
                .expect("vsplat carries an indexed lpacknum_ map");
            let base = (0..n)
                .find(|&i| {
                    report.metas[i].relation == map_tag
                        && clauses[i].prems.is_empty()
                        && clauses[i].metavars.len() == 2
                })
                .expect("vsplat ListN map zero clause");
            let args = [con("case.I8"), con("zero-lane")];
            let d_map = metalogic::derive_mixed(&rs, base, n, &args, vec![]).unwrap();
            assert_genuine(&d_map);
            assert_eq!(
                d_map.concl(),
                &metalogic::derivable(&rs, &instantiate(&clauses[base], &args)).unwrap()
            );
        })
    }

    /// `Instr_ok/select-impl` accepts either a numeric or vector value type.
    /// Its structural `or` is represented by a two-clause guard relation;
    /// this exercises the numeric branch with a reflexive encoded equality.
    #[test]
    fn select_impl_structural_or_branch_is_derivable() {
        with_total_stack(|| {
            let defs = wasm_spec();
            let (clauses, report) = total_spec_clauses(&defs).unwrap();
            let rs = rule_set_of(clauses.clone());
            let n = rs.n_clauses().unwrap();

            let main = (0..n)
                .find(|&i| {
                    report.metas[i].relation == "Instr_ok" && report.metas[i].name == "select-impl"
                })
                .expect("Instr_ok/select-impl");
            let guard_tag = clauses[main]
                .prems
                .iter()
                .find_map(|p| {
                    let LowerPrem::Judgement(j) = p else {
                        return None;
                    };
                    concl_tag(j).filter(|tag| tag.starts_with("ev.guard."))
                })
                .expect("select-impl structural-or guard");
            let branch = (0..n)
                .find(|&i| {
                    report.metas[i].relation == guard_tag
                        && matches!(clauses[i].prems.as_slice(), [LowerPrem::Side(_)])
                })
                .expect("one select-impl guard branch");
            let args = vec![con("same-type"); clauses[branch].metavars.len()];
            let LowerPrem::Side(side) = &clauses[branch].prems[0] else {
                unreachable!()
            };
            let mut side = side.clone();
            for (mv, arg) in clauses[branch].metavars.iter().zip(&args) {
                side = subst_free(&side, &Var::new(metavar_name(mv), phi()), arg);
            }
            let d_guard = metalogic::derive_mixed(
                &rs,
                branch,
                n,
                &args,
                vec![Premise::Side(prove_side(&side).unwrap())],
            )
            .unwrap();
            assert_genuine(&d_guard);
            assert_eq!(
                d_guard.concl(),
                &metalogic::derivable(&rs, &instantiate(&clauses[branch], &args)).unwrap()
            );
        })
    }
}
