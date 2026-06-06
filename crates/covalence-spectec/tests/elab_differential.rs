//! Phase 2g — differential test against `wasm_spec_ast`.
//!
//! Runs the full Covalence pipeline on the wasm-3.0 corpus
//! (lex → parse → elab → build_doc → to_spectec_ast) and compares the
//! resulting `Vec<SpecTecDef>` against the OCaml reference dump that
//! ships with `wasm_spec_ast::get_wasm_spectec_ast()`. The assertion is
//! NOT pointwise equality — the converter is still skeleton-level. The
//! test reports per-discriminant coverage (count of names that match in
//! both sides) so we can track progress slice over slice.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use covalence_spectec::{
    ast_doc::{build_doc, to_spectec_ast},
    elab::build_table,
    lex::lex,
    parse::parse,
    source::SourceMap,
};
use spectec_ast::{SpecTecDef, SpecTecExp, SpecTecOpTyp, SpecTecRule};

fn assets_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("assets/spectec")
}

#[test]
fn diff_against_wasm_spec_ast() {
    // Load and elaborate the entire wasm-3.0 corpus.
    let dir = assets_dir().join("wasm-3.0");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("spectec"))
        .collect();
    files.sort();

    let mut map = SourceMap::new();
    let mut all_tops = Vec::new();
    for f in &files {
        let text = std::fs::read_to_string(f).unwrap();
        let id = map.add(f, &text);
        let tokens = lex(id, &text).unwrap();
        let tops = parse(id, tokens).unwrap();
        all_tops.extend(tops);
    }
    let ctx = build_table(&all_tops).expect("build_table failed");
    let doc = build_doc(&all_tops, &ctx);
    let ours = to_spectec_ast(&doc, &ctx);

    // Reference: the OCaml dump.
    let reference = covalence_spectec::wasm::get_wasm_spectec_ast();

    // Coverage analysis. Build sets of (kind, name) pairs from each
    // side, plus map name → MixOp for relations.
    let (our_kinds, our_rel_mixops) = summarise_with_rec(&ours);
    let (ref_kinds, ref_rel_mixops) = summarise_with_rec(&reference);

    let kinds = ["Typ", "Rel", "Dec", "Gram"];
    let mut report: BTreeMap<&str, KindCoverage> = BTreeMap::new();
    for k in &kinds {
        let ours: BTreeSet<&String> = our_kinds
            .iter()
            .filter_map(|(kk, n)| if kk == k { Some(n) } else { None })
            .collect();
        let theirs: BTreeSet<&String> = ref_kinds
            .iter()
            .filter_map(|(kk, n)| if kk == k { Some(n) } else { None })
            .collect();
        let both: usize = ours.intersection(&theirs).count();
        report.insert(
            *k,
            KindCoverage {
                ours: ours.len(),
                theirs: theirs.len(),
                both,
            },
        );
    }

    // MixOp comparison: among Rel names common to both sides, how many
    // have identical MixOp fragment lists?
    let mut rel_mixop_matches = 0usize;
    let mut rel_mixop_compared = 0usize;
    for (name, ours_mo) in &our_rel_mixops {
        if let Some(theirs_mo) = ref_rel_mixops.get(name) {
            rel_mixop_compared += 1;
            if ours_mo == theirs_mo {
                rel_mixop_matches += 1;
            }
        }
    }

    eprintln!("=== Phase 2g differential coverage report ===");
    eprintln!("(numbers are: ours / theirs / both — both is the intersection size)");
    for (k, c) in &report {
        let pct = if c.theirs == 0 {
            0.0
        } else {
            100.0 * c.both as f64 / c.theirs as f64
        };
        eprintln!(
            "  {:6}  ours: {:>4}  theirs: {:>4}  matched names: {:>4}  ({:>5.1}% of theirs)",
            k, c.ours, c.theirs, c.both, pct,
        );
    }
    eprintln!(
        "  Rel MixOp matches: {rel_mixop_matches} / {rel_mixop_compared} compared (Rel names appearing on both sides)"
    );
    if rel_mixop_matches < rel_mixop_compared {
        eprintln!("  MixOp mismatches (first 8):");
        let mut shown = 0;
        for (name, ours_mo) in &our_rel_mixops {
            if shown >= 8 { break; }
            if let Some(theirs_mo) = ref_rel_mixops.get(name)
                && ours_mo != theirs_mo {
                    eprintln!(
                        "    {name}: ours {ours_mo:?}\n      theirs {theirs_mo:?}"
                    );
                    shown += 1;
                }
        }
    }

    // Rule body coverage: for relations that appear on both sides,
    // walk paired rules in source order and count how many of OUR
    // rule conclusions are real expressions (non-sentinel).
    let our_rules = rules_by_relation(&ours);
    let their_rules = rules_by_relation(&reference);
    let mut our_real_concl = 0usize;
    let mut total_rule_pairs = 0usize;
    for (rel, our_list) in &our_rules {
        if let Some(their_list) = their_rules.get(rel) {
            let pairs = our_list.len().min(their_list.len());
            total_rule_pairs += pairs;
            for r in our_list.iter().take(pairs) {
                if !is_raw_sentinel_exp(rule_concl(r)) {
                    our_real_concl += 1;
                }
            }
        }
    }
    eprintln!(
        "  Rule conclusions: {our_real_concl} non-sentinel of {total_rule_pairs} paired rules"
    );

    // Typ inst coverage: how many of our Typ decls have at least one
    // non-empty `insts` list (one per profile-tagged declaration)?
    let (our_typ_with_insts, total_typ) = count_typ_insts(&ours);
    eprintln!("  Typ insts non-empty: {our_typ_with_insts} / {total_typ} of our Typ entries");

    // Rec grouping coverage.
    let our_rec_count = count_rec_groups(&ours);
    let their_rec_count = count_rec_groups(&reference);
    eprintln!("  Rec groups: ours {our_rec_count}, theirs {their_rec_count}");
    eprintln!("    ours histogram (size → count):   {:?}", rec_size_histogram(&ours));
    eprintln!("    theirs histogram (size → count): {:?}", rec_size_histogram(&reference));

    // Dec clause coverage: how many of our Dec clauses have a
    // non-sentinel rhs?
    let (our_dec_real_rhs, our_dec_total_clauses) = count_dec_clause_rhs(&ours);
    eprintln!(
        "  Dec clause RHS: {our_dec_real_rhs} non-sentinel of {our_dec_total_clauses} clauses"
    );

    let (rel_t_real, rel_t_total) = count_rel_t_real(&ours);
    let (dec_t_real, dec_t_total) = count_dec_t_real(&ours);
    let (gram_t_real, gram_t_total) = count_gram_t_real(&ours);
    let (their_rel_t, _) = count_rel_t_real(&reference);
    let (their_dec_t, _) = count_dec_t_real(&reference);
    let (their_gram_t, _) = count_gram_t_real(&reference);
    eprintln!(
        "  Rel.t non-placeholder: ours {rel_t_real} / {rel_t_total} (theirs {their_rel_t})"
    );
    eprintln!(
        "  Dec.t non-placeholder: ours {dec_t_real} / {dec_t_total} (theirs {their_dec_t})"
    );
    eprintln!(
        "  Gram.t non-placeholder: ours {gram_t_real} / {gram_t_total} (theirs {their_gram_t})"
    );

    let dec_with_ps = count_dec_with_ps(&ours);
    let typ_with_ps = count_typ_with_ps(&ours);
    let their_typ_with_ps = count_typ_with_ps(&reference);
    let their_dec_with_ps = count_dec_with_ps(&reference);
    eprintln!("  Dec.ps non-empty: ours {dec_with_ps}, theirs {their_dec_with_ps}");
    eprintln!("  Typ.ps non-empty: ours {typ_with_ps}, theirs {their_typ_with_ps}");

    let our_total_prods = count_total_prods(&ours);
    let their_total_prods = count_total_prods(&reference);
    eprintln!("  Grammar prods: ours {our_total_prods}, theirs {their_total_prods}");

    // Operator-type stats: how many Un/Bin/Cmp do we have, and how
    // many have a non-default (`Nat`) operator-type field?
    let (ours_ops, ours_refined) = count_op_types(&ours);
    let (their_ops, their_refined) = count_op_types(&reference);
    eprintln!(
        "  Op types (Un/Bin/Cmp): ours {ours_refined} non-Nat of {ours_ops}; \
         theirs {their_refined} non-Nat of {their_ops}"
    );

    let ours_sub = count_sub_nodes(&ours);
    let their_sub = count_sub_nodes(&reference);
    eprintln!("  Sub coercions: ours {ours_sub}, theirs {their_sub}");

    // Deep structural equality: for every (kind, name) on both sides,
    // does our `SpecTecDef` equal OCaml's via `PartialEq`?
    let deep = deep_equal_report(&ours, &reference);
    if std::env::var("SPECTEC_DIFF_SHOW").is_ok() {
        let limit: usize = std::env::var("SPECTEC_DIFF_SHOW")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        show_first_mismatches(&ours, &reference, limit);
    }
    eprintln!("  per-kind deep structural equality:");
    eprintln!(
        "    Typ:  {} / {} ({:.1}%)",
        deep.typ_eq, deep.typ_total,
        100.0 * deep.typ_eq as f64 / deep.typ_total.max(1) as f64,
    );
    eprintln!(
        "    Rel:  {} / {} ({:.1}%)",
        deep.rel_eq, deep.rel_total,
        100.0 * deep.rel_eq as f64 / deep.rel_total.max(1) as f64,
    );
    eprintln!(
        "    Dec:  {} / {} ({:.1}%)",
        deep.dec_eq, deep.dec_total,
        100.0 * deep.dec_eq as f64 / deep.dec_total.max(1) as f64,
    );
    eprintln!(
        "    Gram: {} / {} ({:.1}%)",
        deep.gram_eq, deep.gram_total,
        100.0 * deep.gram_eq as f64 / deep.gram_total.max(1) as f64,
    );

    let arity_report = arity_match_report(&ours, &reference);
    eprintln!("  per-kind arity match (same body-count for same-name def):");
    eprintln!(
        "    Typ insts:   {} / {} ({:.1}%)",
        arity_report.typ_match, arity_report.typ_total,
        100.0 * arity_report.typ_match as f64 / arity_report.typ_total.max(1) as f64,
    );
    eprintln!(
        "    Rel rules:   {} / {} ({:.1}%)",
        arity_report.rel_match, arity_report.rel_total,
        100.0 * arity_report.rel_match as f64 / arity_report.rel_total.max(1) as f64,
    );
    eprintln!(
        "    Dec clauses: {} / {} ({:.1}%)",
        arity_report.dec_match, arity_report.dec_total,
        100.0 * arity_report.dec_match as f64 / arity_report.dec_total.max(1) as f64,
    );
    eprintln!(
        "    Gram prods:  {} / {} ({:.1}%)",
        arity_report.gram_match, arity_report.gram_total,
        100.0 * arity_report.gram_match as f64 / arity_report.gram_total.max(1) as f64,
    );

    // Acceptance: the names align. (Bodies don't match yet — that's
    // the deferred lowering work surfaced by this test.) We require
    // each kind to have >= 80% name overlap with the OCaml output.
    for (k, c) in &report {
        if c.theirs == 0 {
            continue;
        }
        let pct = 100.0 * c.both as f64 / c.theirs as f64;
        assert!(
            pct >= 80.0,
            "{k}: only {pct:.1}% name overlap with wasm_spec_ast (ours={}, theirs={}, both={})",
            c.ours,
            c.theirs,
            c.both,
        );
    }

    // Per-kind deep-equality floors. Bump these upward whenever a
    // task lands an improvement (the `docs/sketches/spectec-tasks`
    // tree describes the work). Never lower them — a regression
    // means new code broke something that used to work, which is
    // exactly what this test exists to catch.
    let floors: [(&str, usize); 4] =
        [("Typ", 144), ("Rel", 18), ("Dec", 67), ("Gram", 33)];
    let actual = [
        ("Typ", deep.typ_eq),
        ("Rel", deep.rel_eq),
        ("Dec", deep.dec_eq),
        ("Gram", deep.gram_eq),
    ];
    for ((kf, floor), (_, got)) in floors.iter().zip(actual.iter()) {
        assert!(
            got >= floor,
            "{kf}: deep-equality count {got} regressed below floor {floor}; \
             either a recent change broke prior progress or the floor needs to \
             be lowered (do NOT lower without a deliberate decision)"
        );
    }
}

#[derive(Debug, Default)]
struct KindCoverage {
    ours: usize,
    theirs: usize,
    both: usize,
}

type KindPairs = Vec<(String, String)>;
type MixOpMap = BTreeMap<String, Vec<String>>;

// `summarise` (non-recursing version) was used before our converter
// emitted `Rec` groups. Now both sides need to recurse, so we always
// use `summarise_with_rec`. Kept as a doc comment for future
// non-recursing diffs.


/// Build a `name -> rules` map for each `Rel` def. Recurses into `Rec`.
fn rules_by_relation(defs: &[SpecTecDef]) -> BTreeMap<String, Vec<SpecTecRule>> {
    let mut out: BTreeMap<String, Vec<SpecTecRule>> = BTreeMap::new();
    fn walk(d: &SpecTecDef, out: &mut BTreeMap<String, Vec<SpecTecRule>>) {
        match d {
            SpecTecDef::Rel { x, rules, .. } => {
                out.entry(x.clone()).or_default().extend(rules.iter().cloned());
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk(d, out);
                }
            }
            _ => {}
        }
    }
    for d in defs {
        walk(d, &mut out);
    }
    out
}

fn rule_concl(r: &SpecTecRule) -> &SpecTecExp {
    let SpecTecRule::Rule { e, .. } = r;
    e
}

/// Detect our `raw_sentinel()` value (`Bool { b: false }`) — anything
/// the OCaml elaborator would never naturally produce as a top-level
/// conclusion. Used to count *real* lowered conclusions in the diff.
fn is_raw_sentinel_exp(e: &SpecTecExp) -> bool {
    matches!(e, SpecTecExp::Bool { b: false })
}

fn count_typ_insts(defs: &[SpecTecDef]) -> (usize, usize) {
    let mut with = 0;
    let mut total = 0;
    fn walk(d: &SpecTecDef, with: &mut usize, total: &mut usize) {
        match d {
            SpecTecDef::Typ { insts, .. } => {
                *total += 1;
                if !insts.is_empty() {
                    *with += 1;
                }
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk(d, with, total);
                }
            }
            _ => {}
        }
    }
    for d in defs {
        walk(d, &mut with, &mut total);
    }
    (with, total)
}

fn count_rec_groups(defs: &[SpecTecDef]) -> usize {
    let mut n = 0;
    fn walk(d: &SpecTecDef, n: &mut usize) {
        if let SpecTecDef::Rec { ds } = d {
            *n += 1;
            for d in ds {
                walk(d, n);
            }
        }
    }
    for d in defs {
        walk(d, &mut n);
    }
    n
}

/// Break down Rec groups by size — singletons (self-recursive defs)
/// vs multi-member (mutually-recursive groups).
fn rec_size_histogram(defs: &[SpecTecDef]) -> std::collections::BTreeMap<usize, usize> {
    let mut hist: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    fn walk(d: &SpecTecDef, hist: &mut std::collections::BTreeMap<usize, usize>) {
        if let SpecTecDef::Rec { ds } = d {
            *hist.entry(ds.len()).or_insert(0) += 1;
            for d in ds {
                walk(d, hist);
            }
        }
    }
    for d in defs {
        walk(d, &mut hist);
    }
    hist
}

fn is_placeholder_typ(t: &spectec_ast::SpecTecTyp) -> bool {
    matches!(t, spectec_ast::SpecTecTyp::Bool)
}

fn count_rel_t_real(defs: &[SpecTecDef]) -> (usize, usize) {
    let mut real = 0;
    let mut total = 0;
    fn walk(d: &SpecTecDef, real: &mut usize, total: &mut usize) {
        match d {
            SpecTecDef::Rel { t, .. } => {
                *total += 1;
                if !is_placeholder_typ(t) {
                    *real += 1;
                }
            }
            SpecTecDef::Rec { ds } => for d in ds { walk(d, real, total); },
            _ => {}
        }
    }
    for d in defs { walk(d, &mut real, &mut total); }
    (real, total)
}

fn count_dec_t_real(defs: &[SpecTecDef]) -> (usize, usize) {
    let mut real = 0;
    let mut total = 0;
    fn walk(d: &SpecTecDef, real: &mut usize, total: &mut usize) {
        match d {
            SpecTecDef::Dec { t, .. } => {
                *total += 1;
                if !is_placeholder_typ(t) {
                    *real += 1;
                }
            }
            SpecTecDef::Rec { ds } => for d in ds { walk(d, real, total); },
            _ => {}
        }
    }
    for d in defs { walk(d, &mut real, &mut total); }
    (real, total)
}

fn count_gram_t_real(defs: &[SpecTecDef]) -> (usize, usize) {
    let mut real = 0;
    let mut total = 0;
    fn walk(d: &SpecTecDef, real: &mut usize, total: &mut usize) {
        match d {
            SpecTecDef::Gram { t, .. } => {
                *total += 1;
                if !is_placeholder_typ(t) {
                    *real += 1;
                }
            }
            SpecTecDef::Rec { ds } => for d in ds { walk(d, real, total); },
            _ => {}
        }
    }
    for d in defs { walk(d, &mut real, &mut total); }
    (real, total)
}

fn count_dec_with_ps(defs: &[SpecTecDef]) -> usize {
    let mut n = 0;
    fn walk(d: &SpecTecDef, n: &mut usize) {
        match d {
            SpecTecDef::Dec { ps, .. } if !ps.is_empty() => *n += 1,
            SpecTecDef::Rec { ds } => for d in ds { walk(d, n); },
            _ => {}
        }
    }
    for d in defs { walk(d, &mut n); }
    n
}

#[derive(Default)]
struct DeepEqReport {
    typ_eq: usize,
    typ_total: usize,
    rel_eq: usize,
    rel_total: usize,
    dec_eq: usize,
    dec_total: usize,
    gram_eq: usize,
    gram_total: usize,
}

fn deep_equal_report(ours: &[SpecTecDef], theirs: &[SpecTecDef]) -> DeepEqReport {
    let our_map = build_def_map(ours);
    let their_map = build_def_map(theirs);
    let mut r = DeepEqReport::default();
    for ((kind, name), ours_def) in &our_map {
        let Some(theirs_def) = their_map.get(&(kind.clone(), name.clone())) else {
            continue;
        };
        match kind.as_str() {
            "Typ" => {
                r.typ_total += 1;
                if ours_def == theirs_def {
                    r.typ_eq += 1;
                }
            }
            "Rel" => {
                r.rel_total += 1;
                if ours_def == theirs_def {
                    r.rel_eq += 1;
                }
            }
            "Dec" => {
                r.dec_total += 1;
                if ours_def == theirs_def {
                    r.dec_eq += 1;
                }
            }
            "Gram" => {
                r.gram_total += 1;
                if ours_def == theirs_def {
                    r.gram_eq += 1;
                }
            }
            _ => {}
        }
    }
    r
}

fn show_first_mismatches(ours: &[SpecTecDef], theirs: &[SpecTecDef], n: usize) {
    let our_map = build_def_map(ours);
    let their_map = build_def_map(theirs);
    for kind in ["Typ", "Rel", "Dec", "Gram"] {
        let mut shown_for_kind = 0;
        for ((k, name), od) in &our_map {
            if k != kind { continue; }
            if shown_for_kind >= n { break; }
            let Some(td) = their_map.get(&(k.clone(), name.clone())) else { continue };
            if od != td {
                eprintln!("\n=== {kind} {name} differs ===");
                eprintln!("OURS:   {od:#?}");
                eprintln!("THEIRS: {td:#?}");
                shown_for_kind += 1;
            }
        }
    }
}

fn build_def_map(defs: &[SpecTecDef]) -> BTreeMap<(String, String), SpecTecDef> {
    let mut out = BTreeMap::new();
    fn walk(d: &SpecTecDef, out: &mut BTreeMap<(String, String), SpecTecDef>) {
        match d {
            SpecTecDef::Typ { x, .. } => {
                out.insert(("Typ".into(), x.clone()), d.clone());
            }
            SpecTecDef::Rel { x, .. } => {
                out.insert(("Rel".into(), x.clone()), d.clone());
            }
            SpecTecDef::Dec { x, .. } => {
                out.insert(("Dec".into(), x.clone()), d.clone());
            }
            SpecTecDef::Gram { x, .. } => {
                out.insert(("Gram".into(), x.clone()), d.clone());
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk(d, out);
                }
            }
        }
    }
    for d in defs {
        walk(d, &mut out);
    }
    out
}

#[derive(Default)]
struct ArityReport {
    typ_match: usize,
    typ_total: usize,
    rel_match: usize,
    rel_total: usize,
    dec_match: usize,
    dec_total: usize,
    gram_match: usize,
    gram_total: usize,
}

/// For each (kind, name) appearing on both sides, compare the
/// immediate-child arity (Typ.insts.len, Rel.rules.len, Dec.clauses.len,
/// Gram.prods.len). Useful coarse measure: "are we producing the right
/// number of inner items per def?"
fn arity_match_report(ours: &[SpecTecDef], theirs: &[SpecTecDef]) -> ArityReport {
    let our_map = build_arity_map(ours);
    let their_map = build_arity_map(theirs);
    let mut r = ArityReport::default();
    for ((kind, name), ours_n) in &our_map {
        let Some(theirs_n) = their_map.get(&(kind.clone(), name.clone())) else {
            continue;
        };
        match kind.as_str() {
            "Typ" => {
                r.typ_total += 1;
                if ours_n == theirs_n {
                    r.typ_match += 1;
                }
            }
            "Rel" => {
                r.rel_total += 1;
                if ours_n == theirs_n {
                    r.rel_match += 1;
                }
            }
            "Dec" => {
                r.dec_total += 1;
                if ours_n == theirs_n {
                    r.dec_match += 1;
                }
            }
            "Gram" => {
                r.gram_total += 1;
                if ours_n == theirs_n {
                    r.gram_match += 1;
                }
            }
            _ => {}
        }
    }
    r
}

fn build_arity_map(defs: &[SpecTecDef]) -> BTreeMap<(String, String), usize> {
    let mut out = BTreeMap::new();
    fn walk(d: &SpecTecDef, out: &mut BTreeMap<(String, String), usize>) {
        match d {
            SpecTecDef::Typ { x, insts, .. } => {
                out.insert(("Typ".into(), x.clone()), insts.len());
            }
            SpecTecDef::Rel { x, rules, .. } => {
                out.insert(("Rel".into(), x.clone()), rules.len());
            }
            SpecTecDef::Dec { x, clauses, .. } => {
                out.insert(("Dec".into(), x.clone()), clauses.len());
            }
            SpecTecDef::Gram { x, prods, .. } => {
                out.insert(("Gram".into(), x.clone()), prods.len());
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk(d, out);
                }
            }
        }
    }
    for d in defs {
        walk(d, &mut out);
    }
    out
}

fn count_total_prods(defs: &[SpecTecDef]) -> usize {
    let mut n = 0;
    fn walk(d: &SpecTecDef, n: &mut usize) {
        match d {
            SpecTecDef::Gram { prods, .. } => *n += prods.len(),
            SpecTecDef::Rec { ds } => for d in ds { walk(d, n); },
            _ => {}
        }
    }
    for d in defs { walk(d, &mut n); }
    n
}

/// Walk every Un/Bin/Cmp anywhere inside the def list (recursing
/// through Rec). Returns (total_count, count_with_non_default_optyp).
/// Default = `Num(Nat)`. Anything else (Int, Rat, Real, Bool) is
/// considered "refined."
fn count_op_types(defs: &[SpecTecDef]) -> (usize, usize) {
    let mut total = 0usize;
    let mut refined = 0usize;
    fn refined_op(t: &SpecTecOpTyp) -> bool {
        !matches!(t, SpecTecOpTyp::Num(spectec_ast::SpecTecNumTyp::Nat))
    }
    fn walk_exp(e: &SpecTecExp, total: &mut usize, refined: &mut usize) {
        use SpecTecExp as E;
        match e {
            E::Un { t, e2, .. } => {
                *total += 1;
                if refined_op(t) {
                    *refined += 1;
                }
                walk_exp(e2, total, refined);
            }
            E::Bin { t, e1, e2, .. } | E::Cmp { t, e1, e2, .. } => {
                *total += 1;
                if refined_op(t) {
                    *refined += 1;
                }
                walk_exp(e1, total, refined);
                walk_exp(e2, total, refined);
            }
            E::Idx { e1, e2 } | E::Comp { e1, e2 } | E::Mem { e1, e2 }
            | E::Cat { e1, e2 } => {
                walk_exp(e1, total, refined);
                walk_exp(e2, total, refined);
            }
            E::Slice { e1, e2, e3 } => {
                walk_exp(e1, total, refined);
                walk_exp(e2, total, refined);
                walk_exp(e3, total, refined);
            }
            E::Upd { e1, e2, .. } | E::Ext { e1, e2, .. } => {
                walk_exp(e1, total, refined);
                walk_exp(e2, total, refined);
            }
            E::Str { efs } => {
                for spectec_ast::SpecTecExpField::Field { e, .. } in efs {
                    walk_exp(e, total, refined);
                }
            }
            E::Dot { e1, .. } | E::Len { e1 } | E::Lift { e1 } | E::Unopt { e1 }
            | E::Cvt { e1, .. } | E::Sub { e1, .. } | E::Proj { e1, .. }
            | E::Uncase { e1, .. } | E::Iter { e1, .. } => {
                walk_exp(e1, total, refined);
            }
            E::Tup { es } | E::List { es } => {
                for e in es {
                    walk_exp(e, total, refined);
                }
            }
            E::Case { e1, .. } => walk_exp(e1, total, refined),
            E::Opt { eo: Some(e) } => walk_exp(e, total, refined),
            E::Opt { eo: None } | E::Bool { .. } | E::Num { .. } | E::Text { .. }
            | E::Var { .. } | E::Call { .. } => {}
        }
    }
    fn walk_prem(p: &spectec_ast::SpecTecPrem, total: &mut usize, refined: &mut usize) {
        use spectec_ast::SpecTecPrem as P;
        match p {
            P::Rule { e, .. } | P::If { e } => walk_exp(e, total, refined),
            P::Let { e1, e2 } => {
                walk_exp(e1, total, refined);
                walk_exp(e2, total, refined);
            }
            P::Else => {}
            P::Iter { pr1, .. } => walk_prem(pr1, total, refined),
        }
    }
    fn walk_def(d: &SpecTecDef, total: &mut usize, refined: &mut usize) {
        match d {
            SpecTecDef::Rel { rules, .. } => {
                for SpecTecRule::Rule { e, prs, .. } in rules {
                    walk_exp(e, total, refined);
                    for p in prs {
                        walk_prem(p, total, refined);
                    }
                }
            }
            SpecTecDef::Dec { clauses, .. } => {
                for spectec_ast::SpecTecClause::Clause { e, prs, .. } in clauses {
                    walk_exp(e, total, refined);
                    for p in prs {
                        walk_prem(p, total, refined);
                    }
                }
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk_def(d, total, refined);
                }
            }
            _ => {}
        }
    }
    for d in defs {
        walk_def(d, &mut total, &mut refined);
    }
    (total, refined)
}

fn count_sub_nodes(defs: &[SpecTecDef]) -> usize {
    let mut n = 0usize;
    fn walk_exp(e: &SpecTecExp, n: &mut usize) {
        use SpecTecExp as E;
        match e {
            E::Sub { e1, .. } => {
                *n += 1;
                walk_exp(e1, n);
            }
            E::Un { e2, .. } | E::Len { e1: e2 } | E::Lift { e1: e2 }
            | E::Unopt { e1: e2 } | E::Cvt { e1: e2, .. } | E::Dot { e1: e2, .. }
            | E::Proj { e1: e2, .. } | E::Uncase { e1: e2, .. }
            | E::Iter { e1: e2, .. } | E::Case { e1: e2, .. } => walk_exp(e2, n),
            E::Bin { e1, e2, .. } | E::Cmp { e1, e2, .. } | E::Idx { e1, e2, .. }
            | E::Comp { e1, e2 } | E::Mem { e1, e2 } | E::Cat { e1, e2 } => {
                walk_exp(e1, n);
                walk_exp(e2, n);
            }
            E::Slice { e1, e2, e3 } => {
                walk_exp(e1, n);
                walk_exp(e2, n);
                walk_exp(e3, n);
            }
            E::Upd { e1, e2, .. } | E::Ext { e1, e2, .. } => {
                walk_exp(e1, n);
                walk_exp(e2, n);
            }
            E::Str { efs } => {
                for spectec_ast::SpecTecExpField::Field { e, .. } in efs {
                    walk_exp(e, n);
                }
            }
            E::Tup { es } | E::List { es } => {
                for e in es {
                    walk_exp(e, n);
                }
            }
            E::Opt { eo: Some(e) } => walk_exp(e, n),
            _ => {}
        }
    }
    fn walk_prem(p: &spectec_ast::SpecTecPrem, n: &mut usize) {
        use spectec_ast::SpecTecPrem as P;
        match p {
            P::Rule { e, .. } | P::If { e } => walk_exp(e, n),
            P::Let { e1, e2 } => {
                walk_exp(e1, n);
                walk_exp(e2, n);
            }
            P::Else => {}
            P::Iter { pr1, .. } => walk_prem(pr1, n),
        }
    }
    fn walk_def(d: &SpecTecDef, n: &mut usize) {
        match d {
            SpecTecDef::Rel { rules, .. } => {
                for SpecTecRule::Rule { e, prs, .. } in rules {
                    walk_exp(e, n);
                    for p in prs {
                        walk_prem(p, n);
                    }
                }
            }
            SpecTecDef::Dec { clauses, .. } => {
                for spectec_ast::SpecTecClause::Clause { e, prs, .. } in clauses {
                    walk_exp(e, n);
                    for p in prs {
                        walk_prem(p, n);
                    }
                }
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk_def(d, n);
                }
            }
            _ => {}
        }
    }
    for d in defs {
        walk_def(d, &mut n);
    }
    n
}

fn count_typ_with_ps(defs: &[SpecTecDef]) -> usize {
    let mut n = 0;
    fn walk(d: &SpecTecDef, n: &mut usize) {
        match d {
            SpecTecDef::Typ { ps, .. } if !ps.is_empty() => *n += 1,
            SpecTecDef::Rec { ds } => for d in ds { walk(d, n); },
            _ => {}
        }
    }
    for d in defs { walk(d, &mut n); }
    n
}

fn count_dec_clause_rhs(defs: &[SpecTecDef]) -> (usize, usize) {
    let mut real = 0;
    let mut total = 0;
    fn walk(d: &SpecTecDef, real: &mut usize, total: &mut usize) {
        match d {
            SpecTecDef::Dec { clauses, .. } => {
                for c in clauses {
                    let spectec_ast::SpecTecClause::Clause { e, .. } = c;
                    *total += 1;
                    if !is_raw_sentinel_exp(e) {
                        *real += 1;
                    }
                }
            }
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk(d, real, total);
                }
            }
            _ => {}
        }
    }
    for d in defs {
        walk(d, &mut real, &mut total);
    }
    (real, total)
}

/// Walk `defs` and produce `(kind, name)` pairs plus a map of
/// `rel-name -> mixop fragments` for later comparison. Recurses into
/// `Rec` groups on both sides (our converter now emits them too).
fn summarise_with_rec(defs: &[SpecTecDef]) -> (KindPairs, MixOpMap) {
    let mut pairs = Vec::new();
    let mut mixops = BTreeMap::new();
    fn walk(d: &SpecTecDef, pairs: &mut KindPairs, mixops: &mut MixOpMap) {
        match d {
            SpecTecDef::Typ { x, .. } => pairs.push(("Typ".into(), x.clone())),
            SpecTecDef::Rel { x, op, .. } => {
                pairs.push(("Rel".into(), x.clone()));
                mixops.insert(x.clone(), op.fragments().to_vec());
            }
            SpecTecDef::Dec { x, .. } => pairs.push(("Dec".into(), x.clone())),
            SpecTecDef::Gram { x, .. } => pairs.push(("Gram".into(), x.clone())),
            SpecTecDef::Rec { ds } => {
                for d in ds {
                    walk(d, pairs, mixops);
                }
            }
        }
    }
    for d in defs {
        walk(d, &mut pairs, &mut mixops);
    }
    (pairs, mixops)
}
