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
use spectec_ast::{SpecTecDef, SpecTecExp, SpecTecRule};

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

    // Dec clause coverage: how many of our Dec clauses have a
    // non-sentinel rhs?
    let (our_dec_real_rhs, our_dec_total_clauses) = count_dec_clause_rhs(&ours);
    eprintln!(
        "  Dec clause RHS: {our_dec_real_rhs} non-sentinel of {our_dec_total_clauses} clauses"
    );

    let (rel_t_real, rel_t_total) = count_rel_t_real(&ours);
    let (dec_t_real, dec_t_total) = count_dec_t_real(&ours);
    let (gram_t_real, gram_t_total) = count_gram_t_real(&ours);
    eprintln!("  Rel.t non-placeholder: {rel_t_real} / {rel_t_total}");
    eprintln!("  Dec.t non-placeholder: {dec_t_real} / {dec_t_total}");
    eprintln!("  Gram.t non-placeholder: {gram_t_real} / {gram_t_total}");

    let dec_with_ps = count_dec_with_ps(&ours);
    let typ_with_ps = count_typ_with_ps(&ours);
    eprintln!("  Dec.ps non-empty: {dec_with_ps} / {dec_t_total}");
    eprintln!("  Typ.ps non-empty: {typ_with_ps} / {total_typ}");

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
