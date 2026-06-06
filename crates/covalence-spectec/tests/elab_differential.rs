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
use spectec_ast::SpecTecDef;

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
    let (our_kinds, our_rel_mixops) = summarise(&ours);
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

/// Walk `defs` and produce `(kind, name)` pairs plus a map of
/// `rel-name -> mixop fragments` for later comparison. Does NOT recurse
/// into `Rec` groups (our converter doesn't emit them yet).
fn summarise(defs: &[SpecTecDef]) -> (Vec<(String, String)>, BTreeMap<String, Vec<String>>) {
    let mut pairs = Vec::new();
    let mut mixops = BTreeMap::new();
    for d in defs {
        match d {
            SpecTecDef::Typ { x, .. } => pairs.push(("Typ".into(), x.clone())),
            SpecTecDef::Rel { x, op, .. } => {
                pairs.push(("Rel".into(), x.clone()));
                mixops.insert(x.clone(), op.fragments().to_vec());
            }
            SpecTecDef::Dec { x, .. } => pairs.push(("Dec".into(), x.clone())),
            SpecTecDef::Gram { x, .. } => pairs.push(("Gram".into(), x.clone())),
            SpecTecDef::Rec { .. } => {}
        }
    }
    (pairs, mixops)
}

/// Like `summarise` but DOES recurse into `Rec` groups (OCaml dump uses
/// them heavily; our skeleton doesn't yet emit them).
fn summarise_with_rec(
    defs: &[SpecTecDef],
) -> (Vec<(String, String)>, BTreeMap<String, Vec<String>>) {
    let mut pairs = Vec::new();
    let mut mixops = BTreeMap::new();
    fn walk(
        d: &SpecTecDef,
        pairs: &mut Vec<(String, String)>,
        mixops: &mut BTreeMap<String, Vec<String>>,
    ) {
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
