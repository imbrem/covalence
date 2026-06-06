//! Build an `ElabContext` (operator table from relation templates) for
//! the full wasm-3.0 corpus. Assert it succeeds, count how many
//! operators we extract, and dump a representative sample.
//!
//! This is the Phase 2c-i acceptance test: the construction pass runs
//! end-to-end on real-world SpecTec input without diagnostic errors.
//! It does NOT verify that the extracted operators are *correct* in
//! detail — that's what the diff-against-spectec_ast tests in Phase 2g
//! will do.

use std::path::PathBuf;

use covalence_spectec::{
    elab::build_table, lex::lex, mixfix::Fragment, parse::parse, source::SourceMap,
    token::Token,
};

fn lit_repr(tok: &Token) -> String {
    match tok {
        Token::Ident(s) => s.clone(),
        Token::Nat(n) => n.to_string(),
        other => other.describe().trim_matches('`').to_string(),
    }
}

fn assets_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("assets/spectec")
}

#[test]
fn build_table_for_wasm_3_0_corpus() {
    let dir = assets_dir().join("wasm-3.0");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("spectec"))
        .collect();
    files.sort();

    // Combine all files into one big elaboration unit (the spec is a
    // single logical module, despite being split across files).
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

    let op_count = ctx.op_table.iter().count();
    assert!(op_count > 0, "no operators extracted from full corpus");

    let type_count = ctx.type_names.len();
    assert!(type_count > 50, "expected dozens of type names, got {type_count}");

    // Profile the table.
    let mut hole_only = 0usize;
    let mut prefix_or_closed = 0usize;
    let mut left_extending = 0usize;
    let mut total_holes = 0usize;
    let mut total_lits = 0usize;
    for op in ctx.op_table.iter() {
        if op.fragments.is_empty() {
            hole_only += 1;
            continue;
        }
        if op.is_prefix_or_closed() {
            prefix_or_closed += 1;
        }
        if op.is_left_extending() {
            left_extending += 1;
        }
        for f in &op.fragments {
            match f {
                Fragment::Hole(_) => total_holes += 1,
                Fragment::Lit(_) => total_lits += 1,
            }
        }
    }

    eprintln!("Extracted operator table from {} files:", files.len());
    eprintln!("  declared type names:  {type_count}");
    eprintln!("  operators total:      {op_count}");
    eprintln!("  prefix/closed:        {prefix_or_closed}");
    eprintln!("  left-extending:       {left_extending}");
    eprintln!("  empty (template):     {hole_only}");
    eprintln!("  total holes:          {total_holes}");
    eprintln!("  total literal frags:  {total_lits}");

    // Show a sample of extracted operators (first 30 by declaration order).
    eprintln!("First 30 operators:");
    for op in ctx.op_table.iter().take(30) {
        let frags: Vec<String> = op.fragments.iter().map(|f| match f {
            Fragment::Hole(_) => "%".into(),
            Fragment::Lit(t) => lit_repr(t),
        }).collect();
        eprintln!("  {:30}  {}", op.name, frags.join(" "));
    }
}
