//! Phase 1 parse-corpus test.
//!
//! Verifies that every vendored upstream `.spectec` file parses to a CST
//! without diagnostic errors. Phase 1 structurally parses `syntax` and
//! `def` only; `relation` / `rule` / `var` / `grammar` fold into
//! `Top::Other`. The acceptance criterion is therefore "parses without
//! error," not "all forms are fully structured."
//!
//! Per-file statistics (top-level form counts by kind) are recorded for
//! the verification report so we can see how the structured/unstructured
//! split lands across the corpus.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use covalence_spectec::{cst::Top, lex::lex, parse::parse, source::SourceMap};

fn assets_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("assets/spectec")
}

fn list_spectec_files(dir: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("spectec"))
        .collect();
    out.sort();
    out
}

#[derive(Default, Clone, Copy, Debug)]
struct FormCounts {
    syntax: usize,
    def_sig: usize,
    def_clause: usize,
    var: usize,
    relation: usize,
    rule: usize,
    grammar: usize,
    other: usize,
}

impl FormCounts {
    fn add(&mut self, tops: &[Top]) {
        for t in tops {
            match t {
                Top::Syntax(_) => self.syntax += 1,
                Top::DefSig(_) => self.def_sig += 1,
                Top::DefClause(_) => self.def_clause += 1,
                Top::Var(_) => self.var += 1,
                Top::Relation(_) => self.relation += 1,
                Top::Rule(_) => self.rule += 1,
                Top::Grammar(_) => self.grammar += 1,
                Top::Other(_) => self.other += 1,
            }
        }
    }

    fn total(&self) -> usize {
        self.syntax
            + self.def_sig
            + self.def_clause
            + self.var
            + self.relation
            + self.rule
            + self.grammar
            + self.other
    }

    fn structured(&self) -> usize {
        self.total() - self.other
    }
}

fn parse_file(path: &Path) -> Result<FormCounts, String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let mut map = SourceMap::new();
    let id = map.add(path, &text);
    let tokens = lex(id, &text).map_err(|d| {
        let (line, col) = map.line_col(d.primary.file, d.primary.start);
        format!("{}:{line}:{col}: lex: {}", path.display(), d.message)
    })?;
    let tops = parse(id, tokens).map_err(|d| {
        let (line, col) = if d.primary.start == u32::MAX {
            (0, 0)
        } else {
            map.line_col(d.primary.file, d.primary.start)
        };
        format!("{}:{line}:{col}: parse: {}", path.display(), d.message)
    })?;
    let mut counts = FormCounts::default();
    counts.add(&tops);
    Ok(counts)
}

#[test]
fn parse_all_wasm_3_0_files() {
    let dir = assets_dir().join("wasm-3.0");
    let files = list_spectec_files(&dir);
    assert!(
        !files.is_empty(),
        "no .spectec files in {} — vendor missing?",
        dir.display()
    );

    let mut errors = Vec::new();
    let mut totals = FormCounts::default();
    let mut per_file: BTreeMap<String, FormCounts> = BTreeMap::new();
    for f in &files {
        match parse_file(f) {
            Ok(counts) => {
                totals.syntax += counts.syntax;
                totals.def_sig += counts.def_sig;
                totals.def_clause += counts.def_clause;
                totals.var += counts.var;
                totals.relation += counts.relation;
                totals.rule += counts.rule;
                totals.grammar += counts.grammar;
                totals.other += counts.other;
                per_file.insert(
                    f.file_name().unwrap().to_string_lossy().into_owned(),
                    counts,
                );
            }
            Err(e) => errors.push(e),
        }
    }

    if !errors.is_empty() {
        panic!("parse errors:\n{}", errors.join("\n"));
    }

    eprintln!(
        "parse_all_wasm_3_0_files: {} files; {} top-level forms ({} structured, {} other)",
        files.len(),
        totals.total(),
        totals.structured(),
        totals.other
    );
    eprintln!(
        "  syntax: {}  def_sig: {}  def_clause: {}  var: {}  relation: {}  rule: {}  grammar: {}  other: {}",
        totals.syntax,
        totals.def_sig,
        totals.def_clause,
        totals.var,
        totals.relation,
        totals.rule,
        totals.grammar,
        totals.other,
    );
    assert_eq!(
        totals.other, 0,
        "Phase 2a goal: every top-level form is structurally recognised; \
         leftover Top::Other count = {}",
        totals.other
    );
    eprintln!("per-file form counts (syn/sig/cls/var/rel/rul/gram):");
    for (name, c) in &per_file {
        eprintln!(
            "  {name:55}  {:>3}/{:>3}/{:>3}/{:>2}/{:>2}/{:>3}/{:>3}  total {}",
            c.syntax,
            c.def_sig,
            c.def_clause,
            c.var,
            c.relation,
            c.rule,
            c.grammar,
            c.total(),
        );
    }
}

#[test]
fn parse_frontend_test_file() {
    let path = assets_dir().join("test-frontend/test.spectec");
    let counts = parse_file(&path).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("frontend test.spectec: {counts:?}");
    assert!(counts.total() > 0);
}

#[test]
fn parse_middlend_test_file() {
    let path = assets_dir().join("test-middlend/test.spectec");
    let counts = parse_file(&path).unwrap_or_else(|e| panic!("{e}"));
    eprintln!("middlend test.spectec: {counts:?}");
    assert!(counts.total() > 0);
}

/// Focused: the two smallest wasm-3.0 files contain almost only syntax+def
/// and should parse with very few `Top::Other` entries (only forward decls
/// of `var`).
#[test]
fn small_wasm_files_mostly_structured() {
    let aux_num = parse_file(&assets_dir().join("wasm-3.0/0.2-aux.num.spectec")).unwrap();
    assert_eq!(
        aux_num.other, 0,
        "0.2-aux.num.spectec should be 100% structured"
    );
    assert!(aux_num.structured() > 5);

    let values = parse_file(&assets_dir().join("wasm-3.0/1.1-syntax.values.spectec")).unwrap();
    // This file uses `var b : byte` etc., so a few Top::Other entries are expected.
    assert!(
        values.structured() > values.other,
        "structured count should dominate in syntax.values"
    );
}
