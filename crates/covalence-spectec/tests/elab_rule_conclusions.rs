//! Apply the OpTable to every `rule` conclusion in the wasm-3.0 corpus.
//!
//! Phase 2c-ii acceptance: for each rule in the combined spec, look up
//! its relation by name and elaborate the conclusion expression. Count
//! successes, classify failures, and assert the overall success rate.

use std::collections::BTreeMap;
use std::path::PathBuf;

use covalence_spectec::{
    cst::Top,
    elab::{ElabPremise, Expr, build_table, elab_rule_conclusion},
    lex::lex,
    parse::parse,
    source::SourceMap,
};

fn assets_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("assets/spectec")
}

#[test]
fn elab_all_rule_conclusions_in_wasm_3_0() {
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

    let mut total_rules = 0usize;
    let mut ok = 0usize;
    let mut err_by_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut shape_histogram: BTreeMap<usize, usize> = BTreeMap::new();
    let mut shape_by_first_expr: BTreeMap<String, usize> = BTreeMap::new();
    let mut all_operand_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut total_premises = 0usize;
    let mut premise_kind: BTreeMap<&str, usize> = BTreeMap::new();

    for top in &all_tops {
        if let Top::Rule(r) = top {
            total_rules += 1;
            match elab_rule_conclusion(r, &ctx) {
                Ok(elab) => {
                    ok += 1;
                    *shape_histogram.entry(elab.operands.len()).or_insert(0) += 1;
                    let kind = expr_kind(elab.operands.first());
                    *shape_by_first_expr.entry(kind.to_string()).or_insert(0) += 1;
                    for operand in &elab.operands {
                        let k = expr_kind(Some(operand));
                        *all_operand_kind.entry(k.to_string()).or_insert(0) += 1;
                    }
                    for p in &elab.premises {
                        total_premises += 1;
                        *premise_kind.entry(premise_kind_name(p)).or_insert(0) += 1;
                    }
                }
                Err(d) => {
                    let key = error_prefix(&d.message);
                    *err_by_kind.entry(key).or_insert(0) += 1;
                }
            }
        }
    }

    eprintln!("elaborated {ok}/{total_rules} rule conclusions");
    eprintln!("operand-count histogram:");
    for (n, c) in &shape_histogram {
        eprintln!("  {n} operand(s): {c} rules");
    }
    eprintln!("first-operand kind:");
    for (k, c) in &shape_by_first_expr {
        eprintln!("  {k}: {c}");
    }
    let total_operands: usize = all_operand_kind.values().sum();
    eprintln!("all-operand kinds ({total_operands} total):");
    for (k, c) in &all_operand_kind {
        eprintln!("  {k}: {c}");
    }
    eprintln!("premises total: {total_premises}");
    for (k, c) in &premise_kind {
        eprintln!("  {k}: {c}");
    }
    if !err_by_kind.is_empty() {
        eprintln!("error buckets:");
        for (k, c) in &err_by_kind {
            eprintln!("  {c:>4}  {k}");
        }
    }

    assert!(total_rules > 200, "expected many rules in wasm-3.0 corpus");
    assert!(
        ok * 2 >= total_rules,
        "Phase 2c-ii goal: at least half of rule conclusions elaborate; \
         got {ok}/{total_rules}"
    );
}

fn premise_kind_name(p: &ElabPremise) -> &'static str {
    match p {
        ElabPremise::Rule { .. } => "Rule",
        ElabPremise::If(_) => "If",
        ElabPremise::Let { .. } => "Let",
        ElabPremise::Else => "Else",
        ElabPremise::Iter { .. } => "Iter",
        ElabPremise::Unelaborated { .. } => "Unelaborated",
    }
}

fn expr_kind(e: Option<&Expr>) -> &'static str {
    match e {
        None => "(none)",
        Some(Expr::Var { .. }) => "Var",
        Some(Expr::Bool { .. }) => "Bool",
        Some(Expr::Num { .. }) => "Num",
        Some(Expr::Text { .. }) => "Text",
        Some(Expr::Un { .. }) => "Un",
        Some(Expr::Bin { .. }) => "Bin",
        Some(Expr::Cmp { .. }) => "Cmp",
        Some(Expr::Idx { .. }) => "Idx",
        Some(Expr::Slice { .. }) => "Slice",
        Some(Expr::Upd { .. }) => "Upd",
        Some(Expr::Ext { .. }) => "Ext",
        Some(Expr::Str { .. }) => "Str",
        Some(Expr::Dot { .. }) => "Dot",
        Some(Expr::Comp { .. }) => "Comp",
        Some(Expr::Mem { .. }) => "Mem",
        Some(Expr::Len { .. }) => "Len",
        Some(Expr::Tup { .. }) => "Tup",
        Some(Expr::Call { .. }) => "Call",
        Some(Expr::Iter { .. }) => "Iter",
        Some(Expr::Proj { .. }) => "Proj",
        Some(Expr::Case { .. }) => "Case",
        Some(Expr::Uncase { .. }) => "Uncase",
        Some(Expr::Opt { .. }) => "Opt",
        Some(Expr::Unopt { .. }) => "Unopt",
        Some(Expr::List { .. }) => "List",
        Some(Expr::Lift { .. }) => "Lift",
        Some(Expr::Cat { .. }) => "Cat",
        Some(Expr::Cvt { .. }) => "Cvt",
        Some(Expr::Sub { .. }) => "Sub",
        Some(Expr::Eps { .. }) => "Eps",
        Some(Expr::Unelaborated { .. }) => "Unelaborated",
    }
}

fn error_prefix(msg: &str) -> String {
    // Group "rule X foo" type messages by stripping the rule name.
    if let Some(rest) = msg.strip_prefix("rule `")
        && let Some(end) = rest.find("` ")
    {
        return format!("rule `…`{}", &rest[end + 1..]);
    }
    msg.chars().take(80).collect()
}
