//! Integration tests for the `.k`-source grammar frontend (`covalence_k::kdef`)
//! against the real vendored K-tutorial fixtures (LAMBDA + IMP).

use covalence_k::kdef::ast::{Assoc, ProdItem};
use covalence_k::kdef::cfg::definition_to_cfg;
use covalence_k::kdef::parse::{line_col, parse_definition};
use covalence_k::kdef::sexpr::{definition_to_sexp, to_text};

const LAMBDA: &str = include_str!("../examples/k-tutorial/lambda.k");
const IMP: &str = include_str!("../examples/k-tutorial/imp.k");

// ---------------------------------------------------------------------------
// LAMBDA — the minimal tutorial grammar
// ---------------------------------------------------------------------------

#[test]
fn parses_lambda_grammar() {
    let def = parse_definition(LAMBDA).unwrap();
    assert!(def.requires.is_empty());
    // Two modules: LAMBDA-SYNTAX and LAMBDA.
    assert_eq!(def.modules.len(), 2);

    let syn = &def.modules[0];
    assert_eq!(syn.name, "LAMBDA-SYNTAX");
    assert_eq!(syn.imports.len(), 1);
    assert_eq!(syn.imports[0].name, "DOMAINS-SYNTAX");
    assert_eq!(syn.syntax.len(), 2); // syntax Val, syntax Exp
    assert_eq!(syn.skipped_sentences, 0);

    // `syntax Val ::= Id | "lambda" Id "." Exp` — one priority block, two prods.
    let val = &syn.syntax[0];
    assert_eq!(val.sort.name, "Val");
    assert_eq!(val.blocks.len(), 1);
    assert_eq!(val.blocks[0].prods.len(), 2);
    // First is the subsort `Val ::= Id`.
    assert_eq!(
        val.blocks[0].prods[0].subsort_of().map(|s| s.name.as_str()),
        Some("Id")
    );
    // Second is `"lambda" Id "." Exp`: terminal, nt, terminal, nt.
    let lam = &val.blocks[0].prods[1].items;
    assert_eq!(lam.len(), 4);
    assert_eq!(lam[0], ProdItem::Terminal("lambda".to_string()));
    assert!(matches!(&lam[1], ProdItem::NonTerminal { sort, .. } if sort.name == "Id"));
    assert_eq!(lam[2], ProdItem::Terminal(".".to_string()));
    assert!(matches!(&lam[3], ProdItem::NonTerminal { sort, .. } if sort.name == "Exp"));

    // `syntax Exp ::= Val | Exp Exp [left] | "(" Exp ")" [bracket]`.
    let exp = &syn.syntax[1];
    assert_eq!(exp.sort.name, "Exp");
    assert_eq!(exp.blocks.len(), 1);
    let prods = &exp.blocks[0].prods;
    assert_eq!(prods.len(), 3);
    // `Exp Exp [left]`.
    assert_eq!(prods[1].items.len(), 2);
    assert!(prods[1].attrs.iter().any(|a| a.key == "left"));
    // `"(" Exp ")" [bracket]`.
    assert!(prods[2].is_bracket());

    // The second module just imports the first.
    assert_eq!(def.modules[1].name, "LAMBDA");
    assert_eq!(def.modules[1].imports[0].name, "LAMBDA-SYNTAX");
    assert!(def.modules[1].syntax.is_empty());
}

#[test]
fn lambda_sexpr_is_stable_and_shaped() {
    let def = parse_definition(LAMBDA).unwrap();
    let text = to_text(&definition_to_sexp(&def));
    // Deterministic canonical rendering (pretty-printed); spot-check stable
    // inline fragments.
    assert!(text.contains("kdef"));
    assert!(text.contains("(requires)"));
    assert!(text.contains("(imports (import DOMAINS-SYNTAX))"));
    // The lambda constructor renders its terminal atoms and nt refs.
    assert!(text.contains(r#"(items "lambda" (nt Id) "." (nt Exp))"#));
    // Attributes ride the production.
    assert!(text.contains("(attrs left)"));
    assert!(text.contains("(attrs bracket)"));
    // The subsort `Exp ::= Val` renders as a lone nt.
    assert!(text.contains("(prod (items (nt Val)) (attrs))"));
    // Rendering is a pure function of the parse.
    assert_eq!(text, to_text(&definition_to_sexp(&def)));
}

// ---------------------------------------------------------------------------
// IMP — priority blocks, attribute lists, List{}
// ---------------------------------------------------------------------------

#[test]
fn parses_imp_grammar() {
    let def = parse_definition(IMP).unwrap();
    // IMP-SYNTAX + IMP.
    assert_eq!(def.modules.len(), 2);
    let syn = &def.modules[0];
    assert_eq!(syn.name, "IMP-SYNTAX");
    // AExp, BExp, Block, Stmt, Pgm, Ids.
    assert_eq!(syn.syntax.len(), 6);

    // AExp has TWO priority blocks (the `>` before `+`): {Int,Id,-,/,()} > {+}.
    let aexp = &syn.syntax[0];
    assert_eq!(aexp.sort.name, "AExp");
    assert_eq!(aexp.blocks.len(), 2, "AExp splits on `>` into two blocks");
    // The tighter (first) block holds the `/` production; the looser holds `+`.
    let tight_has_div = aexp.blocks[0].prods.iter().any(|p| {
        p.items
            .iter()
            .any(|i| *i == ProdItem::Terminal("/".to_string()))
    });
    let loose_has_plus = aexp.blocks[1].prods.iter().any(|p| {
        p.items
            .iter()
            .any(|i| *i == ProdItem::Terminal("+".to_string()))
    });
    assert!(
        tight_has_div && loose_has_plus,
        "`/` binds tighter than `+`"
    );

    // `AExp "/" AExp [left, strict]` — two attributes.
    let div = aexp.blocks[0]
        .prods
        .iter()
        .find(|p| {
            p.items
                .iter()
                .any(|i| *i == ProdItem::Terminal("/".to_string()))
        })
        .unwrap();
    assert!(div.attrs.iter().any(|a| a.key == "left"));
    assert!(div.attrs.iter().any(|a| a.key == "strict"));

    // `BExp "&&" BExp [left, strict(1)]` — attribute with an argument.
    let bexp = &syn.syntax[1];
    let and = bexp
        .blocks
        .iter()
        .flat_map(|b| &b.prods)
        .find(|p| {
            p.items
                .iter()
                .any(|i| *i == ProdItem::Terminal("&&".to_string()))
        })
        .unwrap();
    let strict = and.attrs.iter().find(|a| a.key == "strict").unwrap();
    assert_eq!(strict.arg.as_deref(), Some("1"));

    // `syntax Ids ::= List{Id,","}`.
    let ids = syn.syntax.iter().find(|d| d.sort.name == "Ids").unwrap();
    let list = ids.list.as_ref().expect("Ids is a List{}");
    assert!(!list.non_empty);
    assert_eq!(list.elem.name, "Id");
    assert_eq!(list.sep, ",");

    // The IMP module carries `syntax KResult ::= Int | Bool` and imports DOMAINS.
    let imp = &def.modules[1];
    assert_eq!(imp.name, "IMP");
    assert!(imp.imports.iter().any(|i| i.name == "DOMAINS"));
    assert!(imp.syntax.iter().any(|d| d.sort.name == "KResult"));
}

#[test]
fn imp_grammar_lowers_to_a_valid_cfg() {
    let def = parse_definition(IMP).unwrap();
    let cfg = definition_to_cfg(&def, "IMP-SYNTAX").unwrap().unwrap();
    // All the language sorts are present as non-terminals.
    for s in ["AExp", "BExp", "Block", "Stmt", "Pgm", "Ids"] {
        assert!(cfg.lookup(s).is_some(), "missing sort {s}");
    }
    // Ids (a List{Id,","}) desugars to ε | Id | Id "," Ids → 3 productions.
    let ids = cfg.lookup("Ids").unwrap();
    assert_eq!(cfg.productions_of(ids).count(), 3);
    // Priority is flattened: AExp collects all 6 of its productions
    // (Int, Id, "-" Int, "/", "(" AExp ")", "+") in one non-terminal.
    let aexp = cfg.lookup("AExp").unwrap();
    assert_eq!(cfg.productions_of(aexp).count(), 6);
}

// ---------------------------------------------------------------------------
// Robustness: comments, rule-skipping, associativity, errors
// ---------------------------------------------------------------------------

#[test]
fn skips_rules_and_configuration_between_syntax() {
    // A module mixing syntax with rule/configuration sentences (as lesson_8 does).
    let src = r#"
module M
  imports DOMAINS
  syntax Exp ::= Int | Exp "+" Exp  [left]
  configuration <k> $PGM:Exp </k>
  rule I1:Int + I2:Int => I1 +Int I2
  syntax Stmt ::= "skip"
endmodule
"#;
    let def = parse_definition(src).unwrap();
    let m = &def.modules[0];
    assert_eq!(m.syntax.len(), 2, "both syntax decls parsed");
    assert_eq!(m.skipped_sentences, 2, "configuration + rule skipped");
    assert_eq!(m.syntax[1].sort.name, "Stmt");
}

#[test]
fn block_level_associativity_tag() {
    // `left:` prefixing a priority block.
    let src = r#"
module M
  syntax E ::= "x"
             > left: E "+" E
                   | E "-" E
endmodule
"#;
    let def = parse_definition(src).unwrap();
    let e = &def.modules[0].syntax[0];
    assert_eq!(e.blocks.len(), 2);
    assert_eq!(e.blocks[1].assoc, Some(Assoc::Left));
    assert_eq!(e.blocks[1].prods.len(), 2);
}

#[test]
fn comments_are_ignored() {
    let src = "// a line comment\nmodule M /* block */ syntax E ::= \"x\" endmodule\n";
    let def = parse_definition(src).unwrap();
    assert_eq!(def.modules[0].syntax.len(), 1);
}

#[test]
fn error_reports_a_byte_offset() {
    // Missing `endmodule`.
    let src = "module M\n  syntax E ::= \"x\"\n";
    let err = parse_definition(src).unwrap_err();
    assert!(err.offset <= src.len());
    let (line, _col) = line_col(src, err.offset);
    assert!(line >= 1);
}

#[test]
fn labelled_nonterminal() {
    // `name:` field label on a non-terminal.
    let src = "module M syntax Pair ::= \"<\" first: Exp \",\" second: Exp \">\" endmodule";
    let def = parse_definition(src).unwrap();
    let items = &def.modules[0].syntax[0].blocks[0].prods[0].items;
    let labels: Vec<_> = items
        .iter()
        .filter_map(|i| match i {
            ProdItem::NonTerminal { label, .. } => label.as_deref(),
            _ => None,
        })
        .collect();
    assert_eq!(labels, vec!["first", "second"]);
}
