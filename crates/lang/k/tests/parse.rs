//! Parser integration tests over the hand-written example `.kore` files plus
//! targeted lexical/grammar cases.

use covalence_k::ast::{Pattern, Sentence, Sort};
use covalence_k::parse::{line_col, parse_definition, parse_pattern};

const COUNTER: &str = include_str!("../examples/counter.kore");
const MINI: &str = include_str!("../examples/mini.kore");

#[test]
fn parses_counter_example() {
    let def = parse_definition(COUNTER).unwrap();
    assert_eq!(def.attrs.len(), 0);
    assert_eq!(def.modules.len(), 1);
    let m = &def.modules[0];
    assert_eq!(m.name, "COUNTER");
    // 1 import + 4 sorts + 7 symbols + 6 axioms.
    assert_eq!(m.sentences.len(), 18);
    assert_eq!(m.attrs.len(), 1);

    // Spot-check: the mangled <k>-cell constructor symbol declaration.
    let Sentence::Symbol {
        hooked,
        name,
        sort_vars,
        arg_sorts,
        ret,
        attrs,
    } = &m.sentences[5]
    else {
        panic!("expected symbol sentence, got {:?}", m.sentences[5]);
    };
    assert!(!hooked);
    assert_eq!(name, "Lbl'-LT-'k'-GT-");
    assert!(sort_vars.is_empty());
    assert_eq!(arg_sorts, &[Sort::App("SortCfg".into(), vec![])]);
    assert_eq!(ret, &Sort::App("SortCfg".into(), vec![]));
    assert_eq!(attrs.len(), 2);
}

#[test]
fn parses_mini_example() {
    let def = parse_definition(MINI).unwrap();
    assert_eq!(def.attrs.len(), 1);
    assert_eq!(def.modules.len(), 1);
    let m = &def.modules[0];
    assert_eq!(m.name, "MINI");
    assert_eq!(m.sentences.len(), 7);

    // Spot-check the alias sentence.
    let Sentence::Alias { name, lhs, rhs, .. } = &m.sentences[3] else {
        panic!("expected alias sentence, got {:?}", m.sentences[3]);
    };
    assert_eq!(name, "id");
    assert_eq!(
        lhs.as_ref(),
        &Pattern::App {
            symbol: "id".into(),
            sorts: vec![Sort::Var("S".into())],
            args: vec![Pattern::EVar("X".into(), Sort::Var("S".into()))],
        }
    );
    assert_eq!(
        rhs.as_ref(),
        &Pattern::EVar("X".into(), Sort::Var("S".into()))
    );

    // And that the last sentence is a claim.
    assert!(matches!(m.sentences[6], Sentence::Claim { .. }));
}

#[test]
fn error_carries_byte_offset() {
    // `modul` is a valid identifier but not the `module` keyword; the error
    // must point at its byte offset.
    let src = "[] modul FOO endmodule []";
    let err = parse_definition(src).unwrap_err();
    assert_eq!(err.offset, src.find("modul").unwrap());
    assert!(err.message.contains("module"), "message: {}", err.message);
    assert_eq!(line_col(src, err.offset), (1, 4));
}

#[test]
fn error_offset_line_col_multiline() {
    let src = "[]\nmodule M\n  sort S ()\nendmodule []";
    let err = parse_definition(src).unwrap_err();
    // The `(` where `{` was expected.
    assert_eq!(err.offset, src.find('(').unwrap());
    assert_eq!(line_col(src, err.offset), (3, 10));
}

#[test]
fn lexes_mangled_identifiers() {
    // Apostrophe and dash are identifier characters (K name-mangling).
    let p = parse_pattern("Lbl'-LT-'k'-GT-{}(VarX'Unds'0:SortK{})").unwrap();
    let Pattern::App {
        symbol,
        sorts,
        args,
    } = p
    else {
        panic!("expected application");
    };
    assert_eq!(symbol, "Lbl'-LT-'k'-GT-");
    assert!(sorts.is_empty());
    assert_eq!(
        args,
        vec![Pattern::EVar(
            "VarX'Unds'0".into(),
            Sort::App("SortK".into(), vec![])
        )]
    );
}

#[test]
fn multiary_and_or() {
    let sk = Sort::App("SortK".into(), vec![]);
    // Ternary \and (the post-2025-01 multiary grammar).
    let p = parse_pattern("\\and{SortK{}}(\\top{SortK{}}(), \\top{SortK{}}(), \\top{SortK{}}())")
        .unwrap();
    assert_eq!(
        p,
        Pattern::And(
            sk.clone(),
            vec![
                Pattern::Top(sk.clone()),
                Pattern::Top(sk.clone()),
                Pattern::Top(sk.clone())
            ]
        )
    );
    // Nullary \and is accepted too.
    let p = parse_pattern("\\and{SortK{}}()").unwrap();
    assert_eq!(p, Pattern::And(sk.clone(), vec![]));
    // Binary \or (the common case in older dumps).
    let p = parse_pattern("\\or{SortK{}}(\\top{SortK{}}(), \\bottom{SortK{}}())").unwrap();
    assert_eq!(
        p,
        Pattern::Or(
            sk.clone(),
            vec![Pattern::Top(sk.clone()), Pattern::Bottom(sk)]
        )
    );
}

#[test]
fn mu_takes_no_sort_parameter() {
    let sk = Sort::App("SortK".into(), vec![]);
    let p = parse_pattern("\\mu{}(@X:SortK{}, @X:SortK{})").unwrap();
    assert_eq!(
        p,
        Pattern::Mu {
            var: "@X".into(),
            var_sort: sk.clone(),
            body: Box::new(Pattern::SVar("@X".into(), sk)),
        }
    );
    // A sort parameter in the braces must be rejected.
    assert!(parse_pattern("\\mu{SortK{}}(@X:SortK{}, @X:SortK{})").is_err());
}

#[test]
fn string_escapes() {
    let p = parse_pattern("\\dv{SortString{}}(\"a\\n\\t\\\"\\\\b\\x41\")").unwrap();
    let Pattern::DV(_, lit) = p else {
        panic!("expected \\dv");
    };
    assert_eq!(lit, "a\n\t\"\\bA");
    // Unsupported escape errors cleanly.
    let err = parse_pattern("\\dv{SortString{}}(\"\\q\")").unwrap_err();
    assert!(err.message.contains("escape"), "message: {}", err.message);
}

#[test]
fn left_assoc_expands_to_nested_apps() {
    let p =
        parse_pattern("\\left-assoc{}(Lblf{}(VarA:SortK{}, VarB:SortK{}, VarC:SortK{}))").unwrap();
    let sk = Sort::App("SortK".into(), vec![]);
    let app = |args: Vec<Pattern>| Pattern::App {
        symbol: "Lblf".into(),
        sorts: vec![],
        args,
    };
    let v = |n: &str| Pattern::EVar(n.into(), sk.clone());
    assert_eq!(p, app(vec![app(vec![v("VarA"), v("VarB")]), v("VarC")]));

    let p =
        parse_pattern("\\right-assoc{}(Lblf{}(VarA:SortK{}, VarB:SortK{}, VarC:SortK{}))").unwrap();
    assert_eq!(p, app(vec![v("VarA"), app(vec![v("VarB"), v("VarC")])]));
}
