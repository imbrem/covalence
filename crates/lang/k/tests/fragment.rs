//! Fragment-classifier tests over `examples/counter.kore`.

use covalence_k::ast::{Pattern, Sentence};
use covalence_k::fragment::{AxiomClass, classify, rewrite_rules};
use covalence_k::parse::parse_definition;

const COUNTER: &str = include_str!("../examples/counter.kore");

#[test]
fn classifies_counter_axioms() {
    let def = parse_definition(COUNTER).unwrap();
    let axioms: Vec<&Sentence> = def.modules[0]
        .sentences
        .iter()
        .filter(|s| matches!(s, Sentence::Axiom { .. }))
        .collect();
    assert_eq!(axioms.len(), 6);

    let classes: Vec<AxiomClass> = axioms.iter().map(|s| classify(s)).collect();
    assert_eq!(classes[0], AxiomClass::ConstructorAxiom); // functional{}()
    assert_eq!(classes[1], AxiomClass::Subsort); // subsort{...}()
    assert_eq!(classes[2], AxiomClass::FunctionRule); // \equals equation
    for c in &classes[3..] {
        assert!(matches!(c, AxiomClass::RewriteRule(_)), "got {c:?}");
    }
}

#[test]
fn extracts_rewrite_rules() {
    let def = parse_definition(COUNTER).unwrap();
    let rules = rewrite_rules(&def);
    assert_eq!(rules.len(), 3);

    // Priorities: explicit 50, explicit 30, owise => 200.
    let priorities: Vec<u32> = rules.iter().map(|r| r.priority).collect();
    assert_eq!(priorities, vec![50, 30, 200]);

    // Labels and unique ids came from the attributes.
    assert_eq!(rules[0].label.as_deref(), Some("COUNTER.count-zero"));
    assert_eq!(rules[1].label.as_deref(), Some("COUNTER.count-step"));
    assert_eq!(rules[2].label.as_deref(), Some("COUNTER.count-owise"));
    assert_eq!(rules[0].unique_id.as_deref(), Some("id-count-zero"));

    // Ground rules: \top requires/ensures vanish.
    assert_eq!(rules[0].requires, None);
    assert_eq!(rules[0].ensures, None);
    assert_eq!(rules[2].requires, None);

    // Conditional rule: the requires is the RAW kompiled
    // \equals{SortBool{}, S}(b, \dv{SortBool{}}("true")) pattern.
    let req = rules[1].requires.as_ref().expect("count-step has requires");
    let Pattern::Equals { rhs, .. } = req else {
        panic!("expected \\equals requires, got {req:?}");
    };
    assert_eq!(
        **rhs,
        Pattern::DV(
            covalence_k::ast::Sort::App("SortBool".into(), vec![]),
            "true".into()
        )
    );
    assert_eq!(rules[1].ensures, None);

    // The stripped LHS is the configuration term (the <k> cell application).
    let Pattern::App { symbol, .. } = &rules[1].lhs else {
        panic!("expected application LHS");
    };
    assert_eq!(symbol, "Lbl'-LT-'k'-GT-");
}

#[test]
fn non_axiom_is_other() {
    let def = parse_definition(COUNTER).unwrap();
    let import = &def.modules[0].sentences[0];
    assert!(matches!(classify(import), AxiomClass::Other(_)));
}
