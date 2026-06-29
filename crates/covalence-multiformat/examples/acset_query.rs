//! Conjunctive queries over the interchange ACSet — the data-oriented
//! (Datalog-flavoured) reading of a `FactStore`.
//!
//! We ask the store a relational question directly: *"which geometric facts cite
//! a classical-HOL fact?"* — i.e. find a citation edge `e` with `fc_src(e) = g`,
//! `fc_dst(e) = h`, `g.fact_logic = geometric`, `h.fact_logic = HOL`. The answer
//! is a homomorphism from that pattern into the instance: exactly the
//! cross-kernel bridge, recovered by query rather than by hand.
//!
//! Run:  `cargo run -p covalence-multiformat --example acset_query`

use covalence_multiformat::acset::{Query, instance_of, ob};
use covalence_multiformat::{Cid, DerivationFact, FactStore, codec};

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

fn main() {
    println!("covalence-multiformat — conjunctive queries over the interchange ACSet\n");

    // A small store: a classical-HOL theorem, plus two geometric sequents that
    // import it (and one that does not).
    let hol = DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical"),
        prop_codec: codec::COV_HOL_THM,
        prop: b"|- x = x".to_vec(),
        assumptions: vec![],
        derivation: Cid::of(codec::MM_DERIVATION, b"derivation:refl"),
    };
    let hol_cid = hol.cid();
    let importer = |name: &[u8], imports: Option<Cid>| {
        let mut assumptions = vec![Cid::of(codec::AXIOM_SET, b"assumption:classical/LEM")];
        if let Some(c) = imports {
            assumptions.push(c);
        }
        DerivationFact {
            logic: codec::logic::GEOMETRIC,
            axioms: Cid::of(codec::AXIOM_SET, b"theory:geometric-base"),
            prop_codec: codec::COLN_GEOM_SEQ,
            prop: name.to_vec(),
            assumptions,
            derivation: Cid::of(codec::MM_DERIVATION, b"derivation:glue"),
        }
    };
    let imports = importer(b"x:Comm |- mul-commutes(x)", Some(hol_cid));
    let standalone = importer(b"x:Mon |- unit-unique(x)", None);

    let mut store = FactStore::new();
    store.put(&hol);
    store.put(&imports);
    store.put(&standalone);
    let inst = instance_of(&store).expect("store decodes");

    section("query: geometric facts that cite a classical-HOL fact");
    println!("  e:FactCite, g:Fact, h:Fact");
    println!("  fc_src(e)=g  ∧  fc_dst(e)=h  ∧  g.fact_logic=geometric  ∧  h.fact_logic=HOL");

    let q = Query::builder()
        .var("e", ob::FACT_CITE)
        .var("g", ob::FACT)
        .var("h", ob::FACT)
        .hom("e", "fc_src", "g")
        .hom("e", "fc_dst", "h")
        .attr_eq(
            "g",
            "fact_logic",
            codec::logic::name(codec::logic::GEOMETRIC),
        )
        .attr_eq("h", "fact_logic", codec::logic::name(codec::logic::HOL))
        .build();
    assert_eq!(q.check(inst.schema()), Ok(()));

    let answers = inst.query(&q);
    println!("\n  {} match(es):", answers.len());
    for m in &answers {
        let g = m.get("g").and_then(|p| inst.label(p)).unwrap_or("?");
        let h = m.get("h").and_then(|p| inst.label(p)).unwrap_or("?");
        println!("    geometric {g}\n        cites HOL {h}");
    }
    println!("\n  (the standalone geometric sequent is correctly excluded — it cites no HOL fact)");

    section("what this is");
    println!("  a conjunctive query = a pattern; an answer = a homomorphism into the instance.");
    println!("  chained foreign keys evaluate as joins. This is the relational / Datalog");
    println!("  reading of the same ACSet the structural validator checks.");
}
