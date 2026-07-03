//! Recursive (Datalog) queries over the interchange ACSet: the **transitive
//! closure of citations** — every fact a proof transitively depends on.
//!
//! `edge(g,h) :- fc_src(e)=g, fc_dst(e)=h`  (g directly cites h)
//! `reach(a,b) :- edge(a,b)`
//! `reach(a,c) :- edge(a,b), reach(b,c)`  (recursion = the fixpoint)
//!
//! Run:  `cargo run -p covalence-multiformat --example acset_datalog`

use covalence_multiformat::acset::{Part, Program, Rule, instance_of, ob};
use covalence_multiformat::{Cid, DerivationFact, FactStore, codec};

fn section(title: &str) {
    println!("\n\x1b[1m{title}\x1b[0m");
    println!("{}", "─".repeat(title.chars().count()));
}

/// A HOL fact named `prop`, optionally citing another fact by CID.
fn fact(prop: &[u8], cites: Option<Cid>) -> DerivationFact {
    let mut assumptions = Vec::new();
    if let Some(c) = cites {
        assumptions.push(c);
    }
    DerivationFact {
        logic: codec::logic::HOL,
        axioms: Cid::of(codec::AXIOM_SET, b"theory:HOL-classical"),
        prop_codec: codec::COV_HOL_THM,
        prop: prop.to_vec(),
        assumptions,
        derivation: Cid::of(codec::MM_DERIVATION, prop), // distinct witness per fact
    }
}

fn main() {
    println!("covalence-multiformat — recursive (Datalog) queries over the interchange\n");

    // A citation chain A → B → C → D (each fact cites the previous one's CID).
    // Build leaf-first so each citation target already has an address.
    let d = fact(b"|- D", None);
    let c = fact(b"|- C", Some(d.cid()));
    let b = fact(b"|- B", Some(c.cid()));
    let a = fact(b"|- A", Some(b.cid()));

    let mut store = FactStore::new();
    for f in [&a, &b, &c, &d] {
        store.put(f);
    }
    let inst = instance_of(&store).expect("store decodes");
    let label = |p| inst.label(p).map(short).unwrap_or_else(|| "?".into());

    // edge(a,b) :- fc_src(e)=a, fc_dst(e)=b ; reach = transitive closure.
    let prog = Program::builder()
        .relation("edge", &[ob::FACT, ob::FACT])
        .relation("reach", &[ob::FACT, ob::FACT])
        .rule(
            Rule::builder()
                .var("e", ob::FACT_CITE)
                .var("a", ob::FACT)
                .var("b", ob::FACT)
                .head("edge", &["a", "b"])
                .hom("e", "fc_src", "a")
                .hom("e", "fc_dst", "b")
                .build(),
        )
        .rule(
            Rule::builder()
                .var("a", ob::FACT)
                .var("b", ob::FACT)
                .head("reach", &["a", "b"])
                .rel("edge", &["a", "b"])
                .build(),
        )
        .rule(
            Rule::builder()
                .var("a", ob::FACT)
                .var("b", ob::FACT)
                .var("c", ob::FACT)
                .head("reach", &["a", "c"])
                .rel("edge", &["a", "b"])
                .rel("reach", &["b", "c"])
                .build(),
        )
        .build();
    assert_eq!(prog.check(inst.schema()), Ok(()));

    let sol = inst.solve(&prog);

    section("direct citations  edge(a,b)");
    for t in sorted(sol.tuples("edge"), &label) {
        println!("  {} → {}", label(t[0]), label(t[1]));
    }

    section("transitive dependencies  reach(a,b)  (least fixpoint)");
    println!(
        "  {} direct edges ⇒ {} reachable pairs",
        sol.len("edge"),
        sol.len("reach")
    );
    for t in sorted(sol.tuples("reach"), &label) {
        let tag = if !sol.contains("edge", t) {
            "  (transitive)"
        } else {
            ""
        };
        println!("  {} ⇝ {}{tag}", label(t[0]), label(t[1]));
    }

    section("where Datafun comes in");
    println!("  this fixpoint = a monotone map on a set-lattice iterated to its lfp.");
    println!("  a Datafun surface (monotone types + `fix`) would compile to exactly this,");
    println!("  with termination/monotonicity guaranteed by typing rather than assumed.");
    println!("  see notes/vibes/sketches/acset-datalog-datafun.md");
}

fn short(s: &str) -> String {
    // "...#aaaaaaaa…zzzz" style is already short via Display, but labels are the
    // full wire CID; show the statement-bearing tail compactly.
    let n = s.len();
    if n > 12 {
        format!("…{}", &s[n - 8..])
    } else {
        s.into()
    }
}

fn sorted<'a>(
    it: impl Iterator<Item = &'a Vec<Part>>,
    label: &impl Fn(Part) -> String,
) -> Vec<&'a Vec<Part>> {
    let mut v: Vec<_> = it.collect();
    v.sort_by_key(|t| (label(t[0]), label(t[1])));
    v
}
