//! `.mm` file parsing (the uncompressed-subset stretch goal): read a small
//! hand-written `.mm` from disk, parse it, and round-trip it.
//!
//! "Round-trip" here means: parse the source, then re-emit a normalised `.mm`
//! from the parsed [`covalence_metamath::Database`], parse *that*, and confirm
//! both databases verify and agree on their assertions. We have no canonical
//! serializer in the crate yet (north star), so the test ships a minimal
//! emitter local to the test.

use covalence_metamath::{Database, Proof, Statement, parse, verify_all};

const FIXTURE: &str = include_str!("fixtures/demo0.mm");

#[test]
fn parse_mm_file_and_verify() {
    let db = parse(FIXTURE).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 1);
    assert!(db.statement_by_label("th1").is_some());
    assert!(db.statement_by_label("mp").is_some());
}

#[test]
fn roundtrip_through_emitter() {
    let db1 = parse(FIXTURE).unwrap();
    let emitted = emit(&db1);
    let db2 = parse(&emitted).unwrap_or_else(|e| panic!("re-parse failed: {e}\n---\n{emitted}"));

    // Both verify.
    assert_eq!(verify_all(&db1).unwrap(), 1);
    assert_eq!(verify_all(&db2).unwrap(), 1);

    // The assertion sets agree (label + conclusion).
    let mut a1: Vec<_> = db1
        .assertions()
        .map(|a| (a.label.clone(), a.conclusion.clone()))
        .collect();
    let mut a2: Vec<_> = db2
        .assertions()
        .map(|a| (a.label.clone(), a.conclusion.clone()))
        .collect();
    a1.sort_by(|x, y| x.0.cmp(&y.0));
    a2.sort_by(|x, y| x.0.cmp(&y.0));
    assert_eq!(a1, a2);
}

/// A minimal `.mm` emitter (test-local; the canonical one is a north star).
fn emit(db: &Database) -> String {
    use covalence_metamath::expr_symbols;
    let mut out = String::new();
    for stmt in db.statements() {
        match stmt {
            Statement::Constant(syms) => {
                out.push_str(&format!("$c {} $.\n", syms.join(" ")));
            }
            Statement::Variable(syms) => {
                out.push_str(&format!("$v {} $.\n", syms.join(" ")));
            }
            Statement::Float(f) => {
                out.push_str(&format!("{} $f {} {} $.\n", f.label, f.typecode, f.var));
            }
            Statement::Essential(h) => {
                let body = expr_symbols(&h.expr).unwrap().join(" ");
                out.push_str(&format!("{} $e {} $.\n", h.label, body));
            }
            Statement::Disjoint(vars) => {
                out.push_str(&format!("$d {} $.\n", vars.join(" ")));
            }
            Statement::Assert(a) => {
                let body = expr_symbols(&a.conclusion).unwrap().join(" ");
                match &a.proof {
                    None => out.push_str(&format!("{} $a {} $.\n", a.label, body)),
                    Some(Proof::Normal(p)) => {
                        out.push_str(&format!("{} $p {} $= {} $.\n", a.label, body, p.join(" ")))
                    }
                    Some(Proof::Compressed { labels, letters }) => out.push_str(&format!(
                        "{} $p {} $= ( {} ) {} $.\n",
                        a.label,
                        body,
                        labels.join(" "),
                        String::from_utf8_lossy(letters),
                    )),
                }
            }
        }
    }
    // The emitter above ignores ${ $} nesting; re-insert a block around the
    // essential hypotheses + their assertion so scoping round-trips. For demo0
    // the only scoped group is `mp`; wrap any Essential...Assert run.
    wrap_scopes(&out)
}

/// Wrap runs of `$e` hypotheses and the following assertion in `${ ... $}` so
/// that scoping is preserved on re-parse. (demo0 has exactly one such run.)
fn wrap_scopes(flat: &str) -> String {
    let mut out = String::new();
    let mut lines = flat.lines().peekable();
    while let Some(line) = lines.next() {
        if line.contains(" $e ") {
            out.push_str("${\n");
            out.push_str(line);
            out.push('\n');
            // Consume subsequent $e lines and the closing assertion.
            while let Some(&next) = lines.peek() {
                out.push_str(next);
                out.push('\n');
                lines.next();
                if next.contains(" $a ") || next.contains(" $p ") {
                    break;
                }
            }
            out.push_str("$}\n");
        } else {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}
