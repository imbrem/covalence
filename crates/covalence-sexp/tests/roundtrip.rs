use covalence_sexp::{Bytes, SExp, parse, parse_smt, prettyprint};

fn roundtrip_cov(input: &str) {
    let parsed = parse(input).unwrap();
    let mut buf = Vec::new();
    prettyprint(&parsed, &mut buf).unwrap();
    let output = String::from_utf8(buf).unwrap();
    let reparsed = parse(&output)
        .unwrap_or_else(|e| panic!("failed to reparse {input:?}: {e}\noutput: {output:?}"));
    assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
}

#[test]
fn roundtrip_atoms() {
    roundtrip_cov("foo");
    roundtrip_cov(":key");
    roundtrip_cov("42");
}

#[test]
fn roundtrip_strings() {
    roundtrip_cov(r#""hello world""#);
    roundtrip_cov(r#""a\"b\\c""#);
    roundtrip_cov(r#""line\nbreak""#);
}

#[test]
fn roundtrip_control_chars() {
    roundtrip_cov(r#""\a\b\f\v""#);
    roundtrip_cov(r#""\n\t\r""#);
    roundtrip_cov(r#""hello\"world""#);
    roundtrip_cov(r#""back\\slash""#);
}

#[test]
fn roundtrip_quoted_symbols() {
    roundtrip_cov("|hello world|");
    roundtrip_cov("|foo bar|");
}

#[test]
fn roundtrip_quoted_symbol_with_pipe() {
    roundtrip_cov(r#"|my\|piped\|symbol|"#);
}

#[test]
fn roundtrip_quoted_symbol_with_backslash() {
    roundtrip_cov(r#"|back\\slash|"#);
}

#[test]
fn roundtrip_lists() {
    roundtrip_cov("()");
    roundtrip_cov("(+ 1 2)");
    roundtrip_cov("(assert (= x 0))");
    roundtrip_cov("(set-logic QF_LIA)");
}

#[test]
fn roundtrip_smt() {
    let inputs = [
        "(set-logic QF_LIA)",
        "(declare-fun x () Int)",
        "(assert (= (+ x 1) 2))",
        "(check-sat)",
        r#"(set-info :source "test")"#,
        "(assert (not (= |foo bar| 0)))",
    ];
    for input in inputs {
        let parsed = parse_smt(input).unwrap();
        let mut buf = Vec::new();
        prettyprint(&parsed, &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();
        let reparsed = parse_smt(&output)
            .unwrap_or_else(|e| panic!("failed to reparse {input:?}: {e}\noutput: {output:?}"));
        assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
    }
}

#[test]
fn roundtrip_bytestring() {
    let input = r#"b"\xFF\x00hello""#;
    let parsed = parse(input).unwrap();
    assert_eq!(
        parsed,
        vec![SExp::ByteString(Bytes::from_static(&[
            0xFF, 0x00, b'h', b'e', b'l', b'l', b'o'
        ]))]
    );
    let mut buf = Vec::new();
    prettyprint(&parsed, &mut buf).unwrap();
    let output = String::from_utf8(buf).unwrap();
    let reparsed = parse(&output)
        .unwrap_or_else(|e| panic!("failed to reparse {input:?}: {e}\noutput: {output:?}"));
    assert_eq!(parsed, reparsed, "roundtrip mismatch for {input:?}");
}
