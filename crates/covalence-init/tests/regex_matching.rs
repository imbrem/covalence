//! Integration tests for the regex → byte-predicate matching tactic
//! ([`covalence_init::grammar::regex`]), driven entirely through the public API.
//!
//! The centrepiece is a differential test against an **independent** reference
//! recogniser ([`oracle`]) written over the *surface* `Regex<u8>` — a different
//! implementation from the compiled matcher (which works on the desugared
//! `Core`), so agreement cross-checks the whole pipeline: desugaring, the
//! recognizer, and proof construction.

use covalence_grammar::regex::{Class, Regex, parse_regex_u8};
use covalence_init::Term;
use covalence_init::grammar::regex::tactic::{Word, prove_matches, prove_member, prove_word};
use covalence_init::grammar::regex::{compile, desugar};
use covalence_init::init::ext::TermExt;
use covalence_init::init::regex as ir;

// ============================================================================
// Helpers.
// ============================================================================

fn re(src: &str) -> Regex<u8> {
    parse_regex_u8(src).unwrap_or_else(|e| panic!("parse {src:?}: {e}"))
}

/// A proved theorem with no hypotheses and no observer/oracle dependence.
#[track_caller]
fn assert_clean(thm: &covalence_init::Thm) {
    assert!(thm.hyps().is_empty(), "expected no hypotheses");
    assert!(thm.has_no_obs(), "expected an oracle-free theorem");
}

// ----------------------------------------------------------------------------
// Independent reference recogniser over the surface `Regex<u8>`.
// ----------------------------------------------------------------------------

/// The set of prefix lengths of `w` that `r` can consume from offset 0. `r`
/// matches `w` exactly iff `w.len()` is in the returned set.
fn consume(r: &Regex<u8>, w: &[u8]) -> std::collections::BTreeSet<usize> {
    use std::collections::BTreeSet;
    let unit = |n: usize| BTreeSet::from([n]);
    match r {
        Regex::Empty => BTreeSet::new(),
        Regex::Eps => unit(0),
        Regex::Lit(b) => {
            if w.first() == Some(b) {
                unit(1)
            } else {
                BTreeSet::new()
            }
        }
        Regex::Class(c) => match w.first() {
            Some(&b) if class_has(c, b) => unit(1),
            _ => BTreeSet::new(),
        },
        Regex::Concat(items) => {
            let mut reach = unit(0);
            for item in items {
                let mut next = BTreeSet::new();
                for &n in &reach {
                    for m in consume(item, &w[n..]) {
                        next.insert(n + m);
                    }
                }
                reach = next;
                if reach.is_empty() {
                    break;
                }
            }
            reach
        }
        Regex::Alt(items) => items.iter().flat_map(|it| consume(it, w)).collect(),
        Regex::Star(inner) => star_consume(inner, w),
        Regex::Plus(inner) => {
            // L(r+) = L(r r*): consume one `inner`, then the star.
            let mut out = BTreeSet::new();
            for n in consume(inner, w) {
                for m in star_consume(inner, &w[n..]) {
                    out.insert(n + m);
                }
            }
            out
        }
        Regex::Opt(inner) => {
            let mut s = consume(inner, w);
            s.insert(0);
            s
        }
        Regex::Rep { inner, min, max } => {
            let min = *min as usize;
            // For unbounded, more than `min + |w|` copies cannot reach a new
            // position (each progressing copy eats >=1 byte).
            let cap = max.map_or(min + w.len() + 1, |m| m as usize);
            let mut reach = unit(0); // positions after exactly `c` copies
            let mut out = BTreeSet::new();
            if min == 0 {
                out.insert(0);
            }
            for c in 1..=cap {
                let mut next = BTreeSet::new();
                for &n in &reach {
                    for m in consume(inner, &w[n..]) {
                        next.insert(n + m);
                    }
                }
                if next.is_empty() {
                    break;
                }
                reach = next;
                if c >= min {
                    out.extend(reach.iter().copied());
                }
            }
            out
        }
    }
}

fn star_consume(inner: &Regex<u8>, w: &[u8]) -> std::collections::BTreeSet<usize> {
    use std::collections::BTreeSet;
    let mut reach = BTreeSet::from([0usize]);
    let mut frontier = vec![0usize];
    while let Some(n) = frontier.pop() {
        for m in consume(inner, &w[n..]) {
            if m == 0 {
                continue; // no progress — already represented by `reach`
            }
            let p = n + m;
            if reach.insert(p) {
                frontier.push(p);
            }
        }
    }
    reach
}

fn class_has(c: &Class<u8>, b: u8) -> bool {
    let inside = c.ranges.iter().any(|r| r.lo <= b && b <= r.hi);
    inside != c.negated
}

fn oracle_matches(r: &Regex<u8>, w: &[u8]) -> bool {
    consume(r, w).contains(&w.len())
}

// ============================================================================
// Input-type ergonomics: prove_matches accepts any AsRef<[u8]>.
// ============================================================================

#[test]
fn accepts_str_and_other_byte_like_inputs() {
    let r = re("abc");
    // &str — the headline new capability.
    assert!(prove_matches(&r, "abc").unwrap().is_some());
    // String, &String.
    let owned = String::from("abc");
    assert!(prove_matches(&r, &owned).unwrap().is_some());
    assert!(prove_matches(&r, owned.clone()).unwrap().is_some());
    // &[u8], Vec<u8>, array, byte-string literal.
    assert!(prove_matches(&r, b"abc".as_slice()).unwrap().is_some());
    assert!(prove_matches(&r, vec![b'a', b'b', b'c']).unwrap().is_some());
    assert!(prove_matches(&r, [b'a', b'b', b'c']).unwrap().is_some());
    assert!(prove_matches(&r, b"abc").unwrap().is_some());
    // prove_member is likewise generic over the input type (use a non-matching
    // input here — the matching path runs the slow soundness proof, exercised
    // by the `#[ignore]`d `member_chains_to_language_membership`).
    assert!(prove_member(&re("a|b"), "c").unwrap().is_none());
}

// ============================================================================
// Exact conclusions — the proved theorem is the expected `Matches ⌜r⌝ w`.
// ============================================================================

#[test]
fn conclusion_is_matches_of_compiled_regex() {
    let a = ir::u8_alphabet();
    let nil = covalence_init::init::list::nil(a.clone());

    // `eps` against the empty input proves `Matches ⌜eps⌝ nil`.
    let thm = prove_matches(&re(""), "").unwrap().unwrap();
    let expected = ir::matches(&a, &compile(&re("")), &nil).unwrap();
    assert_eq!(thm.concl(), &expected);
    assert_clean(&thm);

    // `a` against "a" proves `Matches ⌜lit a⌝ [a]`.
    let one_a = covalence_init::init::list::cons(a.clone())
        .apply(Term::u8_lit(b'a'))
        .unwrap()
        .apply(nil)
        .unwrap();
    let thm = prove_matches(&re("a"), "a").unwrap().unwrap();
    let expected = ir::matches(&a, &compile(&re("a")), &one_a).unwrap();
    assert_eq!(thm.concl(), &expected);

    // The compiled term is exactly the desugared `Core`'s cached `⌜c⌝`.
    assert_eq!(compile(&re("a")), *desugar(&re("a")).term());
}

// ============================================================================
// Differential against the independent oracle, over a broad corpus.
// ============================================================================

#[test]
fn agrees_with_oracle_on_corpus() {
    // (regex, inputs). Inputs are kept short because the matching cases build a
    // kernel proof each.
    let corpus: &[(&str, &[&str])] = &[
        ("", &["", "a"]),
        ("a", &["", "a", "b", "aa"]),
        ("abc", &["abc", "ab", "abcd", "abd", ""]),
        ("a|b|c", &["a", "b", "c", "d", "ab", ""]),
        ("a*", &["", "a", "aaaa", "b", "aab"]),
        ("a+", &["", "a", "aaa", "ba", "ab"]),
        ("a?", &["", "a", "aa"]),
        ("(?:ab)*", &["", "ab", "abab", "aba", "a"]),
        ("(?:a|b)c*", &["a", "ac", "bccc", "cc", ""]),
        ("[a-c]+", &["a", "abccba", "", "abx", "d"]),
        ("[^a-c]+", &["x", "xyz", "a", "xa", ""]),
        ("a{3}", &["aaa", "aa", "aaaa", ""]),
        ("a{2,3}", &["a", "aa", "aaa", "aaaa"]),
        ("a{2,}", &["a", "aa", "aaaaa"]),
        ("(?:a?)b", &["b", "ab", "aab"]),
        ("x(?:a|bb)*y", &["xy", "xay", "xbby", "xababby", "xby"]),
        ("a*a*", &["", "a", "aaaa", "b"]),
        ("(?:a?)*", &["", "a", "aa", "ab"]), // nullable inner star
        (".", &["a", "", "ab"]),
        (".*", &["", "ab", "hi"]),
    ];

    for (src, inputs) in corpus {
        let r = re(src);
        for input in *inputs {
            let bytes = input.as_bytes();
            let got = prove_matches(&r, bytes).unwrap();
            let expected = oracle_matches(&r, bytes);
            assert_eq!(
                got.is_some(),
                expected,
                "mismatch: regex {src:?} on input {input:?} \
                 (matcher: {}, oracle: {expected})",
                got.is_some(),
            );
            // Whenever it matches, the proof is clean.
            if let Some(thm) = got {
                assert_clean(&thm);
            }
        }
    }
}

#[test]
fn empty_regex_matches_nothing() {
    // `Regex::Empty` has empty language — not even the empty input matches.
    let r = Regex::<u8>::Empty;
    assert!(prove_matches(&r, "").unwrap().is_none());
    assert!(prove_matches(&r, "a").unwrap().is_none());
    assert!(!oracle_matches(&r, b""));
}

#[test]
fn star_of_nullable_inner_terminates_and_matches() {
    // `(?:a?)*` — the inner matches the empty string; the matcher must not loop
    // and must still match runs of `a`.
    let r = re("(?:a?)*");
    for input in ["", "a", "aaaaa"] {
        assert!(
            prove_matches(&r, input).unwrap().is_some(),
            "should match {input:?}",
        );
    }
    assert!(prove_matches(&r, "b").unwrap().is_none());
}

#[test]
fn full_byte_class_is_shallow_proof() {
    // `.` is a 256-way alternation; the balanced-alt encoding keeps the proof
    // shallow. Confirm it proves a high byte matches.
    let thm = prove_matches(&re("."), b"\xC0").unwrap().unwrap();
    assert_clean(&thm);
}

#[test]
fn wasm_preamble_matches() {
    // The real WASM magic + version, proved against the literal bytes.
    let r = covalence_spectec::grammar::simple::wasm_preamble();
    let good = [0x00, b'a', b's', b'm', 0x01, 0x00, 0x00, 0x00];
    let thm = prove_matches(&r, good).unwrap().unwrap();
    assert_clean(&thm);
    // A wrong version byte fails.
    let bad = [0x00, b'a', b's', b'm', 0x02, 0x00, 0x00, 0x00];
    assert!(prove_matches(&r, bad).unwrap().is_none());
}

// ============================================================================
// Soundness chaining — membership in the denoted language.
// ============================================================================

// `prove_member` chains `init::regex::soundness_at`, whose `lang`-discharge is
// very slow (minutes for a single call — see the regex `SKELETONS.md`). The
// no-match path is cheap, but the membership proof is opt-in via `--ignored` so
// the default run stays fast.
#[test]
fn member_no_match_is_none() {
    assert!(prove_member(&re("a|b"), "c").unwrap().is_none());
}

#[test]
#[ignore = "first prove_member call runs the slow soundness `lang`-discharge (~minutes); see regex SKELETONS"]
fn member_chains_to_language_membership() {
    // `a|b` against "a" lands `⊢ mem [a] ⟦a|b⟧`. The first call warms the
    // cached byte-alphabet `Closed D` proof.
    let thm = prove_member(&re("a|b"), "a").unwrap().unwrap();
    assert_clean(&thm);

    // A *different* regex and word: this reuses the same cached `Closed D`
    // (it is input-independent), so it returns quickly rather than re-running
    // the discharge — the amortisation the cache buys.
    let thm = prove_member(&re("xy*"), "xyy").unwrap().unwrap();
    assert_clean(&thm);
}

// ============================================================================
// Word expressions — concatenation and "parses-as" variables.
// ============================================================================

#[test]
fn word_without_variables_matches_like_bytes() {
    let w = Word::cat(Word::bytes("ab"), Word::Byte(b'c'));
    let thm = prove_word(&re("abc"), &w).unwrap().unwrap();
    assert_clean(&thm);
    // Nil word against eps.
    let thm = prove_word(&re(""), &Word::Nil).unwrap().unwrap();
    assert_clean(&thm);
}

#[test]
fn word_variable_discharges_by_assumption() {
    // Goal `0x00 X` where X parses as `[a-c]+`; the variable is consumed against
    // the single assumption `Matches ⌜[a-c]+⌝ X`.
    let cat = re("[a-c]+");
    let r = Regex::concat([Regex::Lit(0x00u8), cat.clone()]);
    let w = Word::cat(Word::Byte(0x00), Word::var("X", cat));
    let thm = prove_word(&r, &w).unwrap().unwrap();
    assert_eq!(thm.hyps().len(), 1, "exactly the parses-as assumption");
    assert!(thm.has_no_obs());
}

#[test]
fn word_two_variables_under_star() {
    // `(a|b)*` against two variable tokens, both of category `a|b`.
    let cat = re("a|b");
    let r = cat.clone().star();
    let w = Word::cat(Word::var("X", cat.clone()), Word::var("Y", cat));
    let thm = prove_word(&r, &w).unwrap().unwrap();
    assert_eq!(
        thm.hyps().len(),
        2,
        "two distinct variables -> two assumptions"
    );
    assert!(thm.has_no_obs());
}

#[test]
fn word_repeated_variable_shares_one_assumption() {
    // The same variable name twice shares one free var and one assumption.
    let cat = re("a|b");
    let r = cat.clone().star();
    let w = Word::cat(Word::var("X", cat.clone()), Word::var("X", cat));
    let thm = prove_word(&r, &w).unwrap().unwrap();
    assert_eq!(thm.hyps().len(), 1, "repeated variable -> one assumption");
}

#[test]
fn word_variable_category_mismatch_fails() {
    // A variable of category `a|b` cannot satisfy a goal that wants `c`.
    let r = re("c");
    let w = Word::var("X", re("a|b"));
    assert!(prove_word(&r, &w).unwrap().is_none());
}

// ============================================================================
// Timing harness for more involved regexes. Ignored by default; run with:
//   cargo test -p covalence-hol --test regex_matching -- --ignored --nocapture timing
// ============================================================================

#[test]
#[ignore = "timing harness; run explicitly with --nocapture"]
fn timing_involved_regexes() {
    use covalence_init::grammar::regex::Core;
    use std::time::Instant;

    // (label, regex source, a matching input). Each `prove_matches` builds a
    // kernel proof whose size tracks the input, so these surface how proof time
    // scales with input length and regex shape.
    let cases: &[(&str, &str, &str)] = &[
        (
            "identifier",
            r"[a-zA-Z_][a-zA-Z0-9_]*",
            "myVariable_Name123",
        ),
        (
            "ipv4-ish",
            r"[0-9]{1,3}(?:[.][0-9]{1,3}){3}",
            "192.168.100.1",
        ),
        ("hex-bytes", r"(?:[0-9a-f][0-9a-f])+", "deadbeefcafe"),
        (
            "lower-run-40",
            r"[a-z]+",
            "abcdefghijklmnopqrstuvwxyzabcdefghijklmn",
        ),
        ("alt-star", r"(?:foo|bar|baz)+", "foobarbazfoobarbaz"),
        (
            "csv-ish",
            r"[a-z]+(?:,[a-z]+)*",
            "alpha,beta,gamma,delta,epsilon",
        ),
        ("rep-10", r"a{10}", "aaaaaaaaaa"),
        ("nested-semis", r"(?:[a-c]+;)+", "ab;cba;a;bbbb;"),
    ];

    eprintln!(
        "\n{:<14} {:>4} {:>11} {:>11}",
        "regex", "len", "compile", "prove"
    );
    for (label, src, input) in cases {
        let t0 = Instant::now();
        let r = Core::parse(src).unwrap_or_else(|e| panic!("parse {src:?}: {e:?}"));
        let compile_us = t0.elapsed().as_secs_f64() * 1e6;

        let t1 = Instant::now();
        let thm = r.prove_matches(input).unwrap();
        let prove_ms = t1.elapsed().as_secs_f64() * 1e3;

        // Cross-check the proof's existence against the independent oracle.
        assert_eq!(
            thm.is_some(),
            oracle_matches(&re(src), input.as_bytes()),
            "oracle disagreement: {label} ({src:?} on {input:?})",
        );
        assert_clean(&thm.unwrap_or_else(|| panic!("{label}: expected a match")));

        eprintln!(
            "{label:<14} {:>4} {compile_us:>9.1}µs {prove_ms:>9.2}ms",
            input.len()
        );
    }

    // The point of a compiled `Regex`: amortise the desugar+reify across many
    // inputs. Compile once, prove a batch — versus the free function, which
    // recompiles on every call.
    let ids = [
        "alpha",
        "beta_2",
        "Gamma3",
        "_hidden",
        "camelCaseName",
        "SCREAMING_CASE",
    ];
    let r = Core::parse(r"[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
    let t = Instant::now();
    for id in &ids {
        assert!(r.prove_matches(id).unwrap().is_some());
    }
    let cached_ms = t.elapsed().as_secs_f64() * 1e3;

    let t = Instant::now();
    for id in &ids {
        assert!(
            prove_matches(&re(r"[a-zA-Z_][a-zA-Z0-9_]*"), id)
                .unwrap()
                .is_some()
        );
    }
    let recompiled_ms = t.elapsed().as_secs_f64() * 1e3;

    eprintln!(
        "\nbatch of {} identifiers: cached {cached_ms:.2}ms vs recompiled-each {recompiled_ms:.2}ms\n",
        ids.len(),
    );
}
