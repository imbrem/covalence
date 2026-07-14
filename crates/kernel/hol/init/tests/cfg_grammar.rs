//! North-star integration tests for the CFG stratum: kernel-checked parses of
//! **real WASM 3.0 binary-format grammar fragments** and their soundness
//! projection, driven entirely through the public API.
//!
//! Grammars come from the bundled WASM 3.0 spec dump
//! (`covalence_spectec::grammar::wasm3_binary`, via
//! `covalence_init::grammar::spectec::spec_grammar_env`) — never hand-written.
//! Every theorem is asserted hypothesis-free.

use covalence_init::Thm;
use covalence_init::grammar::cfg::{soundness, tactic::prove_derives};
use covalence_init::grammar::spectec::spec_grammar_env;

/// A proved theorem with no hypotheses (oracle-free by construction).
#[track_caller]
fn assert_clean(thm: &Thm) {
    assert!(thm.hyps().is_empty(), "expected no hypotheses, got {thm:?}");
}

// ----------------------------------------------------------------------------
// T1 — the WASM preamble: `\0asm` magic and the version word, through the CFG
// stratum over the real Bmagic / Bversion grammars.
// ----------------------------------------------------------------------------

#[test]
fn t1_preamble_magic_and_version() {
    let (env, _report) = spec_grammar_env(&["Bmagic", "Bversion"]).unwrap();

    let magic = env.nt("Bmagic").expect("Bmagic present in the 3.0 dump");
    let thm = prove_derives(&env, magic, &[0x00, 0x61, 0x73, 0x6D])
        .unwrap()
        .expect("the \\0asm magic parses as Bmagic");
    assert_clean(&thm);

    let version = env
        .nt("Bversion")
        .expect("Bversion present in the 3.0 dump");
    let thm = prove_derives(&env, version, &[0x01, 0x00, 0x00, 0x00])
        .unwrap()
        .expect("the version word parses as Bversion");
    assert_clean(&thm);

    // A corrupt magic byte does not parse.
    assert!(
        prove_derives(&env, magic, &[0x00, 0x61, 0x73, 0x6E])
            .unwrap()
            .is_none()
    );
}

// ----------------------------------------------------------------------------
// T2 — the reftype non-terminal chain: Breftype → Bheaptype → Babsheaptype,
// the genuinely context-free content. `[0x70]` is a one-hop
// (Breftype → Babsheaptype) parse; `[0x64,0x70]` chains three grammars.
// ----------------------------------------------------------------------------

#[test]
fn t2_reftype_chain() {
    let (env, _report) = spec_grammar_env(&["Breftype"]).unwrap();
    let breftype = env.nt("Breftype").expect("Breftype present");

    // One hop: Breftype → Babsheaptype, `func` heap type 0x70.
    let one_hop = prove_derives(&env, breftype, &[0x70])
        .unwrap()
        .expect("[0x70] parses as Breftype via Babsheaptype");
    assert_clean(&one_hop);

    // Two hops: Breftype → 0x64 Bheaptype → 0x64 Babsheaptype.
    let two_hop = prove_derives(&env, breftype, &[0x64, 0x70])
        .unwrap()
        .expect("[0x64,0x70] parses as Breftype via the ref-null chain");
    assert_clean(&two_hop);

    // A lone tag byte with no following heap type does not parse.
    assert!(prove_derives(&env, breftype, &[0x64]).unwrap().is_none());
}

// ----------------------------------------------------------------------------
// T3 — soundness projection: the parsed bytes lie in *every* language family
// closed under the reftype grammar rules.
// ----------------------------------------------------------------------------

#[test]
fn t3_reftype_in_every_closed_family() {
    let (env, _report) = spec_grammar_env(&["Breftype"]).unwrap();
    let breftype = env.nt("Breftype").unwrap();

    let der = prove_derives(&env, breftype, &[0x64, 0x70])
        .unwrap()
        .expect("parses");
    assert_clean(&der);

    // ⊢ ∀F. ClosedFam_E F ⟹ mem w (F ⌜Breftype⌝)
    let projected = soundness::derives_in_family(&env, breftype, &der).unwrap();
    assert_clean(&projected);
}

// ----------------------------------------------------------------------------
// Differential — the tactic agrees with the neutral CFG's independent
// recogniser over the reftype env for short byte strings.
// ----------------------------------------------------------------------------

#[test]
fn differential_reftype_vs_naive_parse() {
    let (env, _report) = spec_grammar_env(&["Breftype"]).unwrap();
    let breftype = env.nt("Breftype").unwrap();
    let cfg = env.cfg();

    // Byte values around the interesting tags (0x63/0x64 prefixes, the
    // 0x69–0x74 absheaptype range).
    let candidates: &[u8] = &[0x62, 0x63, 0x64, 0x69, 0x70, 0x74, 0x75];
    // Length 0, 1, and 2 words over the candidate alphabet.
    let mut words: Vec<Vec<u8>> = vec![vec![]];
    for &b in candidates {
        words.push(vec![b]);
    }
    for &b0 in candidates {
        for &b1 in candidates {
            words.push(vec![b0, b1]);
        }
    }

    for w in &words {
        let tactic_ok = prove_derives(&env, breftype, w).unwrap().is_some();
        let naive_ok = cfg.naive_parse(breftype, w);
        assert_eq!(
            tactic_ok, naive_ok,
            "tactic vs naive_parse disagree on {w:x?}"
        );
        // When the tactic succeeds, the theorem is hypothesis-free.
        if tactic_ok {
            assert_clean(&prove_derives(&env, breftype, w).unwrap().unwrap());
        }
    }
}
