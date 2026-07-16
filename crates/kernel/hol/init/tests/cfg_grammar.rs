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
use covalence_init::grammar::regex::tactic::prove_matches;
use covalence_init::grammar::spectec::{spec_grammar_env, spec_grammar_env_recognition};

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

// ----------------------------------------------------------------------------
// T4 — LEB128 (recognition mode): kernel-checked parses of real WASM varints
// via the monomorphised `Bu32 = BuN(32)` grammar, lowered to a byte-count-
// bounded LEB128 regex terminal. Recognition mode over-approximates the value
// bound (`L(SpecTec) ⊆ L(Cfg)`); a `Derives_E` here witnesses the byte SHAPE.
// ----------------------------------------------------------------------------

#[test]
fn t4_leb128_bu32_recognition() {
    let (env, report) = spec_grammar_env_recognition(&["Bu32"]).unwrap();
    let bu32 = env.nt("Bu32").expect("Bu32 present");

    // Real unsigned LEB128 varints parse, hypothesis-free.
    for w in [
        &[0x00u8][..],                       // 0
        &[0x80, 0x01][..],                   // 128
        &[0xE5, 0x8E, 0x26][..],             // 624485
        &[0xFF, 0xFF, 0xFF, 0xFF, 0x0F][..], // 0xFFFFFFFF, the 5-byte max for 32 bits
    ] {
        let thm = prove_derives(&env, bu32, w)
            .unwrap()
            .unwrap_or_else(|| panic!("{w:x?} should parse as Bu32"));
        assert_clean(&thm);
    }

    // An incomplete varint (continuation bit set, no terminator) is rejected.
    assert!(prove_derives(&env, bu32, &[0x80]).unwrap().is_none());
    // An over-long encoding (6 bytes) exceeds the 32-bit byte-count bound.
    assert!(
        prove_derives(&env, bu32, &[0x80, 0x80, 0x80, 0x80, 0x80, 0x00])
            .unwrap()
            .is_none()
    );

    // Recognition mode is honestly reported.
    assert!(report.mono_instances >= 1, "BuN@32 was monomorphised");
}

// ----------------------------------------------------------------------------
// T4 differential — the kernel `Derives_E ⌜Bu32⌝` recognition agrees, byte for
// byte, with the standalone `leb128_regex(32)` regex oracle proved via the
// regex tactic (`prove_matches`). Two independent kernel paths must coincide.
// ----------------------------------------------------------------------------

#[test]
fn t4_bu32_agrees_with_leb128_regex_oracle() {
    let (env, _report) = spec_grammar_env_recognition(&["Bu32"]).unwrap();
    let bu32 = env.nt("Bu32").unwrap();
    // The exact regex Bu32's BuN@32 instance lowers to.
    let oracle = covalence_spectec::cfg::leb128_regex(32);

    // Enumerate byte strings over a set hitting both the continuation (>=0x80)
    // and terminator (<0x80) ranges, lengths 0..=3.
    let alphabet: &[u8] = &[0x00, 0x01, 0x7F, 0x80, 0x81, 0xFF];
    let mut words: Vec<Vec<u8>> = vec![vec![]];
    for &a in alphabet {
        words.push(vec![a]);
        for &b in alphabet {
            words.push(vec![a, b]);
            for &c in alphabet {
                words.push(vec![a, b, c]);
            }
        }
    }

    for w in &words {
        let derives = prove_derives(&env, bu32, w).unwrap().is_some();
        let matches = prove_matches(&oracle, w).unwrap().is_some();
        assert_eq!(
            derives, matches,
            "Bu32 Derives vs leb128_regex(32) Matches disagree on {w:x?}"
        );
    }
}

// ----------------------------------------------------------------------------
// T4b — a WASM type index (`Btypeidx = Bu32`) parses a varint through the same
// LEB128 instance, showing the whole `*idx` family unlocked.
// ----------------------------------------------------------------------------

#[test]
fn t4b_typeidx_is_leb128() {
    let (env, _report) = spec_grammar_env_recognition(&["Btypeidx"]).unwrap();
    let typeidx = env.nt("Btypeidx").expect("Btypeidx present");
    // Type index 3 (single byte) and 128 (two-byte varint).
    assert_clean(&prove_derives(&env, typeidx, &[0x03]).unwrap().unwrap());
    assert_clean(
        &prove_derives(&env, typeidx, &[0x80, 0x01])
            .unwrap()
            .unwrap(),
    );
    assert!(prove_derives(&env, typeidx, &[0x80]).unwrap().is_none());
}

// ----------------------------------------------------------------------------
// T5 — **a real, whole WASM module**, recognized end to end through the kernel:
// `⊢ Derives_E ⌜Bmodule⌝ ⌜bytes⌝`, hypothesis-free, over the recognition-mode
// `Bmodule` closure (grammar-valued parameter monomorphisation: the 14 section
// grammars, `Bsection_`/`Blist` instances, folded section-id bytes).
//
// # What the theorem means (recognition mode — read before citing)
//
// `L(SpecTec) ⊆ L(Cfg)` on the `Full`-coverage closure: every spec-valid module
// derives, and REFUSAL is sound — but derivability over-approximates validity.
// The widenings in `Bmodule`'s closure, and their concrete consequences:
//
//  - **section `len` / code-size premises dropped**: a section's length prefix
//    is *not* tied to its contents — a module with a wrong `len` still derives;
//  - **`ListN` vectors star-widened** (`Blist` = `Bu32` count + element star):
//    a vector's count prefix is *not* tied to its element count — wrong counts
//    still derive, and trailing low-LEB bytes can be swallowed by a widened
//    index star (truncating the final `end` opcode still derives!);
//  - **custom sections are a byte sink**: `Bcustom` ends in `byte*`, so a parse
//    may re-split to open a custom section at any reachable `0x00` byte and
//    swallow arbitrary garbage (an appended dangling `0x80` still derives);
//  - **`Bname` utf8 / `Bmodule` correlation premises dropped**; **LEB128 final
//    byte's high bits unchecked** (value-range over-approximation).
//
// So the REFUSAL test below is *recognition-refusal* — the tactic failing to
// find a derivation in the over-approximated grammar (which soundly implies
// the bytes are not a spec-valid module) — NOT a kernel theorem of
// non-membership; and corruptions that fall inside a widening (wrong counts,
// swallowed tails) are demonstrated to still derive. Exact `Bmodule` (Under
// mode) remains blocked on value-coupled `ListN` + section-`len`/`Iter`
// premises; see `crates/lib/wasm/spectec/SKELETONS.md`.
// ----------------------------------------------------------------------------

/// The real binary encoding of `(module (func (result i32) i32.const 42))`,
/// 27 bytes, derived byte by byte.
fn wasm_module_i32_const_42() -> Vec<u8> {
    vec![
        0x00, 0x61, 0x73, 0x6D, // magic `\0asm`
        0x01, 0x00, 0x00, 0x00, // version 1
        0x01, 0x05, // type section: id 1, size 5
        0x01, // — vec: 1 rectype
        0x60, 0x00, 0x01, 0x7F, // — functype: 0x60, [] params, [i32] results
        0x03, 0x02, // func section: id 3, size 2
        0x01, 0x00, // — vec: 1 func, typeidx 0
        0x0A, 0x06, // code section: id 10, size 6
        0x01, // — vec: 1 code entry
        0x04, // — body size 4
        0x00, // — vec: 0 local groups
        0x41, 0x2A, // — i32.const 42
        0x0B, // — end
    ]
}

#[test]
fn t5_whole_module_recognition() {
    // The Bmodule closure's `Closed_E` is a right-nested conjunction of ~800
    // clauses; kernel term walks recurse structurally, so whole-module proofs
    // need the same big-stack driver as the relation leg's total load.
    covalence_init::wasm::lower::total::with_total_stack(t5_whole_module_recognition_body)
}

fn t5_whole_module_recognition_body() {
    let t_env = std::time::Instant::now();
    let (env, report) = spec_grammar_env_recognition(&["Bmodule"]).unwrap();
    let t_env = t_env.elapsed();
    let module = wasm_module_i32_const_42();
    let bmodule = env.nt("Bmodule").expect("Bmodule present");

    // Bmodule itself lowers Full (every production of the grammar lowered) —
    // the recognition direction holds for the grammar; instance NTs deeper in
    // the closure attribute conservatively to their generics.
    assert_eq!(
        report.grammars.get("Bmodule"),
        Some(&covalence_spectec::cfg::Coverage::Full),
        "Bmodule lowers Full in recognition mode",
    );

    // THE HEADLINE: a real 27-byte module, kernel-checked, hypothesis-free.
    let t_proof = std::time::Instant::now();
    let thm = prove_derives(&env, bmodule, &module)
        .unwrap()
        .expect("the real module derives as Bmodule");
    let t_proof = t_proof.elapsed();
    assert_clean(&thm);
    println!(
        "T5: {} bytes, env {} clauses / {} NTs (built in {t_env:?}); \
         ⊢ Derives_E ⌜Bmodule⌝ w proved in {t_proof:?}",
        module.len(),
        env.n_clauses(),
        env.cfg().num_nts(),
    );

    // The empty module (magic + version only) also derives.
    assert_clean(
        &prove_derives(
            &env,
            bmodule,
            &[0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00],
        )
        .unwrap()
        .expect("the empty module derives"),
    );

    // RECOGNITION-REFUSAL (see the module comment: sound refusal, not a
    // non-membership theorem): corrupt magic, and an invalid section id at the
    // first post-version position — both fail cleanly, no kernel error.
    let t_refuse = std::time::Instant::now();
    let mut bad_magic = module.clone();
    bad_magic[0] = 0x01;
    assert!(
        prove_derives(&env, bmodule, &bad_magic).unwrap().is_none(),
        "bad magic refused",
    );
    let mut bad_secid = module.clone();
    bad_secid[8] = 0xFF;
    assert!(
        prove_derives(&env, bmodule, &bad_secid).unwrap().is_none(),
        "invalid section id refused",
    );
    println!("T5: two refusals in {:?}", t_refuse.elapsed());

    // PINNED OVER-APPROXIMATION (kernel-checked demonstration of the module
    // comment's caveats — this DERIVES even though it is not a valid module):
    // a truncated tail is swallowed by a widened index star. (The dangling-
    // `0x80` custom-section byte-sink twin is pinned at the `Cfg` level in
    // `covalence-spectec`'s `bmodule_recognition_differential`; proving it here
    // too would only re-spend another full-module proof.)
    assert_clean(
        &prove_derives(&env, bmodule, &module[..module.len() - 1])
            .unwrap()
            .expect("known widening: truncated tail still derives"),
    );
}

// ----------------------------------------------------------------------------
// T5b — the same module through the **whole-spec** env (all 231 grammars, both
// corpora, 1500+ clauses): the per-NT production index keeps the tactic
// tractable at full scale, and `derives_meaning` classifies `Bmodule`'s
// guarantee honestly (Mixed: instance NTs attribute to their non-Full
// generics, so no blanket direction is claimed for the closure).
// ----------------------------------------------------------------------------

/// Ignored by default: the whole-spec grammar env costs ~90 s (debug) on top
/// of T5's already-representative 27-byte `Bmodule` proof — a perf lever, not
/// extra coverage (see `crates/kernel/hol/init/SKELETONS.md`). Run explicitly:
/// `cargo test -p covalence-init --test cfg_grammar t5b -- --ignored`.
#[test]
#[ignore = "~90 s debug whole-spec grammar env; T5 covers the headline — run with --ignored"]
fn t5b_whole_module_on_whole_spec_env() {
    covalence_init::wasm::lower::total::with_total_stack(t5b_whole_module_on_whole_spec_env_body)
}

fn t5b_whole_module_on_whole_spec_env_body() {
    use covalence_init::grammar::spectec::cfg::{
        DerivesMeaning, derives_meaning, spec_grammar_env_all,
    };
    use covalence_spectec::cfg::LowerMode;

    let (env, report) = spec_grammar_env_all(LowerMode::Recognition).unwrap();
    let bmodule = env.nt("Bmodule").expect("Bmodule present");
    let module = wasm_module_i32_const_42();

    let t = std::time::Instant::now();
    let thm = prove_derives(&env, bmodule, &module)
        .unwrap()
        .expect("the real module derives on the whole-spec env");
    assert_clean(&thm);
    println!(
        "T5b: whole-spec env ({} clauses / {} NTs): module proved in {:?}",
        env.n_clauses(),
        env.cfg().num_nts(),
        t.elapsed(),
    );

    // Honest per-NT meaning: the closure mixes instance NTs (attributed
    // conservatively to their generic grammars), so no blanket containment is
    // claimed for Bmodule — the theorem still certifies derivability in the
    // lowered Cfg exactly.
    assert_eq!(
        derives_meaning(&env, &report, LowerMode::Recognition, bmodule),
        DerivesMeaning::Mixed,
    );
}
