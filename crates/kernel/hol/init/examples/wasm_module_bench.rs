//! Benchmark **whole-module kernel recognition** — the workload behind the
//! `cfg_grammar.rs` T5/T5b integration tests, extracted so `bun run
//! bench:wasm-module` can time and profile it in release mode (the tests run
//! debug and are dominated by the same phases).
//!
//! Phases, timed separately (all through the public API, every theorem
//! hypothesis-free):
//!
//! 1. `env` — build the `Bmodule`-rooted recognition [`GrammarEnv`]
//!    (`spec_grammar_env_recognition(["Bmodule"])`): SpecTec grammar →
//!    monomorphised `Cfg<u8>` → kernel clause layout.
//! 2. `prove` — `prove_derives` of the real 27-byte
//!    `(module (func (result i32) i32.const 42))` binary: tactic search +
//!    kernel derivation replay (`reps` repetitions, fastest reported).
//! 3. `refuse` — the two corruption refusals (bad magic, invalid section id).
//! 4. `whole_env` (only with `--whole-spec`) — the same proof on the
//!    all-231-grammar recognition env (the T5b variant; slower because
//!    `Closed_E` spans ~1500 clauses).
//!
//! Output: one JSON object on stdout (everything else on stderr), consumed by
//! `scripts/bench-wasm-module.mjs`.
//!
//! Usage: `wasm_module_bench [reps] [--whole-spec]`

use std::time::Instant;

use covalence_init::grammar::cfg::tactic::prove_derives;
use covalence_init::grammar::spectec::cfg::spec_grammar_env_all;
use covalence_init::grammar::spectec::spec_grammar_env_recognition;
use covalence_init::wasm::lower::total::with_total_stack;
use covalence_spectec::cfg::LowerMode;

/// The real binary encoding of `(module (func (result i32) i32.const 42))` —
/// kept in sync with `cfg_grammar.rs::wasm_module_i32_const_42`.
fn module_bytes() -> Vec<u8> {
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

fn main() {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let whole_spec = argv.iter().any(|a| a == "--whole-spec");
    let reps: usize = argv
        .iter()
        .find(|a| !a.starts_with("--"))
        .and_then(|a| a.parse().ok())
        .unwrap_or(1);

    with_total_stack(move || run(reps, whole_spec));
}

fn run(reps: usize, whole_spec: bool) {
    let bytes = module_bytes();

    // Phase 1: Bmodule-rooted recognition env.
    let t = Instant::now();
    let (env, report) = spec_grammar_env_recognition(&["Bmodule"]).expect("Bmodule env builds");
    let env_ms = t.elapsed().as_secs_f64() * 1e3;
    let bmodule = env.nt("Bmodule").expect("Bmodule present");
    eprintln!(
        "[bench] env: {} clauses, {} grammars full",
        env.n_clauses(),
        report.grammars.len()
    );

    // Phase 2: the whole-module proof (fastest of `reps`).
    let mut prove_ms = f64::INFINITY;
    for i in 0..reps.max(1) {
        let t = Instant::now();
        let thm = prove_derives(&env, bmodule, &bytes)
            .expect("tactic runs")
            .expect("the 27-byte module derives");
        assert!(thm.hyps().is_empty(), "hypothesis-free");
        let ms = t.elapsed().as_secs_f64() * 1e3;
        eprintln!("[bench] prove rep {i}: {ms:.1} ms");
        prove_ms = prove_ms.min(ms);
    }

    // Phase 3: refusals (bad magic; invalid section id).
    let t = Instant::now();
    let mut bad_magic = bytes.clone();
    bad_magic[3] = 0x6E;
    assert!(prove_derives(&env, bmodule, &bad_magic).unwrap().is_none());
    let mut bad_section = bytes.clone();
    bad_section[8] = 0x3F;
    assert!(
        prove_derives(&env, bmodule, &bad_section)
            .unwrap()
            .is_none()
    );
    let refuse_ms = t.elapsed().as_secs_f64() * 1e3;

    // Phase 4 (optional): the whole-spec-env variant (T5b).
    let whole = whole_spec.then(|| {
        let t = Instant::now();
        let (wenv, _) = spec_grammar_env_all(LowerMode::Recognition).expect("whole-spec env");
        let wenv_ms = t.elapsed().as_secs_f64() * 1e3;
        let wb = wenv.nt("Bmodule").expect("Bmodule present");
        let t = Instant::now();
        let thm = prove_derives(&wenv, wb, &bytes)
            .expect("tactic runs")
            .expect("module derives on the whole-spec env");
        assert!(thm.hyps().is_empty());
        let wprove_ms = t.elapsed().as_secs_f64() * 1e3;
        (wenv.n_clauses(), wenv_ms, wprove_ms)
    });

    let mut json = format!(
        "{{\n  \"bytes\": {},\n  \"env_clauses\": {},\n  \"env_ms\": {env_ms:.1},\n  \"prove_ms\": {prove_ms:.1},\n  \"refuse_ms\": {refuse_ms:.1}",
        bytes.len(),
        env.n_clauses(),
    );
    if let Some((wc, we, wp)) = whole {
        json += &format!(
            ",\n  \"whole_env_clauses\": {wc},\n  \"whole_env_ms\": {we:.1},\n  \"whole_prove_ms\": {wp:.1}"
        );
    }
    json += "\n}";
    println!("{json}");
}
