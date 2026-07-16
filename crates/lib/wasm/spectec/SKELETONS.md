# covalence-spectec — skeletons

Intentional placeholders in `crates/lib/wasm/spectec`. See [CLAUDE.md](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Removed (recover from git history)

- **Native `.watsup` frontend.** The hand-written lexer/parser/CST/elaborator/
  typechecker/mixfix/doc-printer + the `syntax`-alias HOL lowering driver
  (`lex.rs`, `parse.rs`, `elab.rs`, `typecheck.rs`, `lower.rs`, …) and corpus
  tests were deleted. The crate is now **AST-first**: it consumes the elaborated
  SpecTec AST `wasm_spec_ast` ships. Reintroduce a native frontend only if we ever
  need to parse `.watsup` ourselves.

## Partial subsystems

- **WASM grammar versions** (`src/grammar.rs`). Only `grammar::wasm3` is wired —
  `wasm_spec_ast` bundles only the WebAssembly 3.0 spec. A validated recipe now
  exists to dump the 1.0/2.0 SpecTec ASTs (build upstream OCaml SpecTec at the
  pinned commit, `spectec … --ast`; see `notes/vibes/logics/cfg-stratum-design.md`
  §"Version lattice"). Both dumps are **produced + validated** (0 decode errors,
  staged in `~/tmp/spectec-dumps/`), **not yet embedded** — remaining work is to
  vendor the blobs and add `grammar::wasm1`/`wasm2`. The `Grammar` view is
  version-independent.
- **CFG lowering — recognition-mode residue** (`src/cfg.rs`). Two modes:
  `lower` (under-approx, `L(lowered) ⊆ L(SpecTec)`) skips premise / parametric /
  `ListN` productions; `lower_recognition` (over-approx recognizer,
  `L(SpecTec) ⊆ L(lowered)`) unlocks them via LEB128-as-regex and the
  monomorphiser — ground-integer **and grammar-valued** instance keys
  (`BuN@32`, `Bsection_@1,…`, `Blist@…`), section-id attr folds, iterated
  value-premise drops — so `Bmodule` + all 14 section grammars lower and a real
  27-byte module recognizes (`bmodule_recognition_differential` pins
  accept/refuse **and the two byte-sink over-approximations**: widened vectors
  swallow low-LEB tails; custom sections swallow arbitrary bytes).
  Whole 231-grammar universe loads via `covalence-init`'s
  `spec_grammar_env_all`; `T*` is left-recursive (`Thexnum`), and the
  recognition corpus adds nullable-body star cycles (`Bcustomsec*`).
  Still not lowered even in recognition mode (honest skips, reported):
  **`T*_` identifier-context params** (context-valued `Exp` params never
  const-fold — the dominant bucket, Recognition 204 skipped prods / 66 dead
  `T*` grammars; Under 236); **`rule`/`let` premises** (`iter`-wrapped `if`s
  over production-locals now drop; the rest skip, 4 prods); **2 bridge
  terminals** (`T*` fragments outside the byte-regex subset); **faithful
  `ListN`** (widened to star, not length-coupled — also what blocks an *exact*
  Under-mode `Bmodule`). Env transport / cross-version metatheorems (M7)
  remain future work.
- **Byte-regex bridge scope** (`regex.rs`). `regex::sym_to_regex_u8` bridges only
  the **regular** fragment — `Var`, `Attr`, `ListN`, and dom-binding iteration
  return `BridgeError`; the CFG layer (`src/cfg.rs`) now handles non-terminal
  references, Attr stripping, and `Opt`/`List`/`List1` desugaring on top of it.
  The 3.0 dump carries the **complete** binary format (~89 `B*` grammars; `Binstr`
  alone has 498 productions), not just a handful — pinned in `cfg::tests`.
