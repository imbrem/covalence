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
  `wasm_spec_ast` bundles only the WebAssembly 3.0 spec. `wasm1`/`wasm2` await
  separately dumped ASTs (run OCaml SpecTec against the 1.0/2.0 specs and embed).
  The `Grammar` view is version-independent, so this is purely "supply more blobs."
- **Binary-grammar coverage** (`grammar.rs`, `regex.rs`). The 3.0 dump exposes only
  a few `B*` binary grammars (bulk is decode `def`s, not `gram`s).
  `regex::sym_to_regex_u8` bridges only the **regular** fragment — `Var`, `Attr`,
  `ListN`, and dom-binding iteration return `BridgeError`. Non-terminal references
  need a CFG layer (grammar environment + reference resolution) that
  `covalence-grammar` lacks; until then a grammar with a `Var` can't flatten to a
  `Regex`.
