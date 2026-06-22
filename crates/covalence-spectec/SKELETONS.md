# covalence-spectec — skeletons

Intentional placeholders in `crates/covalence-spectec`. See [CLAUDE.md](../../CLAUDE.md) § Skeletons.

## Removed (recover from git history)

- **Native `.watsup` frontend.** The hand-written lexer/parser/CST/elaborator/
  typechecker/mixfix/doc-printer (`lex.rs`, `token.rs`, `source.rs`, `cst.rs`,
  `parse.rs`, `mixfix.rs`, `elab.rs`, `typecheck.rs`, `ast_doc.rs`) and the
  `syntax`-alias HOL lowering driver (`lower.rs`), plus their corpus tests,
  were deleted. The crate is now **AST-first**: it consumes the elaborated
  SpecTec AST that upstream `wasm_spec_ast` ships and compiles *from* that. A
  native Rust frontend can be reintroduced later if we ever need to parse
  `.watsup` ourselves rather than the OCaml backend's S-expression dump.

## Partial subsystems

- **WASM grammar versions** (`crates/covalence-spectec/src/grammar.rs`).
  Only [`grammar::wasm3`] is wired up, because `wasm_spec_ast` bundles **only**
  the elaborated WebAssembly 3.0 spec. `wasm1` / `wasm2` await separately
  dumped ASTs (run the OCaml SpecTec compiler against the 1.0 / 2.0 specs and
  embed the result, mirroring `wasm_spec_ast`). The [`grammar::Grammar`] view
  is version-independent, so this is purely "supply more embedded AST blobs."

- **Binary-grammar coverage** (`grammar.rs`, `regex.rs`). The bundled WASM 3.0
  AST exposes only a handful of `B*` *binary* grammars (`Bvectype`, `Bvar`,
  `BX`, …); the bulk of the binary format is specified via decode `def`s rather
  than `gram`s in this dump. [`regex::sym_to_regex_u8`] only bridges the
  **regular** fragment of a grammar symbol — `Var` (non-terminal reference),
  `Attr` (capture), `ListN` (parametric-length iteration), and dom-binding
  iteration all return a typed `BridgeError`. Non-terminal references need a
  CFG layer (a grammar *environment* + reference resolution) that
  `covalence-grammar` does not yet have; until then a grammar with a `Var` is
  not regular and cannot be flattened to a `Regex`.
