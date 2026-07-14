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
- **CFG lowering — parametric / premise / ListN residue** (`src/cfg.rs`). `lower`
  emits `Cfg<u8>` for the regular + non-terminal fragment (under-approximating:
  `L(lowered) ⊆ L(SpecTec)`). Still skipped (per production, reported): premise
  branches (11 `B*` grammars — `Bmodule BuN BsN Bname Bheaptype Bblocktype Bmemarg
  Bsection_ Btable Bfunc Bcode`); param-**dependent** parametric refs (M6
  monomorphisation — param-*independent* ones like `Bvar` are resolved); `ListN` /
  dom-binding iteration (context-sensitive, `Blist`). No premise-drop
  over-approximation mode.
- **Byte-regex bridge scope** (`regex.rs`). `regex::sym_to_regex_u8` bridges only
  the **regular** fragment — `Var`, `Attr`, `ListN`, and dom-binding iteration
  return `BridgeError`; the CFG layer (`src/cfg.rs`) now handles non-terminal
  references, Attr stripping, and `Opt`/`List`/`List1` desugaring on top of it.
  The 3.0 dump carries the **complete** binary format (~89 `B*` grammars; `Binstr`
  alone has 498 productions), not just a handful — pinned in `cfg::tests`.
