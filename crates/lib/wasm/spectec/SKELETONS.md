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
- **CFG lowering — grammar-valued-param residue** (`src/cfg.rs`). Two modes:
  `lower` (under-approx, `L(lowered) ⊆ L(SpecTec)`) skips premise / parametric /
  `ListN` productions; `lower_recognition` (M6, over-approx recognizer,
  `L(SpecTec) ⊆ L(lowered)`) unlocks them via LEB128-as-regex (`BuN`/`BsN` →
  one bounded `leb128_regex` terminal), the monomorphiser (ground-arg instances
  `BuN@32`, premise classification, `ListN` widening). Still not lowered even in
  recognition mode (honest `ParametricRef` skip, reported): **grammar-valued
  params** (`Blist`'s / `Bsection_`'s `BX`) — substituting an arg *grammar* into
  the instance body is unimplemented; and any parametric ref whose args don't
  const-fold to ground values (e.g. `BiN`/`BuN` as a bare root under an open
  `N`). Env transport / cross-version metatheorems (M7) remain future work.
- **Byte-regex bridge scope** (`regex.rs`). `regex::sym_to_regex_u8` bridges only
  the **regular** fragment — `Var`, `Attr`, `ListN`, and dom-binding iteration
  return `BridgeError`; the CFG layer (`src/cfg.rs`) now handles non-terminal
  references, Attr stripping, and `Opt`/`List`/`List1` desugaring on top of it.
  The 3.0 dump carries the **complete** binary format (~89 `B*` grammars; `Binstr`
  alone has 498 productions), not just a handful — pinned in `cfg::tests`.
