# Skeletons — `covalence-hol::surface` (surface-syntax sketch)

Intentional placeholders for the surface-syntax authoring layer. See `CLAUDE.md`
§ Skeletons for the rules, the [crate index](../../SKELETONS.md), and the [root
index](../../../../SKELETONS.md).

## Empty / stub modules

- **`crates/covalence-hol/src/surface/`** — design sketch of the surface
  syntax (the "generalized Haskell" authoring layer, `docs/surface-syntax.md`).
  The AST (`surface::ast`), the `#`-builtin registry (`surface::Builtin`), and
  the parser (`surface::parse` / `parse_str`, pure S-expr → directive AST) are
  implemented, but the layers above remain stubs: the **elaborator** (surface
  → low-level S-expr → kernel object), the **`#by` tactic grammar** (proof
  steps are kept as raw `SExpr`s in `Proof::steps`), and **`#import` content
  addressing** (`#import` resolves names only; by-hash addressing is unbuilt)
  are all future work.
