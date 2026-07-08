# `covalence-haskell` — skeletons

## Severe

- **Typed HOL-Term lowering not done.** The `hol` backend (`src/hol.rs`) lands
  real kernel data but only via the *untyped* carved `sexpr` type (no type
  inference). A well-typed HOL-term lowering (Church-style, with inference /
  elaboration) is the follow-on.
- **No lowering to `init/` definitions.** The end goal — lowering the dialect
  into actual `covalence-init` definitions/theorems so `init/` can be written
  in the Haskell dialect — is not started; the carved `sexpr` output is inert
  data, not a `Def`/`Thm`.

## Minor

- **No reader round-trip test.** The `hol` backend builds atoms as
  `atom (blob …)`, whereas `sexpr_parse`'s reader yields `atom (bytes.abs …)`
  over a symbolic byte list; the two are equal only after evaluation, so a
  pretty-print → `sexpr_parse` → equal-Term round-trip needs the eval harness
  and is skipped.
- **`str_lit` collapses strings into atoms** (raw UTF-8 bytes, unquoted); a
  string with whitespace/parens would not re-read as one atom.

## Minor — unsupported grammar

The parser covers a deliberately small subset. Not yet supported:

- do-notation, guards, `where`/`let` blocks with multiple binders;
- type signatures and type/`data`/`class`/`instance` declarations;
- pattern matching (only bare parameter names) and multi-clause definitions;
- full Haskell layout (only newline separation + indented-continuation
  layout-lite; no offside rule, no `{ ; }` explicit blocks);
- operator sections, `if`/`case`, list/tuple syntax, negative literals,
  floating-point/char literals, user-defined operators (only `+ - * ==`).
