# `covalence-haskell` — skeletons

## Severe

- **Typed HOL-Term realization not done.** The `hol` backend (`src/hol.rs`)
  lands real kernel data but only via the *untyped* carved `sexpr` type (no
  type inference). A well-typed HOL-term realization (Church-style, with
  inference / elaboration) is the follow-on.
- **No lowering to `init/` definitions.** The flagship demos
  (`tests/init_dialect.rs`, `tests/examples.rs` over `examples/*.hs`) lower
  init-flavored modules to exact `(define …)` interchange text and to carved
  `sexpr` kernel `Term`s, but that output is *inert data* — realizing the
  dialect into actual `covalence-init` definitions/theorems (typed `Term`s,
  `Def`/`Thm`) so `init/` can really be written in it is not started. The
  `if` / `list` / `tuple` / `unit` sugar heads currently land as plain
  symbols/atoms; a typed lowering would map them to the real kernel
  conditional / list / product / unit.

## Minor

- **No WASM build for the web demo.** The web Haskell-frontend page
  (`apps/covalence-web/src/routes/haskell`) ships *precomputed* `src → sexpr`
  pairs (real crate output in `src/lib/haskellExamples.json`). A *live*
  in-browser playground needs a wasm-bindgen build exposing
  `parse_expr`/`parse_module` + `expr_to_sexpr`/`module_to_text` (the
  `covalence-web-kernel` pattern), which is not wired.
- **No reader round-trip test.** The `hol` backend builds atoms as
  `atom (mk_blob …)`, whereas `sexpr_parse`'s reader yields `atom (bytes.abs
  …)` over a symbolic byte list; the two are equal only after evaluation, so
  a to-text → `sexpr_parse` → equal-Term round-trip needs the eval harness
  and is skipped.
- **HOL backend collapses string atoms into raw-byte atoms** (unquoted,
  unescaped UTF-8); a string with whitespace/parens would not re-read as one
  atom through `sexpr_parse`.
- **No quoted-symbol form in the interchange grammar** (`src/sexpr.rs`).
  Non-bare symbols (whitespace/parens/`"`/`;`, or all-digit spellings) cannot
  be printed round-trippably; `covalence-sexp` has `|…|` quoting if this is
  ever needed (a dialect bridge to `covalence-sexp` would be the fix).
- **`(define name body)` is a text convention, not a checked construct** —
  `parse_sexprs` accepts any forms; nothing validates module shape on the
  way back in.

## Minor — unsupported grammar

The parser covers a deliberately small subset. Now supported: `if`/`then`/
`else`, list `[…]` / tuple `(…,…)` / unit `()` literals, `--` line and nested
`{- -}` block comments, and top-level type-signature lines (`name :: T`,
parsed-and-ignored). Still not supported:

- do-notation, guards, `where`/`let` blocks with multiple binders, `case`;
- `type`/`data`/`class`/`instance` declarations (only the ignored `name :: T`
  signature form is recognised — the type itself is discarded, not checked);
- pattern matching (only bare parameter names) and multi-clause definitions;
- full Haskell layout (only newline separation + indented-continuation
  layout-lite; no offside rule, no `{ ; }` explicit blocks). A multi-line
  block comment in a module is handled by a comment-blanking pre-pass, but the
  underlying line grouper is still layout-lite;
- operator sections, negative literals, floating-point/char literals,
  user-defined operators (only `+ - * ==`);
- list-cons `:` / list ranges `[a..b]` / list comprehensions.
