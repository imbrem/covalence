# `covalence-haskell` — skeletons

## Severe

- **Typed backend: no per-theory type constructors.** The typed backend
  (`src/typed.rs`, `hol-typed` feature) lowers annotated definitions to real
  well-typed HOL `Term`s **through the `Hol`/`Nat` traits**, but `resolve_ty`
  only knows type *variables*, `nat`, `bool`, and function types. Applied
  constructors (`option a`, `list a`, `int`, `bytes`, `unit`) are reported
  `UnsupportedType` — they need per-theory API traits (`Option`/`List`/… mirroring
  `Nat`), which is why the flagship `tests/typed_monad.rs` lowers only the
  **abstract** monad (ret/bind as free vars over a carrier type variable, `map`
  defined, the `map f (ret a) = ret (f a)` law *stated*). The concrete `option`
  / `list` instances from `init/monad.rs` (`some`/`none`/`option_bind`,
  `singleton`/`concatMap`) need those traits.
- **Typed backend lowers TERMS + law STATEMENTS, not PROOFS.** `typed.rs`
  produces `Term`s (definitions and the monad-map-law equation), not `Thm`s: it
  does not replay `monad.rs`'s derivation (assume left-id → instantiate →
  β-reduce → discharge). Proof/tactic lowering — a dialect proof script driving
  the `Hol` rule methods (`assume`/`all_elim`/`beta_conv`/`imp_intro`/…) to
  build a `Thm` — is the follow-on; the Rust proof stays in `init/monad.rs`
  against the same shapes (see `notes/vibes/init-in-dialect.md`).
- **No typeclass / instance elaboration.** The monad is written with the ops as
  plain free variables + an ambient env (`lower_decl_in`). Real `class Monad m` /
  `instance` elaboration = dictionary passing (a class → a record of ops, an
  instance → a value, methods → projections), and general `m`-polymorphism needs
  HOL-omega type-operator variables (standard HOL has none — hence the
  single-carrier `mcar` type *variable*). Both are deferred.
- **Untyped `hol` backend: no lowering to `init/` definitions.** The demos
  (`tests/init_dialect.rs`, `tests/examples.rs`) lower init-flavored modules to
  exact `(define …)` interchange text and to carved (untyped) `sexpr` kernel
  `Term`s — *inert data*. The typed backend (above) is the typed counterpart but
  covers only the trait-reachable fragment. Realizing dialect defs into actual
  `covalence-init` `Def`/`Thm` (so `init/` is really written in the dialect) is
  still open; the untyped `if`/`list`/`tuple`/`unit` sugar heads land as plain
  atoms.

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
`{- -}` block comments, top-level type-signature lines (`name :: Ty`, now
**parsed into a `Ty` and attached** to the following definition), annotated
lambda binders (`\(x :: Ty) -> e`), and the `Ty` grammar (type variables,
base/applied constructors, function arrows — no inference). Still not supported:

- do-notation, guards, `where`/`let` blocks with multiple binders, `case`;
- `type`/`data`/`class`/`instance` declarations (only the `name :: Ty`
  signature form is recognised; there is no typeclass/instance elaboration);
- higher-kinded / `forall`-quantified / constrained types in the `Ty` grammar
  (only rank-0 vars + constructors + arrows; the monad carrier is a plain type
  *variable*, not a type-operator variable);
- pattern matching (only bare parameter names) and multi-clause definitions;
- full Haskell layout (only newline separation + indented-continuation
  layout-lite; no offside rule, no `{ ; }` explicit blocks). A multi-line
  block comment in a module is handled by a comment-blanking pre-pass, but the
  underlying line grouper is still layout-lite;
- operator sections, negative literals, floating-point/char literals,
  user-defined operators (only `+ - * ==`);
- list-cons `:` / list ranges `[a..b]` / list comprehensions.
