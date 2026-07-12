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
- **Proof format: workable rule subset + no tactic language.** `src/proof.rs`
  (`hol-typed`) replays S-expr proofs through the `Hol`/`Nat` rules and the
  linker checks the conclusion α-equals the lowered statement (demo:
  `examples/nat_theorems.{hs,proof}`, `tests/proof_linker.rs` — `refl_a` /
  `add_base_thm` checked, hole + wrong-proof cases). Deferred: broader rule
  coverage (`exists_*`, `cong_app`, `false_elim`, rewriting — the trait exposes
  them, the replayer wires a subset); a higher-level **tactic** surface
  compiling to the low-level steps; the `monad.rs` `map_ret` proof (assume
  left-id → instantiate → β-reduce → discharge) as a dialect theorem. No
  inference: statement variables are typed by an ambient env, not inferred.
  Design: `notes/vibes/proof-format.md`. (A whole-module-plus-proof-file driver
  emitting a per-theorem proved/hole/rejected report now exists —
  `covalence-web-kernel::check_haskell_proofs`, demoed live on the `/proofs`
  page — but types every statement variable as `nat`; a general ambient-op /
  multi-sort driver is still open.)
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

- **Live web playground: DONE (incl. typed HOL + proof checking).**
  `covalence-web-kernel` (`crates/kernel/web`) compiles the dialect to wasm and
  exposes four fns: `haskell_to_sexpr` (kernel-agnostic S-expr), `haskell_to_hol_term`
  (untyped carved `Term`), `haskell_to_typed_hol` (annotated def/expr →
  well-typed HOL `Term` + type, via `hol-typed`/`NativeHol`), and
  `check_haskell_proofs` (link a theorem module to an S-expr proof file, per-theorem
  proved/hole/axiom/mismatch). The `/haskell` page shows the sexpr / untyped /
  typed views; the `/proofs` page is the live proof checker. All zero-TCB (the
  kernel deps are already in the wasm via `covalence-kernel`). Follow-on: only the
  gaps above (per-theory type traits, broader rule set, tactic layer).
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
