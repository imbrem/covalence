# Task 23 — Grammar: atomic symbols + `Seq`

**Branch:** `spectec-grammar` (foundation — first task on that branch).
**Dependencies:** none.
**Estimated impact:** Gram 11 → ~30–60 of 231. Foundation for #24–#27.

## The big picture

SpecTec's `SpecTecSym` AST (`Var`, `Num`, `Text`, `Eps`, `Seq`, `Alt`,
`Range`, `Iter`, `Attr`) IS the kernel-side data structure you want
for reasoning about parsing. It's a clean grammar algebra: atoms,
concatenation, alternation, ranges, repetition, and a way to bind
parse results to metavariables. Getting our elaborator to produce
this faithfully gives the kernel a well-typed grammar IR to consume.

Right now `grammar_sym_from_tokens` is a 25-line stub that handles a
single token (atom case) and falls back to `Eps` for everything else.
Every multi-token grammar production — i.e. essentially all of them —
loses its structure. This task rebuilds the atom recogniser and adds
juxtaposition-as-`Seq`. After this lands the grammar branch can stack
binders, parens, and iters on top with localized changes.

## Intuition for the OCaml shape

Each grammar production has a *symbol* (the LHS pattern matched
against the byte/text stream) and an *attribute expression* (the AST
value produced when the pattern matches). The symbol is a tree of
`SpecTecSym`s; the attribute is a `SpecTecExp`. We're improving the
symbol side.

OCaml's printer wraps each top-level juxtaposed element in its own
single-element `Seq` before concatenating. Mirror this exactly — the
differential test will diverge for `Seq{[a, b]}` vs
`Seq{[Seq{[a]}, Seq{[b]}]}`.

## Source-of-truth example

Input (`assets/spectec/wasm-3.0/5.3-binary.instructions.spectec:25`):

```
grammar Bcatch : catch =
  | 0x00 x:Btagidx l:Blabelidx => CATCH x l
```

Expected `g` for prod 1 (from the OCaml dump):

```
(seq
  (seq (num 0x00))
  (seq (attr (var "x") (var "Btagidx")))
  (seq (attr (var "l") (var "Blabelidx")))
)
```

This task delivers the `Num` / `Var` parts. The `attr` wrapping for
`x:Btagidx` is task #24 — until #24 lands, `x:Btagidx` will fall
through as `Seq{[Var(x), Colon-lit, Var(Btagidx)]}`, which is wrong
but stable.

## Token-to-AST mapping for this task

| Input shape | `SpecTecSym` output |
| --- | --- |
| (empty) | `Eps` |
| `eps` ident | `Eps` |
| `Nat` (`0x00`, `255`, `0b101`) | `Num { n }` |
| `Text("...")` | `Text { t }` |
| Bare ident `name` | `Var { x: name, as1: [] }` |
| `name(arg, ...)` | `Var { x: name, as1: [Exp{...}, ...] }` |
| 2+ juxtaposed sub-symbols | `Seq { gs: each-wrapped-in-Seq }` |

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - `grammar_sym_from_tokens` (around line 1731) — rewrite.
  - The `make_range_prod` path already produces `Range` for `prev | ...
    | next` chunks — don't touch.
  - The split-on-juxtaposition helper is new; reuse the depth-tracking
    pattern from `split_top_level_commas` elsewhere in the file.

## Approach sketch

```rust
fn grammar_sym_from_tokens(toks: &[Spanned], ctx: &ElabContext) -> SpecTecSym {
    if toks.is_empty() { return Eps; }
    let chunks = split_juxtaposed(toks);
    if chunks.len() == 1 {
        return chunk_to_atom(chunks[0], ctx);
    }
    Seq { gs: chunks.into_iter()
        .map(|c| Seq { gs: vec![chunk_to_atom(c, ctx)] })
        .collect() }
}
```

`split_juxtaposed` walks depth-0 tokens and starts a new chunk at each
"atom boundary". An atom boundary is the transition from an
ident/literal/closing-bracket to the next ident/literal/opening-bracket.
*Do not* split on iter-suffix tokens (`*`, `?`, `+`) or on `:` — those
belong with the preceding token. The exact rules for iter and `:`
matter for #24/#25 but the chunker should already be friendly to them
so those tasks become drop-in.

## Pointers to OCaml

- AST definition mirrored here:
  <https://github.com/WebAssembly/spec/blob/9479f1d/spectec/src/backend-ast/print.ml#L149>
  (Doc-comment on `SpecTecSym` in
  `~/.cargo/registry/.../spectec_ast-2.0.0/src/grammars.rs`.)
- Frontend elaboration:
  `spectec/src/frontend/elab.ml` — search for `elab_sym` / `Seq` /
  `juxt`. The OCaml takes a clearer "explicit sequence" approach;
  we're replicating its output shape, not its parser structure.
- Pretty-printer (canonical output format):
  `spectec/src/backend-ast/print.ml#L149`.

## Testing & validation

Primary harness:

```
cargo test -p covalence-spectec --test elab_differential -- --nocapture
```

Look for the line `Gram:  N / 231`. Should rise from 11.

Show specific diffs:

```
SPECTEC_DIFF_SHOW=20 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | grep "^=== Gram"
```

Focused sanity check — `Bcatch` should now have `Seq{[Seq{[Num 0]},
Seq{[Seq{[Var x, Colon-lit, Var Btagidx]}]}, ...]}` shape (modulo the
binder fix from #24):

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Gram Bcatch differs/,/^===/p'
```

Compare against the OCaml dump:

```
grep -B1 -A 30 '"Bcatch"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

Full crate tests (must stay 123 pass + 1 differential pass):

```
cargo test -p covalence-spectec
```

## Out of scope

- Binders (`name:Type` → `Attr`) — task #24.
- Iter / parens — task #25.
- Top-level `|` alternation INSIDE a single prod's sym. Not used in
  wasm-3.0. Skip — falls naturally out of the per-prod splitting in
  `split_grammar_prods`.
- `xes` (iter binder annotations) on `Iter` — task #25 emits `[]`.
- `Range` syntax — already handled by `make_range_prod`.

## Out of scope but worth a note in code

Add a TODO referencing #24 and #25 where the chunker meets `:`, `(`,
or iter-suffix tokens, so the next task knows where to extend.
