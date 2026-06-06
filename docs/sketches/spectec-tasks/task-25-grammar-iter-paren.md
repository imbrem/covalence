# Task 25 — Grammar: `(...)` `(...)*` `(...)?` → `Iter` / `Seq` nesting

**Branch:** `spectec-grammar`.
**Dependencies:** #23.
**Estimated impact:** Gram +N; unblocks #27.

## The big picture

Grammar productions use parens to group sub-symbols, and trailing
iter suffixes to make a sub-grammar parse zero/one-or-more times.
The wasm-3.0 spec is full of `(in:Binstr)*`, `(t:Bvaltype)?`, and
similar — currently they collapse to `Eps`.

The `SpecTecSym::Iter { g1, it, xes }` variant has the same shape as
the expression-level `Iter` we already handle in `expr_to_spectec`.
The `xes` field is the iter binder annotation (which metavar this
iter is bound to in the outer scope) — for parity with OCaml's
output we need to populate it, but doing so depends on the binder
inference pass; v1 can emit `xes: []` and a follow-up task can fill
it in.

## Intuition

Think of grammar `(X)*` as the parser-world analogue of expression
`x*`: parse `X` zero or more times, yielding a list. The grammar-level
`xes` field is just plumbing for which OUTER metavar this list of
parses gets bound to — for `(in:Binstr)*` it's `in*`. That's the
exact same dom-binder inference we do for premise iters today
(`gather_iter_sources_in_premise`).

## Source-of-truth examples

Bare paren grouping (no iter suffix):

```
| 0x00 (a b) 0x01    →  Seq{[Seq{[Num 0]}, Seq{[Seq{[Var a, Var b]}]}, Seq{[Num 1]}]}
```

(I.e. parens just wrap into a single chunk — the chunker treats
`(...)` as one juxtaposition element, and recurses on the inner.)

Iter — list:

```
| ... (in:Binstr)* 0x0B     (Binstr/block)
```

Inner sym for the iter chunk:

```
(iter (attr (var "in") (var "Binstr")) list (dom "in" (var "in*")))
```

Iter — opt:

```
| 0x40 (t:Bvaltype)? => ...
```

Inner sym:

```
(iter (attr (var "t") (var "Bvaltype")) opt (dom "t" (var "t?")))
```

(For v1 emit `dom` as `[]` and add a TODO. Full impl is a follow-up.)

## Token-to-AST mapping for this task

Extend `chunk_to_atom` (or wherever the per-chunk classifier lives):

| Chunk shape | Output |
| --- | --- |
| `( ... )` | recurse into inner via `grammar_sym_from_tokens` |
| `( ... ) *` | `Iter { g1, it: List, xes: [] }` |
| `( ... ) ?` | `Iter { g1, it: Opt, xes: [] }` |
| `( ... ) +` | `Iter { g1, it: List1, xes: [] }` |

The chunker must treat `(...)` plus optional trailing iter suffix as
a single chunk (don't split between `)` and `*`).

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - Chunker from #23 — extend with the paren-balanced case.
  - `chunk_to_atom` (or equivalent) — add the paren / iter branches.

## Approach sketch

```rust
fn chunk_to_atom(chunk: &[Spanned], ctx: &ElabContext) -> SpecTecSym {
    // Paren-wrapped with optional iter suffix.
    if let Some((inner, iter_suffix)) = match_paren_with_iter(chunk) {
        let g1 = grammar_sym_from_tokens(inner, ctx);
        return match iter_suffix {
            None => g1,
            Some(it) => Iter { g1: Box::new(g1), it, xes: vec![] },
        };
    }
    // Binder, then atom (from #24, then #23).
    ...
}
```

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_sym` with `IterG` /
  `ParenG` / similar cases.
- The `Iter` AST shape (with `xes` aka the "domain" annotations):
  <https://github.com/WebAssembly/spec/blob/9479f1d/spectec/src/backend-ast/print.ml#L149>
- The dom-binder inference logic in OCaml is in
  `spectec/src/frontend/iter.ml` (filename approximate — search for
  `Dom` / `iter_binding`).

## Testing & validation

```
cargo test -p covalence-spectec --test elab_differential -- --nocapture
```

Spot-check `Binstr/block` and `Bblocktype`:

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Gram Bblocktype differs/,/^===/p'
```

Confirm `Gram` count rises and no kind regresses.

Compare iter outputs to OCaml:

```
grep -B1 -A 25 '"Bblocktype"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

## Out of scope

- `xes` / `dom` annotations on `Iter` — emit `[]`, leave a TODO
  pointing at a follow-up task. The differential will still flag
  these but the structural shape will match modulo `xes`.
- Pattern-binder LHS in `Attr` — covered separately in task #24's
  notes.
