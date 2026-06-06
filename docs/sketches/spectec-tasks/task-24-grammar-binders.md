# Task 24 — Grammar: `name:Type` binder → `Attr`

**Branch:** `spectec-grammar`.
**Dependencies:** #23 (needs the juxtaposition chunker as the substrate).
**Estimated impact:** Gram +N, plus unblocks #26 (per-prod `ps`).

## The big picture

Binders are how a grammar production names the result of a sub-parse
so the attribute expression can reference it. `t:Bvaltype` says
"parse a `valtype` via `Bvaltype`, and bind the result to `t` in the
attribute scope." In the AST that's `SpecTecSym::Attr { e: Var(t),
g1: Var(Bvaltype) }` — an explicit `Attr` node wrapping the
sub-grammar.

Without binders, the produced ASTs would parse but you couldn't write
the corresponding semantic values (the `e` field of `Prod`), and the
prod's `ps` list (free metavars in the prod) can't be computed. So
this task unblocks #26 and most of the realistic Gram diffs.

## Intuition

The `Attr` wrapper is asymmetric: the binder side carries an
EXPRESSION (`SpecTecExp`, typically `Var(x)` but can be more complex
patterns like `Case "%" (tup (Var n))` — see the BuN example below).
The grammar side is a `SpecTecSym`. So `Attr` connects the
expression-world result name to the symbol-world parse rule.

For v1 we only need the simple case: `Ident:Ident-or-paren-group`.
Pattern binders are noted as out of scope.

## Source-of-truth examples

Simple binder:

```
| t:Bvaltype => _RESULT t                    (Bblocktype prod 2)
```

becomes

```
(attr (var "t") (var "Bvaltype"))
```

Inside an iter:

```
| ... (in:Binstr)* 0x0B => BLOCK bt in*      (Binstr/block prod 1)
```

The inner sym for `(in:Binstr)*` is

```
(iter (attr (var "in") (var "Binstr")) list (dom "in" (var "in*")))
```

(The `dom` annotation is task #25; this task only delivers the
`Attr{Var("in"), Var("Binstr")}` part inside.)

Pattern-binder (advanced — OUT OF SCOPE for this task):

```
(attr (case "%" (tup (var "n"))) (var "Bbyte"))     (from TuN)
```

Here the binder is a `Case` pattern. Leave as `Var(text-of-LHS)` for
now — the user-facing impact is small and the fix needs Case-pattern
expression elab on the binder side.

## Token-to-AST mapping for this task

Inside `grammar_sym_from_tokens`'s chunker, when a chunk has shape
`Ident, Colon, <rest>`:

1. The LHS `Ident` is the binder expression — emit `SpecTecExp::Var{id}`.
2. The RHS `<rest>` recursively goes through the chunker (since it
   could be `Btagidx` or `Btagidx(N)` etc.).
3. Wrap in `SpecTecSym::Attr { e, g1 }`.

If the LHS isn't a single `Ident` (e.g. `Case "..."` pattern), emit
the chunk as a `Seq` of its sub-atoms (a `Var` for each Ident) — wrong
but stable until the pattern-binder upgrade.

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - The chunker added in #23 — extend its per-chunk classifier to
    recognise `Ident Colon ...`.
- `crates/covalence-spectec/src/token.rs`: confirm `Token::Colon`
  exists (it does — used elsewhere).

## Approach sketch

```rust
fn chunk_to_atom(chunk: &[Spanned], ctx: &ElabContext) -> SpecTecSym {
    // Binder: `Ident Colon <rest>`
    if chunk.len() >= 3
        && let [Spanned { token: Ident(name), .. }, Spanned { token: Colon, .. }, rest @ ..] = chunk
    {
        let g1 = chunk_to_atom(rest, ctx);
        return Attr {
            e: SpecTecExp::Var { id: name.clone() },
            g1: Box::new(g1),
        };
    }
    // Fall through to atom / parametric-grammar / Num / Text / Eps.
    ...
}
```

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — search for `elab_sym`, `SymG`,
  `AttrG` (or similar variant name). The OCaml constructs `Attr` when
  it sees a `name:G` form in grammar productions.
- Pretty-printer: `spectec/src/backend-ast/print.ml#L149` — confirms
  the `(attr e g)` S-expression shape.

## Testing & validation

After this task `Gram Bcatch`, `Gram Bblocktype` etc. should have
their binder-positions elaborated correctly:

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Gram Bcatch differs/,/^===/p'
```

Compare to OCaml:

```
grep -B1 -A 12 '"Bcatch"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

`Gram` count should rise. `Bcatch` may not be fully clean yet (still
needs #26 for `ps` and #25 for any iter binders).

Unit-test idea (add to `ast_doc.rs#cfg(test)` if a suitable harness
exists, else just rely on the differential):

```rust
let src = "grammar Bcatch : nat = | 0x00 x:Btagidx => 0";
// expect prod g = Seq{[Seq{[Num 0]}, Seq{[Attr{Var("x"), Var("Btagidx")}]}]}
```

## Out of scope

- Pattern binders (`Case "%"` LHS) — note as a known limitation in
  the docstring with a pointer to #34 (path/Case expression elab).
- Iter-with-binder (`(in:Binstr)*` whole-construct) — this task only
  handles the inner `Attr`; the outer `Iter` wrap is #25.
- `dom` annotations on `Iter` — task #25 emits `[]`.
- Computing the prod's `ps` from binders — task #26.
