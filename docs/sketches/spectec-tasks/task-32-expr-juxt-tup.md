# Task 32 — Expr: implicit-Tup juxtaposition (`(mut zt)`)

**Branch:** `spectec-expr-juxt`.
**Dependencies:** none — but #35 (`;`-tupled) is a natural follow-up
on the same branch.
**Estimated impact:** Many Rel premises (ARRAY/STRUCT/FUNC with tuple
args), several Dec entries. Hard to estimate precisely without
landing — at minimum unblocks Rel `Arrayinst_ok`, `Comptype_sub`,
and similar.

## The big picture

In SpecTec source, `ARRAY (mut zt)` passes `(mut zt)` as a single
arg. Inside the parens, `mut zt` has no commas — it's an implicit
tuple split by juxtaposition. The destination type for that arg is
`fieldtype = mut? storagetype` — a 2-element tuple type. So
`(mut zt)` should split into `(mut, zt)` against the expected shape.

Currently `(mut zt)` fails the Pratt parse (`mut zt` doesn't match
any single mixfix op), and we fall back to a `Raw` arg → `Bool
false` sentinel.

This is "expected-type-driven implicit splitting": when an inner
juxtaposition is being checked against a `Tup` type of N binds, and
the inner has N type-shaped sub-chunks separated only by
juxtaposition, split into N elements.

## Intuition

We already do something analogous for case ctor args (commit
`3746326` `ctor_params` → `check_exp_against` per arg). This task
generalises: when the EXPECTED type is `Tup{N binds}` and the
expression is a `Raw` / fell-back chunk with N juxtaposed sub-types,
re-interpret it as an N-tuple.

The structural analogue is `chunk_to_atom` in the grammar task
(#23) — same juxtaposition splitting logic, applied at the
expression level when guided by expected type.

## Source-of-truth example

From `assets/spectec/wasm-3.0/7.1-soundness.configurations.spectec`:

```
rule Arrayinst_ok:
  s |- {TYPE dt, FIELDS fv*} : OK
  -- Expand: dt ~~ ARRAY (mut? zt)
```

Inside `ARRAY (mut? zt)`, the expected type for ARRAY's arg is
`fieldtype = mut? storagetype` = `Tup{[Bind(mut?, mut?), Bind(zt,
storagetype)]}`. Our elaboration should produce:

```
(case "ARRAY" (tup
  (tup
    (opt (case "MUT" (tup)))   ;; or similar mut? lowering
    (var "zt")
  )))
```

We currently produce `Bool{b: false}` for the entire `(mut? zt)`
inner.

## Files

- `crates/covalence-spectec/src/typecheck.rs`:
  - `check_exp_against_scope` — add a branch: when `e` is
    `Raw`/`Var`/anything-that-looks-like-juxtaposition and `expected`
    is `Tup{N binds}`, try splitting via juxtaposition.
- `crates/covalence-spectec/src/elab.rs`:
  - May need a helper that returns a `Vec<Expr>` from a juxtaposed
    chunk + expected types — re-attempts classification per chunk.

## Approach sketch

```rust
// In check_exp_against_scope, before falling to general path
if let (Expr::Raw(tr) | Expr::Tup { items: small_chunk_of_idents, .. }, Typ::Tup { ets }) = (&e, expected) {
    if let Some(items) = try_split_juxtaposed_against(tr_or_chunk, ets.len(), env, ctx) {
        // Recursively check each item against its bind type.
        let items = items.into_iter().zip(ets).map(|(it, bind)| {
            check_exp_against_scope(env, it, &bind.typ, scope)
        }).collect();
        return Expr::Tup { span: tr.span, items };
    }
}
```

`try_split_juxtaposed_against` walks the token stream, finds N
type-shaped chunks at depth 0, re-classifies each into an `Expr`.
If N doesn't match expected, return None and fall through.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_exp` with a `TupT`
  expected type, search for "juxtaposition" or implicit-tup handling.
- The pattern is the same as our grammar juxtaposition (#23) but
  on the expression side.

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Rel Arrayinst_ok differs/,/^===/p' | head -100
```

Watch the Tup inside ARRAY in the premise's Expand.

OCaml reference:

```
grep -B1 -A 60 '"Arrayinst_ok"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast | head -80
```

Coverage rises across Rel and Dec — Rel should jump notably (many
rules have this shape).

## Out of scope

- `;`-separated juxtaposition (e.g. `state ; instr*` in config) —
  task #35.
- Mixfix-recognition of compound operators inside the juxtaposition.
  Keep this task to "split into N chunks against expected Tup arity";
  the per-chunk elab uses existing infra.
