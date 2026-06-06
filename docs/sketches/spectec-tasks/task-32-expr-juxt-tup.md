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

### Step 1 — the simple branch (already attempted; insufficient on its own)

In `check_exp_against_scope`, before the general path:

```rust
if let (Expr::Raw(tr), Typ::Tup { ets }) = (&e, expected)
    && let Some(chunks) = try_split_juxtaposed(&tr.tokens, ets.len())
{
    let items: Vec<Expr> = chunks
        .into_iter()
        .zip(ets)
        .map(|(chunk, bind)| {
            let inner = mini_classify_chunk(chunk, chunk_span);
            check_exp_against_scope(env, inner, &bind.typ, scope)
        })
        .collect();
    return Expr::Tup { span, items };
}
```

`try_split_juxtaposed(toks, n)` walks at depth 0; each chunk is one
ident (+ optional iter postfix), one literal, or one balanced paren
group. `mini_classify_chunk` handles `Ident → Var`, `Ident*/?/+ →
Iter{Var}`, `Nat → Num`, `Text`, `eps → Eps`, else `Raw`. (Doesn't
need `ElabContext` for these simple shapes — full re-classification
via `classify_simple_expression` would require threading `ctx`
through the typecheck pass.)

I implemented this branch (commit on the `WIP #32` stash entry in the
covalence-spectec branch — recover with
`git stash list | grep "WIP #32"` and `git stash apply`) but it
does NOT move the differential count, because…

### Step 2 — the critical second piece (NOT YET DONE)

Most real sites have expected type `Var(name)`, not `Tup{...}`
directly. Example: `ARRAY (mut zt)` — ARRAY's ctor_params[0] is
`Var(fieldtype)`, not `Tup`. The Step-1 branch never fires.

To make it useful: when expected is `Var(name)` and `name`
resolves (via `env.ctors` reverse lookup or `doc.syntax`) to a
**single-case headless variant** whose case body is a `Tup{binds}`,
unfold and re-route:

```rust
// Pseudo-code addition before Step 1
if let Typ::Var { x: name, .. } = expected
    && let Some(headless_tup) = resolve_headless_tup_body(name, env)
{
    // Run the Step-1 splitter against headless_tup's binds.
    let inner_tup = check_exp_against_scope_with_tup(env, e, &headless_tup, scope);
    // Wrap as a Case of the headless variant's MixOp (e.g. `["","",""]`
    // for fieldtype, mirroring the OCaml `(case "%%" (tup ...))` shape).
    return Expr::Case {
        span, head: name.clone(),  // or whatever surfaces as the headless head
        args: vec![inner_tup],
    };
}
```

This needs:
1. A `headless_variant_body: BTreeMap<String, (MixOp, Vec<TypBind>)>`
   added to `TypeEnv`. Populate at `build_env` time by walking
   each syntax's single-case headless variants
   (`fieldtype = mut? storagetype`, `instrtype = ... -> ...`,
   `globaltype = mut? valtype`, …).
2. The unfold-and-wrap step above.
3. The lowering of the synthesised `Case` head — OCaml emits these
   as `Case { op: ["","",""], ... }` with no name field. Verify how
   our `Expr::Case { head: String, args }` round-trips through
   `expr_to_spectec` for headless cases.

Without (1)+(2)+(3) the simple branch in Step 1 is dead code.

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
