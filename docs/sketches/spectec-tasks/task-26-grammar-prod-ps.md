# Task 26 — Grammar: per-prod `ps` from binders

**Branch:** `spectec-grammar`.
**Dependencies:** #24 (need `Attr` nodes to walk).
**Estimated impact:** Gram +N — completes the structural parity of a
prod after symbols and binders are right.

## The big picture

Just as a `def` clause has a `ps` list of local metavariable bindings
(see commit 3746326), each grammar production has a `ps` list of the
binders introduced by its sym. For `t:Bvaltype => _RESULT t`, the
prod's `ps` is `[Exp{x:"t", t: Var(valtype)}]`.

The type for each ps entry comes from the YIELD type of the bound
grammar. `Bvaltype` yields `valtype`, `Btagidx` yields `tagidx`. We
already store this map in `env.grammars` (built in `build_env` at
`crates/covalence-spectec/src/typecheck.rs:108`).

## Intuition

This is the parser-side analogue of clause `ps`. The work is identical
in spirit to `clause_ps` in `ast_doc.rs:642`:

1. Walk the prod's sym (a `SpecTecSym` tree).
2. For each `Attr { e: Var(x), g1: Var(GName) }` node, look up
   `GName`'s yield type and emit `Exp { x, t: yield }`.
3. Preserve source order, dedupe.

For iterated binders (`(in:Binstr)*`), the ps entry uses the
SUFFIXED name and an `Iter` type: `Exp{x: "in*", t: Iter<instr, List>}`.
This mirrors task #36 (clause-ps iter suffix) — share infrastructure
if both tasks land near each other.

## Source-of-truth examples

Simple binder:

```
| t:Bvaltype => _RESULT t
```

→

```
(prod
  (exp "t" (var "valtype"))             ;; <- prod ps
  (attr (var "t") (var "Bvaltype"))     ;; sym
  (case "_RESULT" (tup (opt (var "t")))) ;; attr expr
)
```

Iterated binder (note `"in*"` and `Iter`):

```
| 0x02 bt:Bblocktype (in:Binstr)* 0x0B => BLOCK bt in*
```

→

```
(prod
  (exp "bt" (var "blocktype"))
  (exp "in*" (iter (var "instr") list))
  (seq ...)
  (case "BLOCK" ...)
)
```

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - `chunk_to_prod` (around line 1525) — populate the prod's `ps`
    field instead of leaving it empty.
  - Likely a new helper `prod_ps_from_sym(&SpecTecSym, &TypeEnv) ->
    Vec<SpecTecParam>` near the grammar lowering code.
- `crates/covalence-spectec/src/typecheck.rs`:
  - `env.grammars` already maps grammar-name → yield type. No change
    needed unless yield types come back as `Bool` (unknown sentinel).

## Approach sketch

```rust
fn prod_ps_from_sym(sym: &SpecTecSym, env: &TypeEnv) -> Vec<SpecTecParam> {
    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    walk(sym, &Iter::None, &mut order, &mut seen, env);
    order
}

fn walk(s: &SpecTecSym, ctx_iter: &Iter, order: &mut Vec<Param>, seen: &mut Set, env: &TypeEnv) {
    match s {
        SpecTecSym::Attr { e: SpecTecExp::Var { id }, g1: box Var { x: gname, .. } } => {
            if seen.insert(id.clone()) {
                let yield_ty = env.grammars.get(gname).cloned().unwrap_or(Bool);
                let (name, ty) = apply_iter(id, yield_ty, ctx_iter);
                order.push(Param::Exp { x: name, t: ty });
            }
        }
        SpecTecSym::Seq { gs } => { for g in gs { walk(g, ctx_iter, ...); } }
        SpecTecSym::Iter { g1, it, .. } => walk(g1, &combine(ctx_iter, it), ...),
        _ => {}
    }
}
```

`apply_iter` produces `("t", Var(valtype))` for `None` ctx and
`("in*", Iter<instr, List>)` for `Some(List)` ctx.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — search for where `Prod` is
  constructed; the `ps` field of grammar prods is populated alongside
  the sym walk.
- `spectec/src/frontend/iter.ml` — the iter-suffix application logic
  may live here.

## Testing & validation

```
cargo test -p covalence-spectec --test elab_differential -- --nocapture
```

Spot-check:

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Gram Bblocktype differs/,/^===/p' | grep -A 12 "ps:"
```

OCaml reference (look at `(exp ...)` lines following each `(prod`):

```
grep -B1 -A 20 '"Binstr"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast | head -60
```

## Out of scope

- Iter-suffix in name (e.g. `"in*"`): implement minimal version
  using the wrapping `Iter` context; the full feature parity with
  clause.ps is task #36.
- Pattern-binder LHS (`Case "%" (tup (var "n"))`) — leave the walk
  guarded on `Attr { e: Var, g1: Var }` only; document the
  limitation in code comments.
