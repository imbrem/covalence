# Task 36 — Clause-ps: preserve iter suffix (`ai*` not `ai`)

**Branch:** `spectec-clause-iter`.
**Dependencies:** none.
**Estimated impact:** ~50 Dec entries (any def whose clause args use
iterated metavars).

## The big picture

`def $add_arrayinst(z, ai*)` has clause.ps[1] = `Exp{x: "ai*", t:
Iter<arrayinst, List>}` in OCaml. We emit `Exp{x: "ai", t:
Var(arrayinst)}` because `collect_var_names_in_expr` walks through
`Iter` and only records the bare inner name.

The fix is targeted and small:
1. When the collector encounters `Iter{Var(n), kind}`, record `n` +
   iter-suffix together as the binder name, AND propagate the iter
   kind so the type lookup wraps in the right `Iter<...>`.
2. The positional sig lookup in `clause_ps` must combine the bare
   sig type with the recorded iter to produce the final `Iter<T,
   kind>`.

## Intuition

A binder like `ai*` is a single thing in clause scope — a list of
arrayinst. Calling it `ai` loses the "is a list" information; the
suffixed `ai*` carries it. OCaml preserves the suffix in the binder
name AND wraps the type. We need to do both.

## Source-of-truth example

```
def $add_arrayinst(state, arrayinst*) : state hint(show ...) ...
def $add_arrayinst(z, ai*) = ...
```

OCaml:

```
(clause
  (exp "z" (var "state"))
  (exp "ai*" (iter (var "arrayinst") list))
  ...
)
```

We currently emit:

```
(clause
  (exp "z" (var "state"))
  (exp "ai" (var "arrayinst"))
  ...
)
```

## Files

- `crates/covalence-spectec/src/typecheck.rs`:
  - `collect_var_names_in_expr` (around line 795) — when matching
    `Expr::Iter { inner, kind, .. }` where inner is a `Var`,
    record the suffixed name (e.g. `"ai*"`) instead of recursing
    into the bare `Var`.
- `crates/covalence-spectec/src/ast_doc.rs`:
  - `clause_ps` — when looking up the type, if the name has an
    iter suffix (`*`, `?`, `+`), strip it for the env/sig lookup
    and re-wrap the result in `Iter<base, kind>` with the
    appropriate `SpecTecIter` variant.

## Approach sketch

```rust
// In collect_var_names_in_expr
Expr::Iter { inner, kind, .. } => {
    if let Expr::Var { name, .. } = inner.as_ref() {
        let suffix = iter_kind_to_char(kind);  // '*', '?', '+'
        let suffixed = format!("{name}{suffix}");
        if seen.insert(suffixed.clone()) {
            order.push(suffixed);
        }
    } else {
        collect_var_names_in_expr(inner, order, seen);
    }
}

// In clause_ps lookup
let (base, suffix) = strip_iter_suffix(&name);  // already exists at line 807
let base_typ = lookup_base_type(base, sig_ps, env);
let wrapped = wrap_in_iters(base_typ, &suffix);  // already exists at line 736
```

`strip_iter_suffix` and `wrap_in_iters` already exist in typecheck.rs
— reuse.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_def_clause`, search for
  iter-suffix handling in binder collection.
- The pattern is the same as what we already implement for rule.ps
  in `collect_rule_params` (typecheck.rs line 698) — possibly worth
  unifying.

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Dec add_arrayinst differs/,/^===/p' | head -40
```

OCaml reference:

```
grep -B1 -A 30 '"add_arrayinst"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

Should fix the `ai*` vs `ai` binder shape across many Dec entries.
Note: the RHS may still mismatch (tasks #34, #35) but the clause.ps
list should be right.

Add unit test:

```rust
let src = r#"
    syntax foo = nat
    def $f(state, foo*) : state
    def $f(z, x*) = z
"#;
let doc = build_test(src);
let dec = doc.find_def("f");
// Expect clauses[0].ps = [Exp{z, state}, Exp{x*, Iter<foo, List>}]
```

## Out of scope

- Suffix on non-Var inner (e.g. `(a, b)*` — tuple iter). Start with
  the `Var*` case; document the rest as todo.
- Multi-level iter (`a**`). Same approach but with two suffix chars
  — extend if seen in practice.
