# Task 37 — Call args: type-check against def signature

**Branch:** `spectec-call-coerce`.
**Dependencies:** none.
**Estimated impact:** Dec entries with nested calls
(`$append(s.X, e*)`-style); also helps Rel premises that reference
defs.

## The big picture

We already type-check Case constructor args against the variant's
`ctor_params` (commit `3746326`). The same pattern needs to apply to
`Expr::Call` against `env.defs[name].params`. Without this, def-call
args bypass coercion — `Eps → Opt(None)`, `T → T?` wrap, variant
subtype on each arg, etc.

## Intuition

In `infer_exp` for `Expr::Call`:
- We already look up `env.defs[name].ret` for the return type
  (commit `30cadab`).
- Need to also look up `env.defs[name].params` and run each arg
  through `check_exp_against_scope` with the corresponding param
  type.

Mirror the Case branch from `infer_exp`:

```rust
Expr::Case { span, head, args } => {
    let params = env.ctor_params.get(&head);
    let new_args: Vec<Expr> = if let Some(params) = params
        && params.len() == args.len()
    {
        args.into_iter()
            .zip(params.iter())
            .map(|(a, expected)| check_exp_against(env, a, expected))
            .collect()
    } else { ... };
    ...
}
```

…and do the same for `Expr::Call`. Hint: `args` for `Call` is
`Vec<TokenRun>` (raw runs), not `Vec<Expr>` — we need to re-classify
each arg with the right expected type. Or convert to `Expr` first
via `classify_token_run`, then check.

## Source-of-truth example

Inspect a Dec with a nested call from `4.0-execution.configurations`:

```
def $append(list, list) : list   ;; or whatever the actual signature
```

Used in `def $foo(...) = $append(z.X, e*)` — the `e*` arg should
coerce to the iter-typed param if the def's sig calls for it.

Hunt for representative Dec entries:

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | grep "^=== Dec" | head -30
# pick one with a Call in the diff
```

## Files

- `crates/covalence-spectec/src/typecheck.rs`:
  - `infer_exp` for `Expr::Call` — already looks up return type;
    extend to coerce args.
  - May want a helper `check_call_args(env, args, sig, ctx)` that
    handles the raw-tokens → Expr classification per arg.
- `crates/covalence-spectec/src/elab.rs`:
  - May need to expose `classify_token_run` (already pub) for the
    per-arg re-classification.

## Approach sketch

```rust
Expr::Call { span, name, args } => {
    let sig = env.defs.get(&name).cloned();
    let new_args: Vec<TokenRun> = if let Some(sig) = &sig {
        args.into_iter().enumerate().map(|(i, tr)| {
            // Re-classify against expected if we have it
            if let Some(SpecTecParam::Exp { t, .. }) = sig.params.get(i) {
                let expr = classify_token_run(&tr, ctx).unwrap_or(Expr::Raw(tr.clone()));
                let typed = check_exp_against(env, expr, t);
                // Convert back to TokenRun? Or change Expr::Call's args
                // representation to Vec<Expr>? See below.
            }
            tr
        }).collect()
    } else { args };
    let t = sig.map(|s| s.ret).unwrap_or_else(unknown_typ);
    (Expr::Call { span, name, args: new_args }, t)
}
```

**Design tension**: `Expr::Call.args: Vec<TokenRun>` is the
historical representation. The lowering in `ast_doc.rs` reclassifies
per arg. We could:
- (a) Change `Expr::Call.args` to `Vec<Expr>`, do classification at
  `Expr::Call` construction time. Bigger change but cleaner.
- (b) Leave as `Vec<TokenRun>`, do the typecheck-coerce inside the
  lowering pass (`expr_to_spectec`) instead. Smaller change but
  duplicates the type-aware logic in two places.

Recommend (a) — it aligns with how Case args are stored and matches
what the typechecker wants. Migrating is a one-pass refactor.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_call_exp` or
  `elab_app`; mirrors `elab_case` (which we replicate for ctor args).

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | grep "^=== Dec" | head -10
```

For each Dec that uses a nested call, check the diff before/after.
Pick a small one to validate first.

Watch the global counts — Dec should rise, others should NOT regress.

## Out of scope

- Coercion against `Param::Typ` / `Param::Gram` / `Param::Def`
  args. Initial focus on `Param::Exp` (the common case).
- Smarter inference when sig has unknown / `Bool` sentinel types.
  Fall through to bare `infer_exp` like the Case branch does.
