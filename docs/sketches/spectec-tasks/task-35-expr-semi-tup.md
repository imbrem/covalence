# Task 35 — Expr: headless `;`-tupled def RHS / configs

**Branch:** `spectec-expr-juxt` (do after #32).
**Dependencies:** #32 (shares juxtaposition infra).
**Estimated impact:** Many Dec `alloc*` / `add_*` entries that build
configs (`expr1 ; expr2`).

## The big picture

`syntax config = state; instr*` is a headless single-case variant
with MixOp `["", ";", ""]` (delivered in commit `5edde54` /
`56b4dd6`). In expression position, `e1 ; e2` should lower to a
`Case` of that mixfix constructor:

```
(case "%;%" (tup (var "state") (iter (var "instr") list)))
```

Without this, the `; $fof(z)` part of `def $add_arrayinst` RHS
falls back to sentinel.

## Intuition

Parallel to #32 but with an explicit literal separator (`;` instead
of juxtaposition). Like #32 this requires expected-type-driven
mixfix matching: we know the expected type of the RHS is `state`
(from `def $add_arrayinst(...) : state`), `state` resolves to
`config` (via [hint or alias]; the actual mechanism varies), and
`config`'s sole constructor is `_ ; _`. So `e1 ; e2` should match.

## Source-of-truth example

```
def $add_arrayinst(z, ai*) : state =
  $sof(z)[.ARRAYS =++ ai*]; $fof(z)
```

`state` ≡ `config`'s constructor `_ ; _`. RHS becomes:

```
(case "%;%" (tup
  (ext ...)              ;; from #34
  (call "fof" (exp (var "z")))
))
```

## Files

- `crates/covalence-spectec/src/typecheck.rs`:
  - In `check_exp_against_scope`, before falling to general path:
    if `expected` resolves to a single-case Variant with the
    `["", ";", ""]` mixop AND the expression has a top-level `;`,
    split.
  - Or more generally: check whether expected type has a one-case
    constructor with a literal-only template, and try to match
    arbitrary text against it.
- `crates/covalence-spectec/src/elab.rs`:
  - Recognise top-level `;` in expression classifier as a hint to
    route through mixfix.

## Approach sketch

```rust
// In check_exp_against_scope, before infer+coerce
if let Some(ctor) = single_ctor_with_separator(expected, &env) {
    if let Some(parts) = try_split_by_separator(e_tokens, &ctor.separators) {
        let typed_parts = parts.iter().zip(ctor.arg_types).map(|...| check_exp_against);
        return Expr::Case { head: ctor.name, args: typed_parts };
    }
}
```

`single_ctor_with_separator` extracts the mixop separators for a type
whose variant has exactly one case. Returns `Some` only when the
mixop has at least one non-empty literal between holes.

This is more involved than #32. Consider doing #32 first to share
the splitting infrastructure.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_exp` bidirectional check
  against single-case variant types.
- The mixfix table in OCaml carries the literal-separator pattern;
  the elaborator matches arbitrary expressions against it.

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Dec add_arrayinst differs/,/^===/p'
```

After #34 + #35 the RHS of `add_arrayinst` should fully match OCaml.

Watch the full Dec count — `;`-tupling appears in many RHSes.

## Out of scope

- General mixfix-against-arbitrary-expression matching. Limit to
  single-literal-separator single-case variants (`config = state ;
  instr*`-style).
- Heuristic guesses without expected-type guidance. If the type
  isn't known (e.g. inferred), fall through to current behaviour.
