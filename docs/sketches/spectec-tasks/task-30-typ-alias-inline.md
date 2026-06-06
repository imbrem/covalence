# Task 30 — Typ: alias-to-variant inlining (Inn, Lnn, Vnn)

**Branch:** `spectec-typ-alias-inline`.
**Dependencies:** none.
**Estimated impact:** Typ +~4 (Inn, Lnn, Vnn — but watch for Pnn
regression risk; see [[phase-h-no-normalization]] for context).
**Risk:** medium — earlier attempt was reverted because the OCaml
behaviour is inconsistent and we couldn't mirror the predicate.

## The big picture

```
syntax Inn hint(show I#N) hint(macro "nt%") = addrtype
syntax addrtype = | I32 | I64
```

OCaml emits Inn as a Variant `{I32, I64}` (inlining addrtype's
cases), NOT as `Alias{addrtype}`. We emit `Alias{addrtype}`.

But:

```
syntax Pnn hint(show I#N) hint(macro "nt%") = packtype
syntax packtype = | I8 | I16
```

OCaml emits Pnn as `Alias{packtype}` (NOT inlined). The hints are
identical to Inn — yet behaviour differs.

This was investigated earlier (memory [[phase-h-no-normalization]]) and
the leading hypothesis is corpus version skew: the vendored
`wasm_spec_ast` was built from a different revision of the spec where
Pnn had different content.

## Intuition

We should not over-engineer this. Two plausible paths:

1. **Brute-force inline**: inline ALL `syntax X = Y` where Y is a
   variant. Helps Inn/Lnn/Vnn (+3) but breaks Pnn (−1). Net +2.
2. **Predicate-based**: figure out OCaml's actual rule from the
   source and mirror it. Likely tied to whether `X`'s `show` hint
   pattern matches `Y`'s case names — but this is a guess.

Recommendation: read OCaml's elaboration code first. If the predicate
is clear, implement it. If not, accept the corpus skew and either:
- Skip this task entirely (corpus mismatch isn't our bug), or
- Implement (1) brute-force inlining with a hardcoded `packtype`
  allowlist for "don't inline" cases.

## Source-of-truth example

OCaml `Inn` (inlined):

```
(typ "Inn" (inst (variant
  (case "I32" (tup))
  (case "I64" (tup))
)))
```

OCaml `Pnn` (not inlined):

```
(typ "Pnn" (inst (alias (var "packtype"))))
```

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - `inst_for_profile` — the `SyntaxBody::Alias` arm currently emits
    `Alias { typ }` unconditionally; add inlining here.
- Existing helper from earlier attempt (since reverted): the
  `expand_variant_alts` function still lives in the file (line
  1287) — reuse.

## Approach sketch

```rust
SyntaxBody::Alias(tr) if predicate_says_inline(syn, tr) => {
    if let Some(target) = single_type_name(&tr.tokens, &ctx.type_names)
        && let Some(expanded) = expand_variant_alts(&target, doc, ctx, visited)
    {
        SpecTecDefTyp::Variant {
            tcs: expanded.iter().map(|a| alt_to_typcase(a, ctx)).collect(),
        }
    } else {
        SpecTecDefTyp::Alias { typ: typ_expr_to_spectec(&tr.tokens, ctx) }
    }
}
```

`predicate_says_inline` is the hard part. Options:

- Read `spectec/src/frontend/elab.ml` for the actual rule.
- Empirically test: does OCaml inline when the parent type name's
  case-set is a SUPERSET / subset / equal-to the target's case set?
- Hardcoded allowlist `["Inn", "Lnn", "Vnn", "Cnn", "Fnn"]` — fragile
  but might do the job.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — search for `elab_syntyp`,
  `elab_alias`, or `inline` / `expand`.
- The relevant commit is the spec revision pinned in
  `wasm_spec_ast`'s build script (look at its `Cargo.toml` for any
  pinned commit hash).

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | grep "^=== Typ Inn\|^=== Typ Lnn\|^=== Typ Vnn\|^=== Typ Pnn"
```

After this task: Inn / Lnn / Vnn should no longer differ. Pnn must
not regress (it currently matches as Alias).

Compare to OCaml for each:

```
for t in Inn Lnn Vnn Pnn; do
  echo "=== $t ==="
  grep -B1 -A 10 "\"$t\"" ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast | head -12
done
```

## Out of scope

- Anything beyond simple alias-to-variant. Other shapes (parametric
  alias, alias-of-alias chains) can be considered if the predicate
  research reveals them.
- Spec-version pinning. If the vendored dump truly disagrees with
  the input spec, we can document the mismatch and skip the
  contentious entries.
