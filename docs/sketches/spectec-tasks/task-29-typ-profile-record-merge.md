# Task 29 — Typ: profile-merged record bodies

**Branch:** `spectec-typ-profile-merge`.
**Dependencies:** none.
**Estimated impact:** Typ +~10 (`context`, `module`, `state`, `frame`,
similar split-profile records).

## The big picture

SpecTec lets you split a syntax decl across multiple "profile" tags
and use `...` to splice them together:

```
syntax context/syn = { TYPES deftype*, ... }
syntax context/sem = { RECS subtype*, ..., LOCALS localtype* }
```

OCaml merges these into ONE Inst with the combined field list (in
the splice-resolved order). We currently emit one Inst per profile,
each with that profile's local fields — so `context` ends up with
two distinct Insts in our output.

Our variant-side merging already does this via
`MergedSyntax::alts_for_profile` + `splice into ...`. Record-side
needs the same treatment.

## Intuition

The variant merging walks each profile's alts in source order, and
when it hits `...` (a placeholder alt), substitutes in the other
profiles' real alts. The record analogue is the same algorithm but
walking *fields* instead of *alts*, with a "field placeholder" notion
to detect.

In source, the `...` inside a record body is the same `DotDotDot`
token we already handle for variants. The difference: variant `...`
is a whole alt, record `...` is a whole field (between commas).

## Source-of-truth examples

`context` from the spec:

```
syntax context/syn = { TYPES deftype*, ... }
syntax context/sem = {
  RECS subtype*, ..., LOCALS localtype*
}
```

OCaml's merged Inst:

```
(typ "context"
  (inst (struct
    (field "RECS"  (iter (var "subtype") list))
    (field "TYPES" (iter (var "deftype") list))
    ;; ... in source order with /sem's `...` slot filled by /syn's fields
    (field "LOCALS" (iter (var "localtype") list))
  )))
```

(Field order in our current output: `/syn` fields first, then `/sem`
fields — wrong because `/sem`'s fields come BEFORE its `...` slot
where `/syn`'s fields should go.)

## Files

- `crates/covalence-spectec/src/elab.rs`:
  - `MergedSyntax` / `add_syntax_to_merge` — extend to track record
    bodies similarly to variants.
  - Add a `fields_for_profile(profile)` analogous to
    `alts_for_profile`.
- `crates/covalence-spectec/src/cst.rs`:
  - `SyntaxBody::Record(Vec<RecordField>)` — may need a placeholder
    field marker or a `Vec<RecordSlot>` analogous to variants'
    `AltSlot`.
- `crates/covalence-spectec/src/parse.rs`:
  - `parse_record_body` — recognise top-level `...` between commas
    as a placeholder slot.
- `crates/covalence-spectec/src/ast_doc.rs`:
  - `inst_for_profile` — emit fields via the merged view.
  - The existing `insts.dedup()` will then collapse the two
    identical merged Insts into one.

## Approach sketch

1. Add `enum RecordSlot { Placeholder, Real(RecordField) }` parallel
   to `AltSlot`.
2. `parse_record_body` emits one slot per comma-separated chunk
   (`...` → `Placeholder`, normal → `Real(field)`).
3. `MergedSyntax` stores per-profile slot lists for record bodies
   (separate from `profiles[]` variant slots, or unified — caller's
   call).
4. `fields_for_profile(p)` walks `p`'s slots; when it hits
   `Placeholder`, splices in all OTHER profiles' `Real` fields in
   source order. Same algorithm as variant `alts_for_profile`.
5. `inst_for_profile` uses this merged view to build `Struct.tfs`.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_typ` /
  `elab_syntax_record` (or similar). The record-merging algorithm
  is the same logic as variant `...` splicing, applied to fields.
- `MergedSyntax` in our codebase is the model — mirror its shape
  for records.

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Typ context differs/,/^===/p'
```

Compare:

```
grep -B1 -A 30 '"context"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast | head -40
```

Should:
- Reduce `context`'s `insts.len()` from 2 → 1.
- Match field count AND order against OCaml.

Add unit test exercising the splice:

```rust
let src = r#"
    syntax foo/syn = { A nat, ... }
    syntax foo/sem = { B nat, ..., C nat }
"#;
// Expect one merged Inst with fields [B, A, C] (sem order: B before ...,
// ... resolves to /syn's [A], then C).
```

## Out of scope

- Variant-side merging — already works (commit `ee836f1`'s dedup).
- Field-with-hint preservation — keep the existing hint extraction
  per field.
