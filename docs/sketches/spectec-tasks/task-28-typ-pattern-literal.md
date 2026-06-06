# Task 28 — Typ: pattern-literal variants (`bit`, `byte`, `char`)

**Branch:** `spectec-typ-pattern-lit`.
**Dependencies:** none (independent of the grammar branch).
**Estimated impact:** Typ +~15 (bit, byte, char, s33, iN, sN, fN, f32,
f64, i32, i64, i128, name, oktypenat, dim, …).

## The big picture

When a `syntax` decl's body is a list of pure literal alternatives
(`syntax bit = 0 | 1`, `syntax byte = 0 | ... | 0xFF`, `syntax char =
U+0000 | ... | U+D7FF | ...`), OCaml elaborates it to a SINGLE
variant case with:

- One implicit-binder operand (typed `nat`).
- A predicate premise constraining the binder to the literal set.

We currently emit one Variant case PER literal, each with MixOp
`"natural-number literal"` and empty operand list — structurally
miles off.

## Intuition

Conceptually `bit = 0 | 1` is "a bit is some natural number `i` such
that `i = 0 ∨ i = 1`." OCaml encodes that as:

```
Variant {
    Field {
        op: ["",""],          ;; identity mixop with one hole
        t: Tup{[Bind{id:"i", typ:Nat}]},
        prs: [If{i==0 ∨ i==1}],
    }
}
```

This is the type-side analogue of grammar task #27. Both synthesise
an implicit binder when the source is a pure pattern. The two could
share a helper but it's fine to copy.

## Source-of-truth examples

### `bit` — two literal alts

Source: `syntax bit = 0 | 1`

OCaml:

```
(typ "bit"
  (inst
    (variant
      (case "%"
        (tup (bind "i" nat))
        (if
          (bin or bool
            (cmp eq bool (var "i") (num (nat 0)))
            (cmp eq bool (var "i") (num (nat 1)))))))))
```

### `byte` — range with `...`

Source: `syntax byte = 0 | ... | 0xFF`

```
(typ "byte"
  (inst
    (variant
      (case "%"
        (tup (bind "i" nat))
        (if
          (bin and bool
            (cmp ge nat (var "i") (num (nat 0)))
            (cmp le nat (var "i") (num (nat 0xFF)))))))))
```

### `char` — mix of ranges

Source: `syntax char = U+0000 | ... | U+D7FF | U+E000 | ... | U+10FFFF`

OCaml emits compound Or-of-And ranges; same shape as `byte` with the
right disjunction.

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - In the `Variant` body lowering — detect "all alts are pure
    literal patterns (no idents in `type_names`)" and re-route to
    `make_pattern_literal_variant`.
  - New helper: classify alts into ranges (`a | ... | b`) and
    singletons; synthesise the binder + If premise.

## Approach sketch

```rust
fn try_pattern_literal_variant(alts: &[Alt]) -> Option<SpecTecTypCase> {
    let lits = alts.iter()
        .map(classify_literal_alt)
        .collect::<Option<Vec<LitOrRange>>>()?;
    let binder_name = pick_binder_name(alts);  // "i" by default
    let cond = build_range_condition(&lits, &binder_name);
    Some(SpecTecTypCase::Field {
        op: MixOp::new(vec!["".into(), "".into()]),
        t: SpecTecTyp::Tup { ets: vec![Bind { id: binder_name, typ: Nat }] },
        qs: vec![],
        prs: vec![SpecTecPrem::If { e: cond }],
    })
}
```

`pick_binder_name`: look at the spec's convention — `i` for byte/bit,
`n` for nat-ranges. Inspect the OCaml dump per type. Could just use
`i` uniformly if matches OCaml; verify per type.

`build_range_condition`: emit `Or` of `Cmp Eq` for singletons,
`And{Ge, Le}` for ranges, combined with `Or`.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — search for `pat_typ` /
  `lit_pat` / `range_pat`. The pattern-literal-to-implicit-binder
  pass lives there.
- For the canonical binder name, search the OCaml for
  `"i"` / `"n"` constants used during this lowering.

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Typ bit differs/,/^===/p'
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Typ byte differs/,/^===/p'
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Typ char differs/,/^===/p'
```

Compare to OCaml:

```
grep -B1 -A 12 '"bit"\|"byte"\|"char"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

Add a unit test in `ast_doc.rs#cfg(test)`:

```rust
let src = "syntax bit = 0 | 1";
let doc = build_test(src);
let typ = doc.find("bit").unwrap();
assert_matches!(typ, /* one case with If premise */);
```

## Out of scope

- `oktypenat` shape (might be more complex — investigate
  separately).
- Sharing with task #27 — copy first, DRY if both land.
- `dim`/`ishape` (might have non-literal alts mixed in) — start with
  the pure cases; document non-pure as todo.
