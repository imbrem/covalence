# Task 27 — Grammar: implicit-binder prods (`Bbyte`-style ranges)

**Branch:** `spectec-grammar`.
**Dependencies:** #23 (atoms+Seq), #25 (paren/iter — only loosely; not strictly required if #27 only handles Range).
**Estimated impact:** Gram +5–15 entries (`Bbyte`, similar bare-range grammars).

## The big picture

When a grammar prod is *literally* a range with no source-level
binder, OCaml synthesises an implicit binder so the prod still has a
usable name in the attribute expression. The synthesised binder is
named `<implicit-prod-result>` (verbatim, including the angle
brackets — yes, those are part of the metavar name).

```
grammar Bbyte : byte = 0x00 | ... | 0xFF
```

becomes

```
(prod
  (exp "<implicit-prod-result>" nat)
  (attr (var "<implicit-prod-result>") (range (num 0x00) (num 0xFF)))
  (case "%" (tup (var "<implicit-prod-result>")))
)
```

Currently we emit a `Range` prod with `e: Bool false` sentinel and
`ps: []` — task is to elaborate the implicit binder + canonical case
ctor `"%"` wrapping.

## Intuition

OCaml's grammar elaborator treats `0x00 | ... | 0xFF` as
"this prod's *result expression* is whatever byte we matched; bind
it implicitly because the source didn't name it." The case `"%"` is
SpecTec's "single-hole" identity case — `tup (var "...")` of one
element.

This task is structurally similar to #28 (pattern-literal *Typ*
variants like `syntax byte = 0 | ... | 0xFF`). The difference is the
emission target — task #27 produces a grammar `Prod`, task #28
produces a type `Variant`. They share the "implicit binder name +
range premise" logic; consider sharing a helper.

Note: for `Bbyte` the range bound checks are baked into the
`(range ...)` symbol, so no `If` premise — that's different from #28
which emits a real `If{Cmp}` premise on the type side.

## Source-of-truth example

`grammar Bbyte : byte = 0x00 | ... | 0xFF`:

```
(gram
  "Bbyte"
  (var "byte")
  (prod
    (exp "<implicit-prod-result>" nat)
    (attr (var "<implicit-prod-result>") (range (num 0x00) (num 0xFF)))
    (case "%" (tup (var "<implicit-prod-result>")))
  )
)
```

## Files

- `crates/covalence-spectec/src/ast_doc.rs`:
  - `make_range_prod` (around line 1654) — currently emits
    `Prod { ps:[], g: Range{...}, e: raw_sentinel(), prs:[] }`.
    Replace with the implicit-binder shape above.
  - Probably extract a helper `make_implicit_binder_prod(g_lower,
    g_upper)` that returns the full shape.

## Approach sketch

```rust
fn make_range_prod(lower: &[Spanned], upper: &[Spanned], ctx: &ElabContext, _: Span)
    -> SpecTecProd
{
    let g_lower = grammar_sym_from_tokens(lower, ctx);
    let g_upper = grammar_sym_from_tokens(upper, ctx);
    let bind_name = "<implicit-prod-result>".to_string();
    let range = SpecTecSym::Range { g1: Box::new(g_lower), g2: Box::new(g_upper) };
    SpecTecProd::Prod {
        ps: vec![SpecTecParam::Exp {
            x: bind_name.clone(),
            t: SpecTecTyp::Num(SpecTecNumTyp::Nat),
        }],
        g: SpecTecSym::Attr {
            e: SpecTecExp::Var { id: bind_name.clone() },
            g1: Box::new(range),
        },
        e: SpecTecExp::Case {
            op: MixOp::new(vec!["%".to_string()]),
            e1: Box::new(SpecTecExp::Tup {
                es: vec![SpecTecExp::Var { id: bind_name }],
            }),
        },
        prs: vec![],
    }
}
```

Caveats:
- The case head `"%"` is SpecTec's identity case marker. Verify
  against the OCaml dump that all Bbyte-style prods use it (they do
  for ranges; other patterns vary).
- The bind type is always `Nat` for byte-range prods. For wider
  ranges (e.g. `0x00 ... 0xFFFFFFFF` for `Bu32`) it's still `nat`
  modulo the bounds — OCaml uses `nat` uniformly for these implicit
  binders.
- Use `metadata.implicit_binder_name()` from the OCaml source's
  conventions — the literal string `<implicit-prod-result>` is
  load-bearing for the differential test.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — search for `implicit` or
  `implicit_prod_result` or `<implicit`. Should land in the prod
  elaborator's range-handling branch.
- Pretty-printer: confirm `(case "%" ...)` is what `%` renders as.

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Gram Bbyte differs/,/^===/p'
```

Compare:

```
grep -B1 -A 12 '"Bbyte"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

Should match exactly after this task. Also check `Bu8`, `BuN`,
`Bs33` for similar shape.

## Out of scope

- Cases where the implicit binder gets coerced (e.g. `Bs33` may
  have a Cvt). Handle only the bare range case; document others as
  needing follow-up.
- Sharing infra with #28 — fine to copy-paste for the v1; can DRY
  later.
