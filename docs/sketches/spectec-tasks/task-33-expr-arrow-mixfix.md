# Task 33 — Expr: ARROW mixfix in operand types (`eps -> valtype?`)

**Branch:** `spectec-expr-arrow`.
**Dependencies:** none.
**Estimated impact:** Many Rel rules. The `instrtype = resulttype ->_(localidx*) resulttype`
mixfix shows up in every `Instr_ok/*`, `Blocktype_ok`, `Block_*`-style rule.

## The big picture

```
syntax instrtype = resulttype ->_(localidx*) resulttype
```

This declares a mixfix constructor where the FULL form is
`resulttype1 ->_(localidx*) resulttype2`. In rules the shorter form
`resulttype1 -> resulttype2` is written when the optional middle
`_(localidx*)` is empty. OCaml's elaborator accepts both forms;
Pratt fails on the short form because the mixfix template's middle
`_(...)` doesn't match.

The pattern generalises: SpecTec mixfix templates can have
"optional" middle slots. We need to recognise them.

## Intuition

OCaml probably encodes this by having the mixfix template's
optional-middle fragments collapse to default values (empty list /
None) when absent. The Pratt parser would then have two parsing
modes for the same op: full and short.

We have backtracking for prefix ops already (commit `1fd5ec7`,
multiple ops sharing a leading literal). Extend to "same op with
optional middle slot."

## Source-of-truth example

Source:

```
rule Blocktype_ok/valtype:
  C |- _RESULT valtype? : eps -> valtype?
  -- (Valtype_ok: C |- valtype : OK)?
```

Conclusion's third operand: `eps -> valtype?`. Expected type:
`instrtype`. OCaml elaborates this to:

```
(case "%->_%" (tup
  (var "eps")  ;; or List{[]}
  (var "...")
  (iter (var "valtype") opt)
))
```

(Exact `%->_%` mixop string TBD — sample the OCaml dump for an
`Instr_ok/*` rule to verify.)

We currently produce `Bool {b: false}` for the entire `eps -> valtype?`.

## Files

- `crates/covalence-spectec/src/elab.rs`:
  - `alt_to_constructor_with_holes` or the mixfix template parser
    in `build_table` — extend to recognise that `_(...)` after `->`
    is an optional iter-position.
- `crates/covalence-spectec/src/mixfix.rs`:
  - `parse_term` / `consume_remaining` — add "skippable optional
    fragment" support. When the next expected lit is the start of an
    optional slot and the input doesn't match, default the
    associated hole to `Eps` / `List{[]}` and continue.

## Approach sketch

1. Mark optional slots in `Op` fragments. Currently:
   ```rust
   pub enum Fragment { Lit(Token), Hole(Precedence) }
   ```
   Extend:
   ```rust
   pub enum Fragment { Lit(Token), Hole(Precedence), OptionalGroup(Vec<Fragment>) }
   ```
2. `template_to_fragments` (in `elab.rs`) emits `OptionalGroup`
   when the source has `_(...)` — define exactly what source syntax
   triggers this; look at the spec for examples.
3. `consume_remaining` checks `OptionalGroup`: try to consume the
   group; on failure, restore input and emit a default `Hole`
   value (`Eps`?) for the hole inside the group.

Alternative: special-case at the relation-template-elab level
without changing Fragment. Parse `_(localidx*)` as an Iter-postfix
on a Hole. The "optional" semantic could be encoded via a different
hole precedence.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_typ` for variant cases;
  `elab_op` / `elab_template` for mixfix templates. Search for
  `Optional` or `_(`-related parsing.
- The spec's syntax for optional mixfix slots is documented in the
  SpecTec language overview (search `docs/spectec.md` in the
  upstream repo).

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Rel Blocktype_ok differs/,/^===/p'
```

Compare:

```
grep -B1 -A 40 '"Blocktype_ok"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast | head -50
```

Coverage rise: Rel should jump. Expect to also unblock `Comptype_ok`,
`Instr_ok/*` (any rule using `instrtype`).

## Out of scope

- Generalising "optional mixfix slot" to arbitrary positions. Start
  with the `_(localidx*)`-after-arrow pattern; broaden if/when
  other ops need it.
- The full mixfix template language. We only need enough to handle
  what wasm-3.0 uses.
