# Task 34 — Expr: path expressions + functional update / extend

**Branch:** `spectec-expr-paths`.
**Dependencies:** none.
**Estimated impact:** ~30+ Dec entries (all `alloc*`, `add_*`,
many `store_*` defs).

## The big picture

The `alloc*` and `add_*` defs in the execution semantics use
SpecTec's functional-update syntax to write "the state with field
X extended/updated":

```
def $add_arrayinst(z, ai*) = $sof(z)[.ARRAYS =++ ai*]; $fof(z)
```

The `$sof(z)[.ARRAYS =++ ai*]` is "take `$sof(z)`, extend its
`.ARRAYS` field with `ai*`". Currently this falls back to `Bool
false` because we don't parse path expressions or update/extend.

`SpecTecExp` has `Upd`, `Ext`, `Dot`, `Idx`, `Slice` variants —
target IR exists, just need to lower to them.

## Intuition

A *path* is a sequence of accessors: `.FIELD`, `[i]`, `[i : j]`
(slice). It addresses a sub-component of a structure. A *functional
update* (`e[path := e']`) returns a copy of `e` with `path`
overwritten by `e'`. *Extend* (`e[path =++ e']`) is the same but
appends `e'` to the existing value at `path` (which must be a list).
*Functional extend* (`e[path =.. e']`) is yet another variant — see
spec for exact semantics.

`Path` itself has a small AST: `Root | DotPath(at, Path) | IdxPath
(e, Path) | SlicePath(e1, e2, Path)`. SpecTec's `SpecTecPath` ought
to mirror this — verify in
`~/.cargo/registry/.../spectec_ast-2.0.0/src/`.

## Source-of-truth examples

```
def $add_arrayinst(z, ai*) = $sof(z)[.ARRAYS =++ ai*]; $fof(z)
```

OCaml (subset):

```
(ext
  (call "sof" (exp (var "z")))
  (dot root (mixop "ARRAYS"))
  (iter (var "ai") list ...)
)
```

Where:
- `ext` = `SpecTecExp::Ext { e1: ..., path: ..., e2: ... }`
- `path` = `SpecTecPath::Dot { p1: Root, at: MixOp "ARRAYS" }`

## Files

- `crates/covalence-spectec/src/elab.rs`:
  - New `try_classify_path_update(toks, span, ctx)` recogniser —
    looks for `... [ ... := ...]`, `... [ ... =++ ...]`,
    `... [ ... =.. ...]` at top level.
  - Path itself: extend existing `Path` AST (already partially
    sketched in `elab.rs` — see `Expr::Upd { path }`).
- `crates/covalence-spectec/src/ast_doc.rs`:
  - `expr_to_spectec` — Path conversion already has a stub
    (`path_to_spectec`); make sure it covers Dot / Idx / Slice / Root.

## Approach sketch

1. **Tokenizer**: confirm `=++`, `=..`, `:=` are distinct tokens
   (check `token.rs`). Add if missing.
2. **Path recognition**: at the classifier level, when we see
   `expr [ <path-body> <update-op> <rhs> ]`, split:
   - `<path-body>` parses as a Path (starts with `.` or `[i]`).
   - `<update-op>` chooses between Upd / Ext / one of the variants.
   - `<rhs>` is an expression.
3. **Path parser**: walk `<path-body>` left-to-right. Recognise
   `.FIELD` (Dot), `[i]` (Idx), `[i:j]` (Slice). Compose with
   `Path::Root` as the base.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_path`, `elab_exp_upd`.
- Path AST: `spectec/src/frontend/elab.ml` (or `il/types.ml`) —
  search for `path` / `DotP` / `IdxP` / `RootP`.
- Spec docs: the SpecTec language reference (in upstream repo's
  `docs/`).

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Dec add_arrayinst differs/,/^===/p' | head -80
```

Compare:

```
grep -B1 -A 30 '"add_arrayinst"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

Dec count should jump notably. Watch for grouped wins on
`alloc_*` / `add_*` / `store_*` families.

Unit-test idea:

```rust
let src = r#"
    syntax state = nat
    def $f(state, nat) : state
    def $f(z, n) = z[.FIELD =++ n]
"#;
// Expect e = Ext { e1: Var z, path: Dot{Root, "FIELD"}, e2: Var n }
```

## Out of scope

- The `;`-tupling part of the RHS (`...; $fof(z)`) — task #35.
- Path-with-Iter (`[ai*][.X]`-style chains) — start with simple
  paths; document compound cases as todo.
