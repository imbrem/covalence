# Task 31 — Typ: `Typ` vs `Exp` parametric arg disambiguation

**Branch:** `spectec-typ-arg-kind`.
**Dependencies:** none.
**Estimated impact:** Typ +~15 (`comptype`, `subtype`, anything using
`list(...)`, `option(...)`, similar).
**Risk:** medium — earlier naive attempt regressed Dec by 8 (reverted).

## The big picture

`list(fieldtype)` in a type position should lower to
`SpecTecArg::Typ{t: Var(fieldtype)}`, not `SpecTecArg::Exp{e:
Var(fieldtype)}`. The earlier attempt was "if the arg looks like a
type name, emit Typ" — broke too many Dec entries because Exp-position
arguments to similar-looking calls also got reclassified.

The robust fix: know each parametric type's per-arg KIND from its
declaration. For built-ins (`list`, `option`?), hardcode a registry.
For user-declared `syntax Foo(syntax X, n : nat)`, take the kind from
the param decl.

## Intuition

OCaml's elaborator knows that `list` takes a `Typ` arg and `option`
takes a `Typ` arg, because they're declared that way upstream
(probably in `prelude.watsup` or hardcoded as built-ins). When we
see `list(fieldtype)` at a TYPE position, we look up `list`'s
signature and route arg[0] through type elaboration; for
`some_pred($foo)` at an EXP position, we look up `some_pred`'s sig
and route arg[0] through expression elaboration.

The "look at the call site context" heuristic that broke earlier is
the wrong axis — we need the CALLEE's signature, not the syntactic
position.

## Source-of-truth example

`syntax comptype = | STRUCT list(fieldtype) | ARRAY fieldtype | ...`

OCaml:

```
(case "STRUCT" (tup (bind "_" (var "list" (typ (var "fieldtype"))))))
```

i.e. `Var{x:"list", as1:[Typ{t:Var("fieldtype")}]}`.

We currently emit:

```
(case "STRUCT" (tup (bind "_" (var "list" (exp (var "fieldtype"))))))
```

i.e. `Exp{e:Var(fieldtype)}` instead of `Typ{t:Var(fieldtype)}`.

## Files

- `crates/covalence-spectec/src/typecheck.rs`:
  - Add a parametric-type registry. Could be a `BTreeMap<String,
    Vec<ParamKind>>` in `TypeEnv` (`enum ParamKind { Typ, Exp,
    Gram, Def }`).
  - Populate from user `syntax Foo(...)` decls (read the parens
    list from `syn.decl.params` or wherever).
  - Built-in registrations for `list`, `option`, anything else
    OCaml hardcodes.
- `crates/covalence-spectec/src/ast_doc.rs`:
  - `typ_expr_to_spectec` — when handling the parametric
    `Ident(args)` case, look up the callee in the registry. For
    each arg, route to Typ vs Exp lowering based on its kind.

## Approach sketch

```rust
// In TypeEnv
pub param_kinds: BTreeMap<String, Vec<ParamKind>>,

#[derive(Clone)]
pub enum ParamKind { Typ, Exp, Gram, Def }

// In build_env
// 1. Built-ins
env.param_kinds.insert("list".into(), vec![ParamKind::Typ]);
env.param_kinds.insert("option".into(), vec![ParamKind::Typ]);
// 2. From syntax decls
for syn in &doc.syntax {
    if !syn.params.is_empty() {
        let kinds = syn.params.iter().map(infer_param_kind).collect();
        env.param_kinds.insert(syn.name.clone(), kinds);
    }
}

// In typ_expr_to_spectec, parametric branch
let kinds = ctx.env.param_kinds.get(name);
let arg_specs = arg_chunks.iter().enumerate().map(|(i, chunk)| {
    match kinds.and_then(|k| k.get(i)) {
        Some(ParamKind::Typ) => SpecTecArg::Typ { t: typ_expr_to_spectec(chunk, ctx) },
        _ => SpecTecArg::Exp { e: token_run_to_expr(chunk, ctx) },
    }
}).collect();
```

Note: `typ_expr_to_spectec` currently doesn't have direct `TypeEnv`
access — it's called before/independently of `build_env`. Threading
the registry in may require either:
- Lifting the parametric arg lowering to a post-`build_env` pass, or
- Adding the registry to `ElabContext` (built in `build_table`), or
- Doing a second pass over the converted AST.

The second option is cleanest — `ElabContext` is built before
typecheck so it can carry the built-in / declared kind table.

## Pointers to OCaml

- `spectec/src/frontend/elab.ml` — `elab_typ` /
  `elab_args` / `elab_arg` — search for `ParamT` vs `ExpP` /
  similar discrimination during parametric-type lowering.
- Prelude / built-in registration: `spectec/src/frontend/multiplicity.ml`
  or `spectec/src/frontend/elab_intern.ml` (names approximate; grep
  the OCaml for `"list"` / `"option"`).

## Testing & validation

```
SPECTEC_DIFF_SHOW=300 cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | sed -n '/Typ comptype differs/,/^===/p'
```

Validate against OCaml:

```
grep -B1 -A 12 '"comptype"' ~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast
```

**Critical regression test:** Dec count must NOT drop. Run the full
diff and watch:

```
cargo test -p covalence-spectec --test elab_differential -- --nocapture 2>&1 | grep -E "Typ:|Rel:|Dec:|Gram:"
```

If Dec regresses, the kind table is wrong (a builtin or syntax decl
classified incorrectly). Audit the affected Dec entries to find which
parametric call is being misclassified.

## Out of scope

- Inferring kinds from usage (vs declared). If OCaml infers, mirror
  that — but start with explicit decls.
- Gram / Def args — initial focus on Typ vs Exp; extend later.
