# SpecTec elaboration — remaining task tree

Coverage snapshot (commit `56b4dd6`, run `cargo test -p covalence-spectec --test elab_differential -- --nocapture`):

```
Typ:  130 / 206  (63.1%)
Rel:   18 / 125  (14.4%)
Dec:   67 / 461  (14.5%)
Gram:  11 / 231   (4.8%)
```

Each task here is a self-contained unit of work with a concrete acceptance
criterion: the per-kind deep-equality count (or specific named entries)
should rise after the task lands, with no other entry regressing.

## Suggested branches

Group adjacent tasks where the implementation overlaps; otherwise one
branch per task.

| Branch | Tasks | Why grouped |
| --- | --- | --- |
| `spectec-grammar` | 23, 24, 25, 26, 27 | Tightly coupled — all touch `grammar_sym_from_tokens` and the prod emitter. |
| `spectec-typ-pattern-lit` | 28 | Standalone, but shares "implicit binder" helper with #27. |
| `spectec-typ-profile-merge` | 29 | Standalone — touches `MergedSyntax`. |
| `spectec-typ-alias-inline` | 30 | Standalone, low-risk investigation. |
| `spectec-typ-arg-kind` | 31 | Standalone — introduces parametric-type registry. |
| `spectec-expr-juxt` | 32, 35 | `;`-tupled RHS reuses juxtaposition infra. |
| `spectec-expr-arrow` | 33 | Standalone — mixfix tweak. |
| `spectec-expr-paths` | 34 | Standalone — new Expr lowering paths. |
| `spectec-clause-iter` | 36 | Standalone — small fix in `collect_var_names_in_expr`. |
| `spectec-call-coerce` | 37 | Standalone — extends `infer_exp` for Call. |

Total: **10 branches**.

## Dependency graph

```
spectec-grammar
└── 23 (atoms+Seq)
    ├── 24 (binders) → 26 (prod ps)
    └── 25 (iter+paren)
        └── 27 (implicit-binder ranges)        [also depends on 23]

spectec-typ-pattern-lit
└── 28 (pattern-literal variants)

spectec-typ-profile-merge
└── 29 (profile record merging)

spectec-typ-alias-inline
└── 30 (Inn/Lnn/Vnn inlining)

spectec-typ-arg-kind
└── 31 (Typ vs Exp parametric arg)

spectec-expr-juxt
└── 32 (juxtaposition Tup)
    └── 35 (`;`-tupled config / RHS)

spectec-expr-arrow
└── 33 (ARROW in operand types)

spectec-expr-paths
└── 34 (Dot / Idx / Upd / Ext)

spectec-clause-iter
└── 36 (iter suffix in clause.ps)

spectec-call-coerce
└── 37 (call args vs def sig)
```

No cross-branch dependencies — each can be developed and merged independently.

## Background reading

- `crates/covalence-spectec/CLAUDE.md` — crate-level conventions.
- `crates/covalence-spectec/src/lib.rs` — module layout, "no unsafe" rule.
- `docs/sketches/spectec-verification-plan.md` — strategic context.
- `crates/covalence-spectec/tests/elab_differential.rs` — the differential harness.
- The OCaml reference dump lives in
  `~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/wasm_spec_ast-1.0.1/src/wasm-3.0.spectec-ast`
  — searchable for the expected output of any def by name.

## Hygiene for every branch

- `cargo test -p covalence-spectec` must pass (123 unit + 1 differential).
- The differential coverage numbers may NEVER regress on any kind.
- New code follows the "no unsafe, no interior mutability, no global state"
  rule from `lib.rs`.
- Add a per-task entry to the differential test's expected count if the task
  lands a known improvement (so a future regression flags loudly).
