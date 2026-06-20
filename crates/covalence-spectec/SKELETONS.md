# covalence-spectec — skeletons

Intentional placeholders in `crates/covalence-spectec`. See [CLAUDE.md](../../CLAUDE.md) § Skeletons.

## Partial subsystems

- **`covalence-spectec` → HOL lowering driver** (`crates/covalence-spectec/src/lower.rs`).
  The **untrusted** driver that lowers SpecTec (the DSL the WebAssembly spec is
  written in) into `covalence-core` HOL objects. This is a de-risking slice, not
  coverage. **Covered:** a single-ident `syntax NAME = BASE` *alias* declaration,
  lowered to a kernel `TypeSpec::newtype` over one of a small fixed set of base
  types (`nat`/`bool`/`int`/`bytes`/`unit`), via `lower_top` / `lower_syntax`.
  Tested end-to-end in `tests/lower.rs` (parse snippet → lower → assert the
  `Type`/`TypeSpec` is well-formed and `Term::type_of` round-trips it).
  **Deferred (every other SpecTec form):**
  - `syntax` **variant** and **record** bodies (lower to coproducts / products /
    inductive types — needs constructor lowering + the inductive engine).
  - **parametric** `syntax foo(N)` aliases (lower to a parametric `TypeSpec`
    over type args; currently rejected).
  - alias bodies that are anything other than a bare base-type ident — iter
    postfixes, applications, tuples, function arrows (rejected today).
  - base-type idents outside the fixed map (rejected with "unsupported base
    type"; no general SpecTec-type → kernel-`Type` resolver yet).
  - **`def`** signatures/clauses → HOL defining equations (`Term` + `Thm::define`);
    **`relation`** + **`rule`** → inductive relations / inference rules
    (the `T_wasm` executor-semantics theory). These are the substantive targets;
    the `Lowered` enum is shaped to grow a `TermDef` / `Relation` variant.
  Dependency direction: `covalence-spectec` now depends on `covalence-core`
  (driver imports the kernel; the kernel never imports the driver — no cycle).
  No new TCB surface: every emitted object is re-checked by the kernel.

