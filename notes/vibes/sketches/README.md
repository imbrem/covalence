+++
id = "N002Y"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-03T21:05:38+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Sketches

Forward-looking design sketches — aspirational and informal. When one graduates
into a real plan it moves up to `notes/vibes/` and its sketch is deleted.

## Logic frontends (object logics over the Metamath waist)

Umbrellas: [`../logics/logic-frontends.md`](../logics/logic-frontends.md),
[`../logics/metatheory.md`](../logics/metatheory.md). ACL2/Lisp graduated to
[`../lisp/`](../lisp/).

- [`type-theories.md`](./type-theories.md) — MLTT, book HoTT, NuPRL, and
  IZF/CZF → type-theory translation. Shared judgment-form + binding machinery.
- [`lf-dedukti.md`](./lf-dedukti.md) — LF / λΠ / Dedukti: the smallest dependent
  type theory (built first for the TT infra) and a second universal substrate to
  federate with via a waist-to-waist `≅`.

## Other

- [`acset-datalog-datafun.md`](./acset-datalog-datafun.md) — where a Datafun-style
  typed language slots into the `covalence-acset` recursive-query engine.
- [`covalence-ml-naive-compiler.md`](./covalence-ml-naive-compiler.md) — a
  maximally-naive SML→WASM compiler as the silvered node of the ML→WASM executor
  graph; mature compilers ride alongside as untrusted mirrors. Deferred.
