# Lisp — the `SExpr → Reduction → Lisp → ACL2` tower

The Lisp frontend is built as a **tower**, each layer a clean, tested API the next sits on:

| Layer | What it is | Crates |
|---|---|---|
| **SExpr** | the S-expression API — read/print/build/hash + the kernel S-expression datatype and its computation laws. **The foundation.** | `covalence-sexp` (surface tree + reader/printer/visitor), the kernel `sexpr` type (`init/inductive/`) |
| **Reduction** | parametric certified reduction — a `Reduces` step relation, generic in *representation × semantics × strategy* ([`initial-ideas/parametric-reduction.md`](./initial-ideas/parametric-reduction.md)). Print only after a kernel `Thm`. | `covalence-repl` (traits), `covalence-lisp` (impls) |
| **Lisp** | a dialect over the reduction layer: reader → resolve (symbols/numbers/strings) → reduce → print; the REPL + `/lisp` endpoint | `covalence-lisp` |
| **ACL2** | ACL2 as a dialect + discipline (mandatory measures, the-method) on the Lisp | later |

Peers on the concatenative axis (`/forsp`, `/forth`) ride the same reduction layer;
`covalence-forsp` already exists.

## This push: polish the foundation

The S-expression API is load-bearing for everything above, so this push **cleans, tests,
and polishes it thoroughly** — including dropping the `carved` jargon in favor of plain
**S-expression** naming *in the code*, not just the docs.

**Rename (do it as we build, test-gated):** `CarvedSExpr → SExpr`-family naming
(bundle/accessor/file/backend), `carved.rs → sexpr.rs`, `carved() → sexpr…()`,
`carved_backend() → sexpr…_backend()`. The HOL datatype stays `sexpr`. Naming decision to
lock: the kernel bundle name must not clash with `covalence_sexp::SExpr` (the surface
tree) — candidates `SExprTheory` / `HolSExpr` / `SExprHol` (bundle) + `sexpr_theory()`.
Coordinate the rename with the `covalence-lisp` build so the kernel and its first consumer
move together and `cargo test` stays green throughout.

**Polish/test targets for the S-expression API:**
- `covalence-sexp`: round-trip (parse ∘ print = id) property tests across dialects; the
  event/`SExpBuilder` path; the deparse gap ([`initial-ideas/parsing-relations.md`](./initial-ideas/parsing-relations.md)).
- kernel `sexpr`: the computation laws (`car`/`cdr`/`cons`/`consp`/`atom?`/`eq`) exercised
  as kernel theorems; the recursor/induction; a clean, documented lowering `SExpr → sexpr`.

## Map

- [`minimal-spec/`](./minimal-spec/) — the buildable spec: [`README.md`](./minimal-spec/README.md), [`implementation-plan.md`](./minimal-spec/implementation-plan.md), [`lisp.wit`](./minimal-spec/lisp.wit).
- [`initial-ideas/`](./initial-ideas/) — the design corpus: parametric-reduction, reduction-relations-and-state, generic-repl-trait, lisp-dialects-and-order, parsing-relations, content-addressing-sexpr, lisp-frontend-sketch, lisp-acl2-answers, acl2-lisp.
- [`abstract-sexpr-api.md`](./abstract-sexpr-api.md) — reusable-API design: the
  `AbstractSExpr` carrier trait (carved `sexpr` / ACL2 `A` / surface `SExpr` as
  impls) + the abstract reduction axes (equational / relational / certificate
  shapes, `Composer` split, `CertifiedEval`, transport exit) with a sliced
  migration plan.
- Status report: [`STATUS.md`](./STATUS.md) once the first build lands.
- ACL2: [`acl2-full-plan.md`](./acl2-full-plan.md) (the governing S0–S12 plan),
  [`acl2-s7-s12-plan.md`](./acl2-s7-s12-plan.md) (remaining stages, concretely),
  [`acl2-fidelity.md`](./acl2-fidelity.md) (assumptions/deviations ledger),
  [`acl2-agent-guide.md`](./acl2-agent-guide.md) (agent orientation: module map, patterns, gotchas, process),
  stage designs [`acl2-s0-s3-design.md`](./acl2-s0-s3-design.md) /
  [`acl2-s4-s6-design.md`](./acl2-s4-s6-design.md) /
  [`acl2-s5-design.md`](./acl2-s5-design.md) (each with implementation reports),
  [`acl2-book-frontend.md`](./acl2-book-frontend.md) (book import pipeline),
  [`acl2-premise-builder.md`](./acl2-premise-builder.md) (generic induction
  premise builder: object-level simplifier + IH splicing — the
  surface-defthm → S6-kernel-path design),
  [`acl2-dialect.md`](./acl2-dialect.md) (slice-1 dialect notes).
