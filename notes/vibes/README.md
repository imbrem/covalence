# notes/vibes/ — the AI-generated design corpus

Design notes and plans, organized by area. Deleted material is recoverable from
git history (and `backup/pre-hol-cleanup` for the pre-HOL-cleanup pass).

## Start here

| Doc | What it covers |
|---|---|
| [`vision/project-map.md`](./vision/project-map.md) | The map — crate groups + active threads, each with status + pointers. |
| [`vision/VISION.md`](./vision/VISION.md) | The system vision: metatheory-as-default, executors → HOL → internal Metamath waist, scoped truths. |
| [`vision/k-framework-vision.md`](./vision/k-framework-vision.md) | North star: full K + all sublanguages, the K-Wasm ⟷ SpecTec goal. |
| [`vision/roadmap.md`](./vision/roadmap.md) | Time-to-product for the Metamath vision (set.mm in GT; analysis in SOA). |
| [`kernel/tcb/what-is-the-tcb.md`](./kernel/tcb/what-is-the-tcb.md) | The TCB in human terms: trusted crates, mint sites, admitted rules. |
| [`../design/README.md`](../design/README.md) | The design-doc queue (decision records with status). |

## `kernel/` — the TCB and its design

Read `kernel-design.md` before touching the trusted base.

| Doc | What it covers |
|---|---|
| [`kernel/kernel-design.md`](./kernel/kernel-design.md) | `covalence-core`, the TCB: term/type representation, the rule surface, the `defs/` catalogue. |
| [`kernel/closed-world-kernel.md`](./kernel/closed-world-kernel.md) | Current kernel direction: first-order theories in the type system; soundness by uniqueness-of-implementation. |
| [`kernel/pure-design.md`](./kernel/pure-design.md) | The value-directed `Thm<C,P>` floor: `Stmt`/`Rule`/`Derive`, nuclei & bridges, content-addressing + federation. |
| [`kernel/base-relcalc-holomega-design.md`](./kernel/base-relcalc-holomega-design.md) | Authoritative base + middle redesign: base as a relations-as-untrusted-functions calculus; middle retargeted to HOL-ω. |
| [`kernel/type-hierarchy.md`](./kernel/type-hierarchy.md) | The equality hierarchy + the `defs/` type catalogue (nat/int/rat/real/bytes/list/…). |
| [`kernel/covalence-fol.md`](./kernel/covalence-fol.md) · [`kernel/base-abstraction.md`](./kernel/base-abstraction.md) · [`kernel/base-api-surface.md`](./kernel/base-api-surface.md) · [`kernel/defs-rehome-design.md`](./kernel/defs-rehome-design.md) | Base API surface, the typed-repr FOL sketch, and the active defs re-home. |

**`kernel/tcb/`** — [`what-is-the-tcb.md`](./kernel/tcb/what-is-the-tcb.md) · [`soundness-audit.md`](./kernel/tcb/soundness-audit.md) · [`tcb-holomega-roadmap.md`](./kernel/tcb/tcb-holomega-roadmap.md)
**`kernel/literals/`** — the leaf-elimination endgame: [`literal-endgame-design.md`](./kernel/literals/literal-endgame-design.md) · [`eg5-preflight.md`](./kernel/literals/eg5-preflight.md) · [`sha256-round-keystone.md`](./kernel/literals/sha256-round-keystone.md)
**`kernel/inductive/`** — [`inductive-support.md`](./kernel/inductive/inductive-support.md) (how it works now) · [`inductive-api-design.md`](./kernel/inductive/inductive-api-design.md) (the `covalence-inductive` API)

## `logics/` — object logics over the waist

| Doc | What it covers |
|---|---|
| [`logics/logic-frontends.md`](./logics/logic-frontends.md) | Umbrella + difficulty matrix for external systems as object logics (MLTT/HoTT, ACL2/Lisp, LF/Dedukti). |
| [`logics/theories-models-and-logics.md`](./logics/theories-models-and-logics.md) | signature → theory → model; within-logic model multiplicity; Metamath as shared substrate; PA→SOA→ZF. |
| [`logics/metatheory.md`](./logics/metatheory.md) | Object theories + derivations as first-class HOL objects; theory morphisms/transport. |
| [`logics/proof-format.md`](./logics/proof-format.md) | The Haskell dialect's theorem/proof split (equation statements + name-linked S-expr proofs). |
| [`logics/wasm-spec.md`](./logics/wasm-spec.md) | The SpecTec WASM-spec front end; dual to the Metamath front end. |
| [`logics/init-in-dialect.md`](./logics/init-in-dialect.md) | Writing `init/` in the Haskell dialect over the typed HOL backend. |
| [`logics/opentheory-import.md`](./logics/opentheory-import.md) | Verifying OpenTheory articles on the native HOL kernel (`NativeOt` backend, zero-TCB hyp-tracked axioms, defineTypeOp v6, `cov hol` + `bun run opentheory`). |

## `surface/` — the authoring layer (aspirational)

[`surface/surface-compiler.md`](./surface/surface-compiler.md) (canonical: theories/models/logics, the multi-stage compiler) ·
[`surface/surface-syntax.md`](./surface/surface-syntax.md) (rationale) ·
[`surface/frontend.md`](./surface/frontend.md) (UX vision: one surface, handler-dispatched reasoning)

## `lisp/` — the Lisp/ACL2 frontend

[`lisp/minimal-spec/`](./lisp/minimal-spec/) — the buildable spec: a `/lisp` REPL where an S-expr is evaluated as a reduction theorem, on a generic `Repl` ≤ `SExprRepl` ≤ `Lisp` trait stack, ending at the metacircular interpreter in the browser. [`lisp/initial-ideas/`](./lisp/initial-ideas/) — the design corpus behind it (dialects/UB, parsing relations, content-addressing, proptest-as-theorem, ACL2-inside).

## `web/` · `observers/` · `plans/`

- **web/** — [`web-kernel.md`](./web/web-kernel.md) (kernel in the browser; `.cov` articles; federation) · [`cov-project.md`](./web/cov-project.md) · [`wasm3-rust.md`](./web/wasm3-rust.md)
- **observers/** — [`observers.md`](./observers/observers.md) (untrusted facts into HOL without growing the TCB) · [`backend-decoupling.md`](./observers/backend-decoupling.md) (the `covalence-hol-api` trait surface)
- **plans/** — [`refactor-plan.md`](./plans/refactor-plan.md) · [`next-stage-breakdown.md`](./plans/next-stage-breakdown.md) · [`pure-hol-and-build-plan.md`](./plans/pure-hol-and-build-plan.md) · [`sketch-separation-thoughts.md`](./plans/sketch-separation-thoughts.md)

## `sketches/` · `handoff/` · `build/`

Scratch sketches ([`sketches/`](./sketches/)), open task handoffs ([`handoff/`](./handoff/)), and build known-issues ([`build/known-issues.md`](./build/known-issues.md)).
