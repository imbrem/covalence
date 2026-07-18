# Project map — where everything is, and what's in flight

**Status:** navigation aid (AI-drafted), the consolidated map. Point-in-time
snapshot (2026-07-11) of *where things live* and *what threads are active*. For
each crate's precise contract see the **crate-map** skill
(`.claude/skills/crate-map/SKILL.md`); for open work see the per-crate
open-work index linked below and the root [open-work index](../../../docs/todos/todos.json).
This map **links, does not duplicate** those.

**Read-first design docs:** [`VISION.md`](./VISION.md),
[`kernel-design.md`](../kernel/kernel-design.md), [`roadmap.md`](./roadmap.md),
[`what-is-the-tcb.md`](../kernel/tcb/what-is-the-tcb.md), the vibes index
[`README.md`](../README.md), and the design-doc queue
[`../design/README.md`](../../design/README.md).

## Part 1 — the crate groups at a glance

`crates/` is hierarchical (`app ffi kernel lang lib proof server store vcs`);
package names keep their `covalence-*` prefix. Layering flows bottom-up:
**wrappers → storage → kernel/TCB → proof frontends → apps.**

| group | path | what lives here (one line) |
|---|---|---|
| **lib** | `crates/lib/` | **Wrapper crates** — one per external dep (hash, sqlite, rand, sexp, types, wasm, spectec, graph, json, arrow, parquet, sat, smt, crypto, parse, proptest, git, llm, fuse, data/{acset,multiformat}, proto). All external-dep use funnels through here. |
| **store** | `crates/store/` | Content-addressed **blob store** (`covalence-store`, portable to wasm32) + **kv** surface. |
| **vcs** | `crates/vcs/` | **Object** serialization (`covalence-object`): dirs/tables, git tree-format. |
| **kernel** | `crates/kernel/` | The **TCB and the tiers on it**: `base` (pure equality kernel + trusted + eval), `hol` (core = HOL TCB, eval = computation tier, traits, init = semi-trusted API), `shell`, `web` (kernel→wasm32 for the browser). |
| **lang** | `crates/lang/` | **Surface / object languages**: `haskell` (dialect→IR→HOL backend), `forsp` (Lisp/repl), `grammar`, `inductive` (logic-agnostic inductive-types API). |
| **proof** | `crates/proof/` | **Proof-format frontends** (untrusted drivers): `metamath`, `alethe`, `egglog`, `opentheory`, `lean`. |
| **server** | `crates/server/` | The **service layer**: `core` (axum HTTP/WS serve), `client` (remote kernel), `lsp`. |
| **ffi** | `crates/ffi/` | Foreign bindings: `python` (PyO3). |
| **app** | `crates/app/` | **End-user apps/tools**: `cov` (the CLI), `repl`, `tcb-db` (TCB-as-SQLite). |

The trusted subset of `kernel/` is the TCB — see
[`what-is-the-tcb.md`](../kernel/tcb/what-is-the-tcb.md). The machine-tracked dependency
graph + TCB closure is `docs/deps/` (`bun run deps`).

## Part 2 — the active threads

Each thread: what it is, status, and the key pointers (design notes +
open-work markers). "Status" is a coarse read; the open-work markers files are the live TODO.

### A. Backend / kernel (the TCB tower)

The closed-world equality base → HOL core → eval computation tier → semi-trusted
`init` API. **Status: load-bearing, actively evolving.** The base facade + the
`CertificateAlgebra` abstraction landed (additive, zero TCB delta); core/eval
migration onto the trait is deferred behind an in-flight freeze.

- Design: [`kernel-design.md`](../kernel/kernel-design.md),
  [`closed-world-kernel.md`](../kernel/closed-world-kernel.md),
  [`base-abstraction.md`](../kernel/base-abstraction.md),
  [`base-api-surface.md`](../kernel/base-api-surface.md).
- Open work: [open-work index](../../../docs/todos/todos.json)
  (Stage 0 only; ADTs/Set/HOL/macro unbuilt),
  [open-work index](../../../docs/todos/todos.json)
  (hash-consing default, `defs/` D3 residue),
  [open-work index](../../../docs/todos/todos.json).
- Root open-work index items: #1 (base Stage 0), #2 (hash-consing not adopted).

### B. Haskell frontend

Small Haskell-dialect surface: `Haskell ⇒ SExpr IR ⇒ backend`, with a
`hol`-feature backend realizing the IR as carved `sexpr` kernel `Term`s. The
"write `init/` in the dialect" on-ramp. **Status: parser + IR + demo backend
land real kernel data; no typed HOL realization, no lowering to real `init/`
definitions yet.**

- Crate: `crates/lang/haskell` (`covalence-haskell`).
- Open work: [open-work index](../../../docs/todos/todos.json)
  (typed HOL-term realization; lowering to `init/` defs; parser subset — no
  layout/patterns/types/do).
- Vision context: [`frontend.md`](../surface/frontend.md),
  [`surface-compiler.md`](../surface/surface-compiler.md).

### C. K-framework (north star)

Full K + all its sublanguages (WASM/x86/C/K itself); relate KWasm to the
official SpecTec WASM semantics. **Status: north-star vision; composes with the
existing SpecTec/WASM front end. Not yet a design-doc proposal.**

- Vision: [`k-framework-vision.md`](./k-framework-vision.md).
- Composes with: [`wasm-spec.md`](../logics/wasm-spec.md), `covalence-spectec`
  (`crates/lib/wasm/spectec`), `covalence-wasm` (`crates/lib/wasm/core`),
  the metalogic engine (`crates/kernel/hol/init/src/metalogic`).
- Shared blocker: the **CFG stratum** (root open-work index #8;
  [open-work index](../../../docs/todos/todos.json)).

### D. Relational base rewrite

Move all computation into untrusted relations; make axioms serializable
propositions; **persist proven facts as signed SQLite**. **Status: design-doc
STUB (maintainer to flesh out); scaffolding landed (the abstraction seam +
`tcb-db` PoC).**

- Design doc: [`../design/relational-base-rewrite.md`](../../design/relational-base-rewrite.md).
- Scaffolding: `crates/kernel/base/src/algebra.rs` (`CertificateAlgebra` +
  RelKernel recipe), `crates/kernel/base/trusted/src/rel.rs` (execute/compose/
  transpose), `crates/app/tcb-db` (`covalence-tcb-db`).
- Design corpus: [`base-abstraction.md`](../kernel/base-abstraction.md) §4–5,
  [`base-relcalc-holomega-design.md`](../kernel/base-relcalc-holomega-design.md),
  [`tcb-holomega-roadmap.md`](../kernel/tcb/tcb-holomega-roadmap.md) (Fronts D/E).

### E. Leaf-elimination / EG5

Delete the literal-leaf term kinds (`TermKind::{Nat,Int,SmallInt,Blob,Bool}`)
from `covalence-core` so literals enter HOL only via `toHOL` — shrinking the
core TCB toward the `base+HOL (target)` audit config. **Status: mechanism waves
+ EG3a/EG3b/A3 landed; the irreversible EG5 deletion is UNBLOCKED-WITH-DECISIONS
but NOT yet executed.**

- Design: [`literal-endgame-design.md`](../kernel/literals/literal-endgame-design.md),
  [`eg5-preflight.md`](../kernel/literals/eg5-preflight.md),
  [`tcb-holomega-roadmap.md`](../kernel/tcb/tcb-holomega-roadmap.md) (Front A).
- Open work: [open-work index](../../../docs/todos/todos.json)
  (`defs/` D3 residue dies with the literal leaves); root open-work index #6.

### F. HOL-ω (middle language retarget)

Retarget the middle language to **HOL-ω** (kinds = base sorts; micro-Haskell →
HOL-ω Monad mapping) — the textbook-HOL middle above a relations base.
**Status: design/reflection primitives present in base but unconsumed
(B-K1..3); roadmap-bearing.**

- Design: [`base-relcalc-holomega-design.md`](../kernel/base-relcalc-holomega-design.md),
  [`tcb-holomega-roadmap.md`](../kernel/tcb/tcb-holomega-roadmap.md).
- Surface: the HOL-ω reflection ops in `crates/kernel/base` (unconsumed today —
  [`base-api-surface.md`](../kernel/base-api-surface.md) §C).

### G. Web demo

Kernel-in-browser + the SvelteKit web app: article view, graph, Metamath, and a
**live TCB-audit page**. **Status: web app renders real artifacts; kernel→wasm32
(`covalence-web-kernel`) is the browser-kernel path.**

- App: `apps/covalence-web` (routes: `article`, `graph`, `metamath`, `tcb`,
  `view`); the TCB page embeds `docs/deps/tcb-audit.json`.
- Crate: `crates/kernel/web` (`covalence-web-kernel`).
- Vision: [`web-kernel.md`](../web/web-kernel.md), [`wasm3-rust.md`](../web/wasm3-rust.md).

## Part 3 — the inventory, consolidated

The per-crate open-work index files are the authoritative open-work registry
(the root [open-work index](../../../docs/todos/todos.json) indexes them and ranks the
top 10 holes). This map's job is *navigation*: pick the thread above, follow its
pointers. Don't restate skeleton contents here — they rot; the co-located files
don't.
