# Where We Are (planning-stage)

Honest snapshot of the Covalence tree as of the `planning-stage` branch.
Captures what's shipping, what's in flight, what's stale, and what's planned
but not yet started. Read this before the design docs in
[`docs/design/`](./design/).

> **Note on status.** Everything in [`docs/design/proposals/`](./design/proposals/)
> is **proposed**, not committed. Those docs describe a possible
> direction (the layered-framework proposal), not a decided
> architecture. The list of in-flight code and superseded docs below
> *is* current; the "new direction" referenced is one proposal we're
> currently exploring, not a settled plan.

## TL;DR

We've successfully built the **substrate** (content-addressed store,
BLAKE3 wrappers, WASM engine, signature scheme, parsers, S-expressions).
We have **three parallel kernels** in various stages of development, none
of which match the target architecture. Application crates (REPL, server,
client, LSP, VSCode extension, web app) work against the *oldest* kernel
design. We are mid-replanning — these docs are the planning artifact.

The currently-favored direction is the **layered-framework proposal**
([`docs/design/proposals/layered-framework/`](./design/proposals/layered-framework/)):
a tiny
[Framework](./design/proposals/layered-framework/02-framework.md)
(Pure-style LF) at the bottom, a
[HOL layer](./design/proposals/layered-framework/) as an object theory
over it, and a
[Morphism layer](./design/proposals/layered-framework/) above that.
Hashing, signatures, executors, and the namespace machinery are all
**outside the trust boundary** as oracles or untrusted layers. This is
a *proposal*, not a decided architecture — alternatives are welcome.

The **[shared-backbone proposal](./design/proposals/shared-backbone/)**
is a sibling: it adopts the layered-framework kernel shape and adds
*the path* — substrate-first with the prover and VCS developed in
parallel over a content-addressed shared backbone, an
oracle-everything stratification (Stores leave the framework;
verifiable reads become oracle observations rather than TCB
primitives), and `attest`/`decide` reframed as the first concrete
oracle (not legacy). The kill list, the four phases, and the
supersession of [`refactor-plan.md`](./refactor-plan.md) Phase A–H +
Phase P are documented there. Read together with `layered-framework/`.

---

## 1. The substrate (shipping, considered correct shape)

These wrapper crates have stable APIs and are used throughout. The
[wrapper-crate discipline](../CLAUDE.md#wrapper-crates) is well-
established and should continue through the redesign.

| Crate                 | Wraps                                  | Status |
|-----------------------|----------------------------------------|--------|
| `covalence-store`     | content-addressed blob storage         | shipping |
| `covalence-hash`      | BLAKE3 (default+keyed+derive), SHA-256, Git hashes | shipping |
| `covalence-wasm`      | `wat`/`wasmparser`/`wasmprinter`/`wasm-encoder`, optional `wasmtime` | shipping |
| `covalence-sqlite`    | `rusqlite` + recommended pragmas       | shipping |
| `covalence-git`       | git-compatible objects + LFS           | shipping |
| `covalence-rand`      | `rand` + RNG abstractions              | shipping |
| `covalence-sig`       | Ed25519 (via `ed25519-dalek`)          | shipping |
| `covalence-parse`     | `winnow` + LEB128                      | shipping |
| `covalence-sexp`      | S-expression parser with dialects      | shipping |
| `covalence-types`     | `Decision`, `Bits`, `Nat`/`Int`        | shipping |
| `covalence-sat`       | SAT formulas, DIMACS, DRAT             | shipping |
| `covalence-smt`       | SMT-LIB2, theories, Alethe             | shipping |
| `covalence-object`    | `Dir`/`Table` serialization            | shipping |

---

## 2. Three kernels coexist

### 2.1 `covalence-kernel` (~4.9k LoC)

The current focus of the Phase A–H refactor described in
[`docs/refactor-plan.md`](./refactor-plan.md). Arena + UF + Prop + Thm +
Context + concept system. Recently shipped:

- **Phase F1** — `VarId`/`TyVarId` newtypes
- **Phase H** — `Arena::hash()` content addressing *(problematic — see
  [§5 Open issues](#5-open-issues-with-the-current-code))*
- **Phase G3** — `declare_type_operator` with tyvar order validation
- **Phase P** (partial) — parallel `EProp`/`EThm` egraph types alongside
  legacy `Prop`/`Thm`

| File          | LoC  |
|---------------|------|
| `arena.rs`    | 1933 |
| `prop.rs`     |  781 |
| `ty.rs`       |  388 |
| `hash.rs`     |  365 |
| `term.rs`     |  247 |
| `kernel.rs`   |  235 |
| `uf.rs`       |  176 |
| `primop.rs`   |  167 |
| `reduce.rs`   |  167 |
| `eprop.rs`    |  140 |
| `id.rs`       |  112 |
| `subst.rs`    |   60 |
| `egraph.rs`   |   44 |
| `lib.rs`      |   37 |

### 2.2 `covalence-hol` (~2.1k LoC)

A separate HOL-Light-shaped kernel with its own arena, term/type system,
and LCF-style inference rules. **Explicitly "left untouched" per the
original MVP plan.** Used as the proof target of `covalence-opentheory`.

| File         | LoC  |
|--------------|------|
| `light.rs`   |  958 |
| `arena.rs`   |  630 |
| `null.rs`    |  349 |
| `traits.rs`  |  231 |
| `types.rs`   |  129 |
| `lib.rs`     |   14 |

### 2.3 `covalence-opentheory` (~2k LoC)

OpenTheory article reader → drives `covalence-hol`. Substantive logic,
not just plumbing.

| File           | LoC  |
|----------------|------|
| `interp.rs`    |  802 |
| `resolve.rs`   |  549 |
| `theory.rs`    |  313 |
| `fetch.rs`     |  179 |
| `name.rs`      |  101 |
| `reader.rs`    |   70 |
| `machine.rs`   |   70 |
| `object.rs`    |   69 |

---

## 3. Application shells (work against the *oldest* design)

These all bind to `covalence-kernel`'s legacy `decide` / `attest()` model
(WASM-component-as-proposition; see superseded
[`MVP_DESIGN.md`](../MVP_DESIGN.md)):

| Crate / app                     | Purpose                                  |
|---------------------------------|------------------------------------------|
| `covalence-repl`                | S-expression REPL via `Session`          |
| `covalence-serve`               | REST + WebSocket server (axum 0.8)       |
| `covalence-client`              | sync/async HTTP client for remote kernel |
| `covalence-lsp`                 | LSP for `.smt`/`.smt2`/`.alethe`/`.cov`/`.wat` |
| `covalence` (CLI binary `cov`)  | clap + color-eyre                        |
| `covalence-python`              | PyO3 bindings                            |
| `extensions/covalence-vscode`   | VS Code extension                        |
| `apps/covalence-web`            | SvelteKit web app                        |

They work, but they reason against the *propositional WASM* model, not
the HOL kernel. Any layered redesign needs to swap their bindings — the
plan is to keep them stable against the legacy kernel until the new
layered stack is implementable, then migrate.

---

## 4. Vision, supersession, and the new design

### Canonical vision

- [`ARCHITECTURE.md`](../ARCHITECTURE.md) (v2) at the repo root — the
  big picture: planes, mirrors, oracles, mount-as-implication, format
  plane, base-shift functor.
- [`AGENTS.md`](../AGENTS.md) — operational summary of `ARCHITECTURE.md`.

### Superseded (kept for history)

- [`MVP_DESIGN.md`](../MVP_DESIGN.md) — WASM-component-as-proposition
  model. Predates the HOL vision.
- [`DESIGN.md`](../DESIGN.md) — first sketch of the HOL kernel. Refined
  into [`docs/prover-architecture.md`](./prover-architecture.md),
  itself refined into the design docs in [`docs/design/`](./design/).

### In flight

- [`docs/refactor-plan.md`](./refactor-plan.md) (Phases A–H) — kernel
  cleanup. Continuing to land; strategic value uncertain given the
  layered redesign.
- [`docs/prover-architecture.md`](./prover-architecture.md) — current
  kernel architecture; predates the framework concept and the
  store-as-primitive insight.
- [`docs/prover-mvp-plan.md`](./prover-mvp-plan.md) — earlier
  "wipe-and-restart" plan; the Phase 0 reset never happened.

### The currently-favored direction (proposed, not committed)

The [layered-framework proposal](./design/proposals/layered-framework/)
sketches three layers:

1. **CovalenceFramework** — Pure-style logical framework (LF). Would
   be the actual TCB /
   [meta-trust set](./design/proposals/layered-framework/00-glossary.md#meta-trust-set).
   ~700–800 LoC target. New crate. Described in
   [`docs/design/proposals/layered-framework/02-framework.md`](./design/proposals/layered-framework/02-framework.md).
2. **CovalenceHOL** — classical HOL as an object theory over the
   framework. Subset typedef with the disjunct trick, the existentials,
   ε-choice, primops. Doc pending.
3. **CovalenceMorphism** — embeddings, equiconsistency, base-shift,
   commutative-diagram API. Doc pending.

Around the framework, every hash function, every signature scheme,
every executor would be an **oracle** outside the trust boundary.

This is one **proposal**. It hasn't been formally adopted; alternative
directions and revisions are welcome. The proposal lives at
[`docs/design/proposals/layered-framework/`](./design/proposals/layered-framework/)
with its own index.

---

## 5. Open issues with the current code

These are concerns the **layered-framework proposal** flags about the
current code. Whether they're actually "violations" depends on whether
the proposal is adopted; listing them here as concerns to weigh, not
as settled judgments.

1. **`covalence-kernel`'s Phase H bakes BLAKE3 into the kernel**
   (`Arena::hash()`, `ContentHash` traits). The layered-framework
   proposal argues this should be a hasher oracle outside the trust
   boundary. See
   [`design/proposals/layered-framework/02-framework.md` §6](./design/proposals/layered-framework/02-framework.md).

2. **Phase P (Prop-as-egraph) layers equality saturation inside the
   kernel.** The proposal argues egraphs belong in *userspace* as an
   oracle that asserts equalities (which the framework then discharges
   via cong+trans+sym), not as a framework primitive.

3. **No store primitive.** The proposal argues crypto assumptions in
   the current kernel have no honest scoping — they implicitly assume
   "no collisions anywhere," which is mathematically false. See
   [`design/proposals/layered-framework/04-store.md`](./design/proposals/layered-framework/04-store.md).

4. **No layered factoring.** Framework concerns (the LF rules), HOL
   concerns (the existentials, subset typedef), and morphism concerns
   (substitutions, imports) all live in one crate, hard to audit
   independently.

5. **Three parallel kernels.** `covalence-kernel`, `covalence-hol`,
   and the parts of `covalence-opentheory` that drive `covalence-hol`.
   Need a single trusted core that they all factor through.

6. **Application shells bind to a superseded kernel API.** REPL,
   server, client, LSP all reason against `decide`/`attest()`. They
   work, but they're not exercising the HOL kernel that's being built.

---

## 6. Where to look first

| If you want…                              | Read                                                                       |
|-------------------------------------------|----------------------------------------------------------------------------|
| The big picture / vision                  | [`ARCHITECTURE.md`](../ARCHITECTURE.md)                                    |
| The **path** (substrate-first, two streams, kill list) | [`docs/design/proposals/shared-backbone/00-overview.md`](./design/proposals/shared-backbone/00-overview.md) |
| The vocabulary the proposed redesign uses | [`docs/design/proposals/layered-framework/00-glossary.md`](./design/proposals/layered-framework/00-glossary.md)                    |
| Conventions in the proposed redesign      | [`docs/design/proposals/layered-framework/01-conventions.md`](./design/proposals/layered-framework/01-conventions.md)              |
| The proposed Framework layer              | [`docs/design/proposals/layered-framework/02-framework.md`](./design/proposals/layered-framework/02-framework.md)                  |
| The proposal index                        | [`docs/design/proposals/layered-framework/README.md`](./design/proposals/layered-framework/README.md)                              |
| The design directory index                | [`docs/design/README.md`](./design/README.md)                                                                                       |
| Ongoing kernel cleanup (Phase A–H, P — *terminated*; see shared-backbone) | [`docs/refactor-plan.md`](./refactor-plan.md)                              |
| Current kernel internals                  | [`docs/prover-architecture.md`](./prover-architecture.md)                  |
| Current kernel build-out plan (*superseded by shared-backbone Phase 2*) | [`docs/prover-mvp-plan.md`](./prover-mvp-plan.md)                          |
| The WASM-prop model (*seed of the WASM oracle*, not legacy) | [`MVP_DESIGN.md`](../MVP_DESIGN.md)                                        |

---

## 7. What we're explicitly NOT doing yet

- **Wiping `covalence-kernel`** (the original "Phase 0 reset" from
  `prover-mvp-plan.md`). The new layered crates will land alongside the
  existing kernel; APIs migrate over once the layers are stable.
- **Touching `covalence-hol` or `covalence-opentheory`.** Their
  HOL-Light shape is the closest reference for the eventual
  CovalenceHOL layer; we'll mine them for the port but not modify yet.
- **Producing the first end-to-end demo.** Per the planning
  discussion, the target is the **Git-repo theorem** (clone, re-hash
  to BLAKE3, prove things about a commit under a scoped no-collision
  assumption), but it builds on the framework crate which doesn't
  exist yet.

---

## 8. Recent changes worth noting

From `git log` on `planning-stage` (most recent first):

- `6206676` — `Cargo.lock: covalence-kernel picks up covalence-hash dep`
- `f3bccac` — `docs: update refactor-plan with Phase P/H actual landing`
- `6056e99` — `kernel: VarId / TyVarId newtypes + per-arena allocators (Phase F1)`
- `08e6d94` — `kernel: content hashing for Arena, Prop, EProp (Phase H)`
- `c2218bd` — `kernel: declare_type_operator validates tyvar ordering (Phase G3)`

Phase H (content hashing) is the most recent substantive landing and
also the most architecturally questionable. The decision to move it
*out* of the trust boundary is captured in
[`docs/design/02-framework.md` §6](./design/02-framework.md).
