+++
id = "N002R"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-18T22:05:39+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Consolidation and context roadmap

**Status:** AI-drafted working plan (2026-07-18). This is a portfolio map and
proposed execution order, not an accepted architecture decision. It complements
the maintainer-authored [`../../plans/next-stage.md`](../../plans/next-stage.md),
the product-oriented [`../vision/roadmap.md`](../vision/roadmap.md), and the
design-doc queue in [`../../design/README.md`](../../design/README.md).

## Outcome

Make Covalence a repository in which a human or agent can, without reconstructing
the project from git history:

1. explain what is trusted, what is proved, and what is only an experiment;
2. find one bounded piece of useful work and its acceptance test;
3. run a representative demo and benchmark;
4. discover the dependency and project impact of a change;
5. add a frontend or representation behind a stable trait without growing the
   TCB; and
6. demonstrate **consilience** by lowering the same claim through independent API
   stacks and proving their equality or translation inside the TCB.

The plan deliberately does not schedule every desired API as an independent
project. The long list is a **capability map**. Work becomes scheduled only when
it participates in a product slice, unlocks several slices, or retires a measured
skeleton.

## Current assets to consolidate

This plan starts from working pieces, not a green field:

- 62 workspace crates and 178 internal dependency edges are already represented
  in `docs/deps/graph.json`; the dependency and TCB artifacts are generated and
  CI-checkable with `bun run deps` / `bun run deps:check`.
- The trusted closure is already audited by `scripts/tcb-audit.mjs`, and
  `covalence-tcb-db` round-trips the current TCB shape through SQLite without
  entering the TCB.
- The base facade and `CertificateAlgebra` seam exist; the relational-base
  proposal has a dedicated draft design doc.
- `set.mm` parse/verify and whole-WASM-module recognition have benchmark
  harnesses. Metamath is the mature import demonstration; ACL2 is a substantial
  in-progress logic/Lisp demonstration; SAT/SMT replay is early.
- The former 41 distributed `SKELETONS.md` files have been migrated to stable
  source-local markers and a generated JSON/SQLite index.
- The web app already exposes proofs, graphs, Metamath, Lisp, K, Forth, Haskell,
  and the TCB audit. These should become a coherent gallery rather than unrelated
  routes.

## One operating model

Use five kinds of repository object. Each has one job:

| Object | Source of truth | Purpose |
|---|---|---|
| Current facts | `docs/`, generated artifacts, code and tests | What exists and is true now |
| Decisions | `notes/design/` | Proposed/accepted choices with explicit status |
| Portfolio | this roadmap and `notes/vibes/vision/` | Desired capabilities and sequencing |
| Work items | generated work database | Concrete, local, queryable unfinished work |
| Projects | checked-in project manifests | Bounded campaigns over work items and metrics |

This prevents roadmaps from becoming issue trackers and prevents local TODOs
from becoming architectural documentation.

## Architecture: stable waist, replaceable stacks

The organizing rule should be visible both in crate boundaries and in the work
database:

```text
frontends / imported projects / user programs
                       |
        domain traits and proof-producing APIs
                       |
       logic encodings, translations, models
                       |
       stable certificate / theorem facade
                       |
     relational base + minimal trusted kernel
```

Each layer may add expressive power only by constructing terms, propositions,
proofs, translations, or explicitly named assumptions in the layer below.
Ordinary domain crates do not mint theorems and do not depend on trusted
implementation details.

A consilience result is a first-class artifact:

```text
source claim
  ├── stack A ──> proposition A ──┐
  └── stack B ──> proposition B ──┴──> TCB theorem: A = B
                                      (or an explicit interpretation A ↝ B)
```

For every public high-level API, record:

- its semantic target;
- which assumptions it adds;
- the proof object or theorem it returns;
- at least one independent representation/backend;
- its intended equality, isomorphism, PER, refinement, or translation theorem;
- whether it changes the TCB (normally: no).

The base redesign gets its own accepted design document and migration gates. It
must not be smuggled into general API cleanup. Preserve the facade, run old and
new certificate algebras differentially, then switch consumers, then delete the
old implementation.

## Capability trunks

Group the desired APIs by the reusable abstractions they exercise.

### 1. Foundations and datatype algebras

- fixed-width integers, bytes, characters, strings, encodings;
- naturals, integers, decimals, rationals, floats, and reals;
- lists, trees, maps, sets, multisets, sequences;
- vectors, tensors, and matrices;
- records, variants, polynomial functors, and least/greatest fixpoints.

The first deliverable is not a catalogue of concrete definitions. It is a small
trait vocabulary separating:

- syntax/representation;
- constructors and eliminators;
- laws supplied as kernel theorems;
- decidable or accelerated operations;
- serialization/content identity.

Start with two deliberately different representations for each foundational
example (for example unary vs double/succ naturals). The equivalence proof is
part of the API's definition of done and directly tests leaf elimination.

### 2. Parsing and data formats

- relations, partial functions, and total functions as parsing interfaces;
- regex, CFG, PEG, lexer, parser, and combined algebraic lexer/parser APIs;
- text/AST PERs;
- S-expressions first, then JSON plus one binary format and one tabular format;
- later MessagePack, CBOR, Ion, YAML, TOML, and broader tabular support.

This trunk should reuse the bytes/string traits and produce the same AST through
at least two parsing routes. The first consilience target is:

> parser combinator result = grammar derivation result, modulo an explicit
> same-AST PER.

The Krishnaswami algebraic lexer/parser paper is a design input for this trunk,
not an implementation requirement for its first slice.

### 3. Metatheory and logical thin waists

- Metamath databases, axiom use, sound extensions, translations, and theory
  relationships;
- Dedukti/LF, OpenTheory, direct Lean, and eventually Rocq;
- ACL2 as a Lisp-integrated logic;
- SAT/SMT proof formats as untrusted proof-producing drivers.

Metamath remains the first product path because it is working and measurable.
ACL2 becomes the second because it stresses computation, induction, and Lisp.
SAT/SMT becomes the third because it tests external automation and replay.
Dedukti/Lean/OpenTheory should enter as projects only when the generic
translation/assumption-reporting interface is fixed.

### 4. Programs and semantic thin waists

- untyped lambda representations, SKI, machines, and automata;
- STLC, System F, Church encodings, total/partial computability;
- Lisp/Scheme and equivalence to abstract computation;
- WASM construction, parsing, SpecTec and K semantics;
- K as a semantic interchange;
- later FORTH, JVM bytecode, and x86.

Choose examples that create commuting diagrams. The flagship is:

> WASM bytes → SpecTec semantics and WASM bytes → K semantics, with a proved
> relationship for a deliberately small shared fragment.

The computation-calculi work supports this flagship; it should not become a
detached encyclopedic formalization effort.

### 5. Domain libraries

- approximate numerics and verified linear algebra;
- graph families, properties, algorithms, and DOT;
- SQL over named relations;
- GraphQL.

These are consumers and stress tests of the earlier trunks. A domain library
graduates to first-class status only when it has stable traits, laws as
theorems, one usable backend, one alternate representation or algorithm, and a
small end-to-end example.

## Work database: replace the registries without losing locality

Keep skeleton comments beside the incomplete code, but generate the global view.
Do not make SQLite the authored source.

### Marker format

Use one parseable line followed by ordinary prose:

```rust
// COV-TODO(id="hol.script.spans", project="script-pipeline",
//          severity="blocking", kind="missing", issue="")
// Thread source spans through parse, elaboration, and proof errors.
```

Required fields: stable `id`, `kind`, and short summary. Inherited/defaulted
fields may come from the nearest crate/project manifest. Useful fields include:
`project`, `severity`, `owner`, `blocked_by`, `area`, `tcb`, `metric`, `issue`,
and `expires`.

Generated columns include commit, file, line, crate, workspace group, content
hash, first/last seen, and marker state. Vendored/generated paths are excluded
by policy so upstream TODOs do not pollute Covalence work.

### Schema and outputs

Use a normalized SQLite database with at least:

- `items`;
- `locations`;
- `dependencies`;
- `projects`;
- `project_items`;
- `metrics`;
- `metric_samples`;
- `artifacts`;
- `runs`.

Also emit deterministic JSON for the web UI and agent tools. Check a compact
golden summary into `docs/work/`; build the full database in `target/` or a
cache. CI checks marker syntax, unique IDs, resolvable dependencies, project
references, and regenerated summaries.

### Migration

1. Build an extractor that inventories both structured markers and legacy
   TODO/FIXME/skeleton prose.
2. Give stable IDs to the root top-ten blockers and one representative crate.
3. Check generated counts and representative entries against the former
   registries during migration.
4. Migrate crate by crate, preserving the detailed local prose until every
   entry has an ID and acceptance criterion.
5. Flip authority to markers + project manifests; delete hand-maintained index
   duplication only after parity checks pass.

### CLI

Make the capability part of `cov dev`, or a small app crate invoked through it:

```text
cov dev work list --project metamath-product --ready
cov dev work show hol.script.spans
cov dev work next --project script-pipeline
cov dev work graph --project wasm-consilience --format dot
cov dev work check
cov dev deps why covalence-init covalence-core
cov dev deps impact covalence-core --projects
cov dev deps graph --group kernel --tcb --format mermaid
```

Machine-readable JSON is mandatory. Human tables and DOT/Mermaid are views over
the same query model.

## Project manifests and autoresearch

A project is versioned data, for example `projects/metamath-product.toml`:

```toml
id = "metamath-product"
goal = "Import set.mm and expose an honest axiom/translation report"
status = "active"
owners = ["maintainer"]
work_query = 'area = "metamath" and state != "done"'
entrypoints = ["bun run bench:setmm"]
acceptance = ["set.mm verifies", "result records axiom use", "web demo is reproducible"]
```

Projects contain:

- a goal and non-goals;
- dependency/project links;
- work-item query plus any explicitly pinned items;
- test and demo commands;
- benchmark metrics and budgets;
- acceptance criteria;
- allowed files or crate groups for autonomous campaigns;
- stop conditions and review policy.

An autoresearch loop operates only inside such a manifest:

1. select a ready item or a stated optimization hypothesis;
2. record the baseline on pinned inputs and environment metadata;
3. make one bounded change;
4. run correctness gates before performance measurement;
5. retain the change only if the declared objective improves without violating
   secondary budgets;
6. append the run, diff, result, and artifact hashes to the database.

Avoid optimizing a single lucky timing. Record distributions, input size, peak
memory, output facts/proofs, TCB metrics, and scaling exponents where possible.
Use fixed corpora and separate cold-build/download time from algorithm time.

Initial benchmark projects:

- `setmm-verify`: parse time, verify time, theorems/s, bytes/s, peak RSS;
- `setmm-hol-import`: imported facts/s, theorem size/count, peak RSS;
- `wasm-module-recognition`: environment build time, proof time, refusal time,
  clauses, bytes, peak RSS;
- `script-load`: representative `.cov` project load time and allocations;
- `tcb-audit`: mint sites, admitted rules, public surface, trusted dependencies.

## Demo product line

Every demo gets the same shell:

- one sentence explaining the claim;
- pinned input and a one-command reproduction;
- visible assumptions and trusted tier;
- proof/derivation artifact and content identity;
- performance data from the same harness CI can run;
- links to its project, work items, crates, and dependency subgraph;
- a browser presentation that never implies more coverage than exists.

The first three polished vertical slices should be:

1. **Metamath product:** import all of `set.mm`, show verification statistics and
   axioms used, then expose the GT relationship as it becomes proved.
2. **ACL2 product:** a small reproducible book/import demonstrating definition,
   induction, and a kernel-backed theorem, integrated with the Lisp surface.
3. **Automation product:** discharge a narrowly stated goal with SAT or SMT,
   replay the certificate, and show the boundary between solver and trusted
   checker.

WASM/SpecTec/K is the next flagship slice once whole-module grammar coverage and
the shared semantic fragment are ready.

## Agent context

The agent on-ramp should be generated where possible and layered by cost:

1. root `README`: what Covalence is, one demo, reading path;
2. root agent instructions: commands, invariants, documentation policy;
3. current project manifest: goal, boundaries, tests, metrics;
4. crate card: purpose, public API, dependencies, dependents, trust tier,
   maintainers, work query;
5. focused design docs and local markers;
6. source.

Add `cov dev context <crate|project|item> --format md|json`, which assembles a
bounded context pack from generated facts and links rather than copying prose.
Include freshness hashes so an agent can tell when a pack is stale. Never put
aspirational claims into generated crate cards.

Agent tasks should be selected from ready work items with explicit acceptance
commands. Each handoff reports: files changed, tests/benchmarks run, metric
movement, new assumptions/TCB delta, and remaining item IDs.

## Phased execution

### Phase 0 — freeze the map (1–2 weeks)

- Accept or revise the relational-base design questions; name its invariants and
  migration gates.
- Create the capability map and 4–6 project manifests, without moving crates.
- Specify the work marker/schema and query contract.
- Define the common demo contract and select pinned fixtures.
- Refresh the architecture skill from Cargo metadata and the current project map.

Exit: each active thread has exactly one project, design doc, or explicit parked
status; no thread depends on an unnamed “future API.”

### Phase 1 — build the control plane (2–4 weeks)

- Implement marker extraction, SQLite/JSON generation, `work list/show/check`,
  and CI parity against current skeleton registries.
- Extend dependency queries with `why`, reverse impact, group/TCB filters, and
  project overlays.
- Normalize benchmark JSON and store baseline samples.
- Add generated crate cards and `context` packs.

Exit: a new agent can find a ready task, understand its impact, and run its
acceptance test without loading root or per-crate skeleton files wholesale.

### Phase 2 — polish three vertical slices (4–8 weeks)

- Ship the Metamath, ACL2, and SAT/SMT demo shells.
- Use their pain points to stabilize only the shared traits they actually need.
- Require assumption/TCB reporting and reproducible benchmark runs in all three.
- Surface them as a coherent web gallery and CLI workflow.

Exit: three honest, shareable demos exercise import, computation/induction, and
external automation through the same trust presentation.

### Phase 3 — foundational APIs through consilience (6–12 weeks)

- Land minimal datatype/encoding traits with two nat and two bytes/string paths.
- Land the parsing relation/PER interfaces and S-expression end-to-end example.
- Move consumers behind `covalence-hol-api`-style traits rather than expanding a
  monolithic initialization catalogue.
- Begin content-addressed project packages and a minimal WIT component boundary.

Exit: an out-of-tree or WASM-compiled project can construct and relate useful
theorems without importing internal implementation crates.

### Phase 4 — relational base migration and semantic flagship

- Implement the alternate relational certificate algebra behind the stable
  facade, with differential tests and TCB audit gates.
- Persist propositions/relation facts according to the accepted reload and
  signature discipline.
- Build the first SpecTec/K shared WASM fragment and its relationship theorem.

Exit: the base implementation can change without high-level API churn, and the
first semantic consilience diagram is visible end to end.

## Prioritization rule

Score candidate projects on:

- product evidence;
- shared abstraction leverage;
- trust-story leverage;
- benchmarkability;
- ability to produce an independent consilience path;
- dependency readiness;
- scope/risk.

Prefer work that advances at least two of product, platform, and trust. Park a
broad API when it has no current consumer, equivalence target, or acceptance
test. This is how the project can keep its breadth without turning every north
star into simultaneous work in flight.

## First open-work census

The initial migration produced 298 stable items: 54 severe, 116 major, and 128
minor. The distribution sharpens the sequencing above:

- `covalence-init` owns 139 items, including 34 severe. This is the main
  consolidation pressure point: catalogue, script, parsing, ACL2, metalogic,
  SpecTec, and WASM concerns currently meet there.
- The base/HOL tower has 51 items across `covalence-pure`,
  `covalence-core`, and `covalence-hol-eval`. Its gaps are fewer but more
  architectural: the evaluation seam, relational base, leaf elimination,
  hash-consing, and consumer migration.
- K, Lisp, Haskell, Metamath, Alethe, SAT, and SMT already have useful bounded
  backlogs. They should be treated as vertical projects over shared APIs, not
  folded further into `covalence-init`.
- Several former registry entries were completed work, historical explanation,
  intentional constraints, or duplicate roll-ups. They were intentionally not
  promoted into permanent work items.

The immediate organizational follow-up is therefore to split ownership and
project overlays around `covalence-init` before adding broad new catalogue APIs.
Marker relocation from the temporary co-located `open_work.rs` files to the
responsible symbols can happen incrementally whenever an area is touched; stable
IDs keep project queries intact.

## Immediate decisions

The maintainer decisions with the highest leverage are:

1. approve the five-object operating model and whether `projects/` is the
   checked-in manifest location;
2. settle the work-item marker syntax and whether the CLI lives under
   `cov dev`;
3. choose the exact three demo acceptance stories;
4. fill the relational-base proposal's serialization, signing, attestation, and
   sequencing decisions;
5. choose the first two representations for the foundational datatype slice;
6. declare which current experiments are active projects and park the rest.
