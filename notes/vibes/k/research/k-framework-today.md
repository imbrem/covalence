+++
id = "N000Q"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-14T19:57:49+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# The K framework today (2026)

> **STATUS: RESEARCH SURVEY (AI-drafted, web-sourced).** Researched 2026-07-13
> via live fetches of primary sources; claims individually marked with
> certainty. Cross-checked by an independent verification pass; corrections
> applied.

Scope: what K is, its maintenance/version/license state, the anatomy of a `.k`
definition, the `kompile` pipeline, KAST vs KORE, and the tutorial/pyk
landscape — the ground truth a Covalence K frontend has to build on. The KORE
IR itself gets its own deep-dive in [`kore-ir.md`](./kore-ir.md).

## What K is

K is Runtime Verification's semantic framework: you write **one** formal
semantics of a language or system in the K language, and the tooling derives
an interpreter, a symbolic executor, and a program verifier from it. The
[repo](https://github.com/runtimeverification/k) describes itself as "a tool
for designing and modeling programming languages and software/hardware
systems" whose tooling compiles K specifications "to build interpreters, model
checkers, verifiers, associated documentation, and more" **[high]**.

## Maintenance, versions, license

*(Staleness note: exact version numbers below rot within weeks; the structural
facts are stable.)*

- **Actively maintained** by Runtime Verification at
  [runtimeverification/k](https://github.com/runtimeverification/k): default
  branch `master`, pushed 2026-06-23, not archived **[high]**.
- **License: BSD-3-Clause** — and this holds across the whole constellation
  (k, pyk, pl-tutorial, kup, llvm-backend, haskell-backend), so importing
  samples, grammars, and test corpora is unproblematic **[high]**.
- **Latest release v7.1.337** (published 2026-06-18), out of **1,895 total
  releases** — effectively a release per merged PR, historically every 1–3
  days **[high]**. The verification pass noted the cadence has visibly paused
  recently (~25 days without a release despite master pushes), so "a new
  release any day" is historical, not guaranteed; the practical advice stands:
  **pin an exact K version** rather than tracking "latest" **[high]**.
- **Monorepo layout** **[high]**: `k-frontend/` (the Java/Maven frontend),
  `k-distribution/` (CLI wrappers, builtins like `domains.md`, the current
  tutorial), `pyk/` (Python tooling), `docs/`, plus `llvm-backend/` and
  `haskell-backend/` wrapper dirs whose native code comes in as git submodules
  from the separate
  [llvm-backend](https://github.com/runtimeverification/llvm-backend) ("KORE
  to llvm translation" — fast concrete execution) and
  [haskell-backend](https://github.com/runtimeverification/haskell-backend)
  ("the symbolic execution engine powering the K Framework") repos, both
  active and BSD-3-Clause **[high]**. (Layout stable since the 2024 monorepo
  consolidation.)
- **Install**: the preferred route is the Nix-based `kup` tool
  (`bash <(curl https://kframework.org/install)`), with Ubuntu/Homebrew/Docker
  alternatives; [kup](https://github.com/runtimeverification/kup) is itself
  active and BSD-3-Clause **[high]** *(install mechanics shift per LTS cycle —
  re-check the README before documenting steps)*.

One research caveat: **kframework.org blocks automated fetching (HTTP 403)**
**[high]**, so all documentation claims here come from the GitHub source files
that generate the site, not the rendered pages.

## Anatomy of a K definition (`.k`)

A K definition is `requires` (file inclusions) plus modules (with imports)
containing sentences of a few kinds
([user manual](https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md))
**[high]**:

- **Syntax declarations**: sort declarations ("define new categories of
  primitive datatypes") and BNF grammar declarations ("define the operators"),
  with attributes like `[function]`, `[token]`, `[strict]`/`[seqstrict]`.
- **A `configuration` declaration**: "labelled, hierarchical records using a
  nested XML-like syntax" — nested cells like `<k>`, `<env>`, `<store>`, with
  cell multiplicity.
- **Rules**: `rule LHS => RHS requires REQ ensures ENS [attrs]` — the
  `requires` clause is "an additional predicate … evaluated before applying
  the rule"; `ensures` is a post-condition (used in symbolic claims) — plus
  `context` declarations for evaluation contexts **[high]**.

This core language shape has been stable across K 5–7 **[high]**.

**Strictness is sugar for heating/cooling.** `strict`/`seqstrict` attributes
auto-generate rules that heat non-value subterms onto the `~>` continuation
for evaluation and cool results back into place; the generated rules carry
`heat`/`cool` attributes (e.g. `rule [addExp1-heat]: <k> HOLE:AExp + AE2:AExp
=> HOLE ~> [] + AE2 ... </k> [heat]`) **[high]**. Crucially for us: `kompile`
desugars all of this *before* emitting KORE, so a KORE-consuming lowering sees
heating/cooling as explicit rewrite axioms, never as sugar **[high]**.

## The kompile pipeline

`kompile` is the compiler driver: it desugars the frontend definition (macros,
strictness, contexts, configuration abstraction) and emits **KORE** — per the
user manual, "a lower-level Kore specification that encodes the same
information, but that is easier to work with programmatically" **[high]**.
Output is a `<name>-kompiled/` directory containing `definition.kore` plus
backend artifacts (the directory name and `definition.kore` are documented in
the haskell-backend README and pyk source, not the user manual itself — the
verification pass pinned this down) **[high]**. The LLVM backend consumes KORE
for fast concrete execution; the Haskell backend for SMT-backed symbolic
execution and proving **[high]**.

The surrounding CLI
([ktools.md](https://raw.githubusercontent.com/runtimeverification/k/master/docs/ktools.md))
**[high]**: `kast`/`kparse` (parsing + format conversion, `--input/--output`),
`krun` (`--debugger`), `kprove` (`--output json`), `kore-repl`, and `kserver`
(a warm JVM server, Nailgun).

**Hello world, 2026 edition** (verbatim from
[tutorial lesson 1.2](https://raw.githubusercontent.com/runtimeverification/k/master/k-distribution/k-tutorial/1_basic/02_basics/README.md))
**[high]**: a module `LESSON-02-A` with `syntax Color ::= Yellow() | Blue()`,
`syntax Color ::= colorOf(Fruit) [function]`, `rule colorOf(Banana()) =>
Yellow()`; then `kompile lesson-02-a.k` (default LLVM backend), `krun
banana.color` or `krun -cPGM='colorOf(Banana())'`; output is the final `<k>`
cell, e.g. `<k> Yellow ( ) ~> .K </k>`.

**Proving workflow** (from
[lesson 1.22](https://raw.githubusercontent.com/runtimeverification/k/master/k-distribution/k-tutorial/1_basic/22_proofs/README.md))
**[high]**: `kompile def.k --backend haskell`, then a `*-spec.k` module of
reachability claims — `claim <k> PGM => RESULT ... </k> <store> S => S'
</store> requires C ensures E` — importing the semantics plus
K-EQUAL/MAP-SYMBOLIC/domains.md; `kprove def-spec.k`; output `#Top`
(matching-logic true) means all claims proved. `[simplification]`-attributed
rules act as prover hints. These claims are the proof objects Covalence would
eventually want to certify internally (today they are discharged by the
Haskell backend + SMT).

## KAST vs KORE

The two-layer picture **[high]**:

- **KAST** is the abstract syntax of *parsed frontend K* — terms, rules,
  claims, still containing sugar like strictness and contexts. It is what
  `kparse`/`kast` produce and what pyk manipulates.
- **KORE** is the flattened **matching-logic IR** produced by `kompile`:
  sorts, symbols/hooked-symbols, axioms and claims over patterns with the full
  matching-logic connective set (`\and \or \implies \exists \forall \mu \nu
  \equals \ceil \floor …`) plus `\rewrites` axioms. Its syntax is specified in
  [haskell-backend docs/kore-syntax.md](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/kore-syntax.md)
  ("the syntax of Kore, as admitted by the Haskell Backend") **[high]**.

KORE is essentially a presentation of a matching-logic theory —
relations-as-axioms, machine-oriented, stable across backends — which is why
it is the natural ingestion point for a Covalence K frontend (each rewrite
axiom becomes a clause of a `Derivable_`-style step relation, the same pattern
as the Metamath/SpecTec frontends). See [`kore-ir.md`](./kore-ir.md).

## Tutorials and pyk

- The **current maintained tutorial** is
  [k-distribution/k-tutorial](https://raw.githubusercontent.com/runtimeverification/k/master/k-distribution/k-tutorial/README.md):
  Section 1 "Basic" lessons 01–22 (installing → parsing → rules → evaluation
  order → configurations → backends → symbolic execution → proofs), plus
  `2_intermediate` and `3_advanced`; it is in-repo and CI-tested **[high]**.
- The **classic "K PL Tutorial"** (LAMBDA, IMP, LAMBDA++, IMP++, types) moved
  out of the k repo into the separate
  [runtimeverification/pl-tutorial](https://github.com/runtimeverification/pl-tutorial)
  repo (BSD-3-Clause, still receiving pushes — though these track K release
  dates and look like automated version bumps; the pedagogy is old but
  stable), and the new tutorial itself warns it "might be out of date"
  **[high]**. IMP/LAMBDA sources for a Covalence test corpus should come from
  pl-tutorial or the small languages built up inside the k-tutorial lessons.
- **pyk** — Python tools for K: KAST/KORE data types and parsers,
  kompile/krun/kprove drivers, proof exploration — lives in the monorepo under
  `pyk/` and is published on PyPI as
  [`kframework`](https://pypi.org/pypi/kframework/json), version-locked to K
  releases (currently 7.1.337). The old standalone runtimeverification/pyk
  repo is archived (last push April 2024) **[high]**. pyk is the reference
  implementation for programmatic KAST/KORE consumption — the thing to crib
  from, not depend on.

## What this means for Covalence

- **License-safe across the board** (BSD-3-Clause everywhere we looked):
  vendoring sample `.k`/`.kore` files, grammars, and tutorial languages as
  test fixtures is fine **[high]**.
- **Consume KORE, not `.k`**: kompile has already desugared strictness,
  contexts, macros, and configuration abstraction by the time
  `definition.kore` exists, so a Covalence frontend that reads KORE gets
  explicit rewrite axioms and skips reimplementing the Java frontend.
- **Pin a K version** and snapshot-test kompiled outputs — the
  release-per-merge cadence means "the latest K" is a moving target even when
  the IR is stable.
- **pyk is the map**: its KORE parser/AST and kast↔kore converters document
  the de-facto semantics of everything kompile emits.
- **The proving workflow is the long-game target**: K reachability claims
  (`claim … requires … ensures …`) discharged by the Haskell backend + SMT are
  exactly the artifacts a construct-don't-trust Covalence integration would
  want to re-certify internally, the way the Metamath frontend replays proofs.

## Sources consulted

- https://github.com/runtimeverification/k
- https://api.github.com/repos/runtimeverification/k
- https://github.com/runtimeverification/k/releases
- https://raw.githubusercontent.com/runtimeverification/k/master/.gitmodules
- https://api.github.com/repos/runtimeverification/haskell-backend
- https://api.github.com/repos/runtimeverification/llvm-backend
- https://api.github.com/repos/runtimeverification/pyk
- https://pypi.org/pypi/kframework/json
- https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md
- https://raw.githubusercontent.com/runtimeverification/k/master/docs/ktools.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/kore-syntax.md
- https://raw.githubusercontent.com/runtimeverification/k/master/k-distribution/k-tutorial/README.md
- https://raw.githubusercontent.com/runtimeverification/k/master/k-distribution/k-tutorial/1_basic/02_basics/README.md
- https://raw.githubusercontent.com/runtimeverification/k/master/k-distribution/k-tutorial/1_basic/22_proofs/README.md
- https://api.github.com/repos/runtimeverification/pl-tutorial
- https://api.github.com/repos/runtimeverification/kup
- https://kframework.org/ (403 to automated fetch; not directly consulted)
