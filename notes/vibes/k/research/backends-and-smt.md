# K backends, the KORE RPC protocol, and where SMT actually lives

> **STATUS: RESEARCH SURVEY (AI-drafted, web-sourced).** Researched 2026-07-13
> via live fetches of primary sources; claims individually marked with
> certainty. Cross-checked by an independent verification pass; corrections
> applied.

Scope: the two production K backends (LLVM and Haskell), the KORE RPC protocol
that all symbolic tooling speaks, exactly where and how SMT/Z3 is used, the K
attributes that wire it up, the kprove/APRProof/KCFG proving stack — and the
load-bearing negative result that **no independently checkable proof object
exists anywhere in the symbolic pipeline**.

## The two backends

Both backends consume **KORE**, the intermediate representation `kompile` emits
from a K definition **[high]**.

- **LLVM backend** ([repo](https://github.com/runtimeverification/llvm-backend))
  — "a fast concrete rewriting engine for KORE": compiles KORE pattern-matching
  to LLVM IR for fast concrete execution. BSD-3-Clause, active (v0.1.141,
  June 2026 — version numbers churn weekly). Mostly C++ (~67%) with a Scala
  KORE-to-IR compiler frontend; PRs target `develop`. It performs **no SMT
  reasoning** at all (the verification pass confirmed: the only `z3` hit in the
  repo is a test dependency in INSTALL.md) **[high]**.
- **Haskell backend** ([repo](https://github.com/runtimeverification/haskell-backend))
  — "the symbolic execution engine powering the K Framework" (that's the GitHub
  repo description; the README H1 is "Symbolic Execution Engine for the K
  Framework"). BSD-3-Clause, active (v0.1.155, June 18 2026), 93.9% Haskell
  **[high]**.

The Haskell backend is really **three engines in one repo** **[high]**:

- legacy **`kore`** — the full matching-logic simplifier: `\and`-based
  unification pushed through constructors/sort-injections/collections,
  substitution normalization (cycle detection → `\bottom` for constructor
  cycles), function evaluation during simplification (which may branch),
  remainder conditions over applied rules
  ([introduction.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/introduction.md))
  **[high]**;
- **`booster`** — a faster, restricted rewriter: matching-based equations, map
  unification only for concrete keys, no general AC unification, a simplified
  predicate language splitting data terms from boolean constraints; it can link
  the LLVM backend as a dynamic library for fast concrete simplification
  ([booster.md](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/docs/booster.md))
  **[high]**;
- **`kore-rpc-booster`** — the proxy and main server: runs booster first and
  replays the step on legacy kore when booster returns Branching/Stuck/Aborted
  or SMT-Unknown **[high]**. RV's stated long-term plan is to delete the proxy
  once booster is complete, so "what booster can't do" claims age fastest.
  `kore-exec` and `kore-repl` are the deprecated non-RPC entry points **[high]**.

## The KORE RPC protocol

All symbolic tooling — pyk's KCFG explorer, `kprove`, Kontrol/KEVM — talks to
these engines **exclusively** through the JSON-RPC "KORE RPC" protocol
([spec](https://github.com/runtimeverification/haskell-backend/blob/master/docs/2022-07-18-JSON-RPC-Server-API.md)):
JSON-RPC 2.0 over raw sockets, newline-delimited, states exchanged as KORE JSON
`{term, predicate, substitution}` **[high]**. The methods (set stable since
2023; fields occasionally added):

- **`execute`** — symbolic rewriting with `max-depth`, `cut-point-rules`,
  `terminal-rules`, step timeouts; stop reasons include stuck / depth-bound /
  timeout / branching / cut-point-rule / terminal-rule / vacuous **[high]**;
- **`simplify`**;
- **`implies`** — pattern implication (antecedent ⇒ consequent), returning
  `valid` + implication + substitution; this is the subsumption check
  **[high]**;
- **`add-module`** — upload extra KORE lemma modules at runtime, identified by
  SHA256 of the unparsed module string **[high]**;
- **`get-model`** — Sat/Unsat/Unknown with a substitution witness **[high]**;
- **`cancel`**.

pyk's `KCFGExplore` drives exactly this: `execute` grows the KCFG, `implies`
checks subsumption into the target, `get-model` refutes/witnesses nodes,
`add-module` injects claim dependencies and circularities **[high]**.

## Where SMT is used — and the shallow translation

SMT (Z3 by default, spoken over SMT-LIB 2) is used **only for
satisfiability/validity of side conditions, never for rewriting itself**
**[high]**. Concretely
([introduction.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/introduction.md):
"we only check satisfiability of a predicate, using the solver to refute
impossible execution paths"):

1. **Refuting infeasible paths.** After unifying a rule's LHS with the
   configuration, the `requires` clause is conjoined with the path condition
   and simplified; residual predicates go to the solver. Booster checks whether
   `K ⇒ P` or `K ⇒ ¬P`; if neither (Unknown), it falls back to legacy kore,
   which may branch on the condition. `ensures` clauses are re-checked after
   the rewrite **[high]**.
2. **`implies`/subsumption** checks during proving **[high]**.
3. **`get-model`** for counterexamples and node refutation **[high]**.

The translation is **deliberately shallow** **[high]** (stable for years; no
new theories added): only `Int` and `Bool` are interpreted — essentially
**QF_LIA + Bool + uninterpreted functions**. Quantifiers, `\ceil`, `\in`,
Bytes, String, Map/Set/List, and anything else untranslatable are abstracted to
**fresh uninterpreted variables/functions** (`SMT-N` counters in
[booster's Translate.hs](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/library/Booster/SMT/Translate.hs),
`SMTDependentAtom` in
[kore's Translate.hs](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/kore/src/Kore/Rewrite/SMT/Translate.hs)).
User sorts become `DeclareSort`. There is **no array, bit-vector, or bytes
theory** **[high]**. Legacy kore does *attempt* translating quantified formulas
(for smt-lemma axioms), falling back to uninterpreted **[high]**. Practical
consequence: bytes/storage/map reasoning in real projects (KEVM/Kontrol) is
done with K-level `simplification` lemma rules, not SMT theories **[high]**.

The legacy kore engine keeps **one incremental Z3 process** for all queries,
initialized with user sorts/symbols, constructor axioms, and smt-lemmas
**[high]**. A documented soundness caveat: Z3 treats partial functions
(`div`/`mod`) as total
([booster.md](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/docs/booster.md),
citing issue #3603) **[high]**.

Server defaults (from
[Server.hs](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/tools/booster/Server.hs);
CLI flags churn — verify before scripting): solver = Z3, reset-interval 100;
flags `--no-booster-smt`, `--fallback-on Branching,Stuck,Aborted` (default),
`--interim-simplification N`, `--no-post-exec-simplify` **[high]**. The default
SMT timeout is **125 ms with retry limit 3** — *not* unlimited (the researcher
pass initially misreported this as unlimited; verified against
`defaultSMTOptions` in `Booster/SMT/Runner.hs` and the CLI defaults in
`CLOptions.hs`; the `Unlimited` values in `Server.hs` are always overridden
when SMT is enabled) **[high]**. Anyone driving `kore-rpc-booster` should
expect fast SMT timeouts by default and raise `--smt-timeout` for hard queries.

## Attributes wiring K to the solver

From the [K user manual](https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md)
(attribute semantics stable for years; note kframework.org's rendering
currently 403s — the source of truth is the markdown in the k repo) **[high]**:

- **`smtlib(name)`** — declares a production as a new SMT symbol with
  *uninterpreted function* semantics;
- **`smt-hook(sexpr)`** — gives a builtin SMT-LIB 2 encoding, with `#1`, `#2`…
  placeholders for arguments; assumes all symbols in the term are already
  declared;
- **`smt-lemma`** — marks a rule to be asserted to Z3 as the conditional
  equality `(=> REQ (= LHS RHS))`;
- **`simplification(priority)`** (default 50) — function-simplification rules
  applied by *matching* (not unification) that "the backend is free to apply at
  any time", with `concrete(vars)`/`symbolic(vars)` restricting when they fire.

## Proving: claims, APRProof, KCFG

Reachability claims are `claim` sentences with `all-path`/`one-path` attributes
(settable per rule or per module); `trusted` admits a claim as an
already-proven circularity without discharging it **[high]**. One-path claims
exist in the attribute system, but the maintained pipeline
(kprove/Kontrol/KEVM) proves **all-path** claims **[high]**.

The modern prover is pyk's **`APRProof`/`APRProver`**
([reachability.py](https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/proof/reachability.py);
pyk now lives inside `runtimeverification/k` under `pyk/`, so module paths may
shift), implementing all-path reachability logic (Stefanescu et al.) plus a
bounded-model-checking extension, over a **KCFG** with a single init node and a
single target node; dependencies are injected as priority-20 rule modules and
circularities via `add-module` **[high]**. The step logic: bound-check →
terminal-check → subsumption-`implies` into the target → `execute` to extend.
Status is PASSED iff no pending or failing leaves remain (or the claim is
admitted); FAILED if failing leaf nodes exist **[high]**.

KCFG structure ([kcfg.py](https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/kcfg/kcfg.py);
data model stable, serialization format version-guarded) **[high]**:

- **Node** = int id + `CTerm` (configuration + path constraints) + attrs
  (VACUOUS, STUCK);
- **Edge** = source/target + depth + applied rule names;
- **Cover** = subsumption of source into target via a constraint substitution
  (`CSubst`);
- **Split** = case split into (node, CSubst) targets;
- **NDBranch** = nondeterministic rule choice; **MergedEdge** collapses
  consecutive edges.

The whole graph (nodes, edges, covers, splits, ndbranches, aliases) plus
init/target and pending/terminal/stuck/vacuous flags, refutation subproofs and
circularity/dependency modules serializes to **JSON** — this is the persisted
artifact a Covalence importer would consume **[high]**.

## The gap: no checkable proof object

**There is no independently checkable proof object anywhere in the production
symbolic pipeline** **[high]**. The KCFG/APRProof JSON is a proof *sketch*: its
validity rests entirely on trusting the Haskell backend (unifier, equation
engine, simplifier) plus Z3. The only proof-object work is external and
**concrete-execution-only**:

- [runtimeverification/proof-generation](https://github.com/runtimeverification/proof-generation)
  (archived Feb 15 2024, NCSA license) formalized matching logic and Kore in
  **Metamath** (~250-line-TCB matching-logic formalization) and generated
  Metamath proof objects for concrete rewriting traces, checkable by standard
  Metamath verifiers (CAV'21, ["Towards a Trustworthy Semantics-Based Language
  Framework via Proof Generation"](https://link.springer.com/chapter/10.1007/978-3-030-81688-9_23))
  **[high]** (frozen since archive, so its Kore formalization may lag current
  KORE syntax);
- its successor is Pi Squared's
  ["Proof of Proof"](https://docs.pi2.network/proof-of-proof/core-technologies/formal-semantics-and-the-k-framework),
  which consumes LLVM-backend "proof hints" (execution traces linking each
  configuration transition to the rewrite rule that caused it) and emits
  matching-logic proof-calculus certificates **[high]** (proprietary and
  fast-moving — re-check before relying on details).

No symbolic/reachability proof objects are emitted by the Haskell backend
today — the symbolic side is exactly the uncovered gap **[high]**.

**Licenses:** haskell-backend, llvm-backend, and the k repo (frontend + pyk)
are BSD-3-Clause; proof-generation is University of Illinois/NCSA — all
permissive and import-compatible **[medium]** (the k repo's license was not
fetched directly this session; verify its LICENSE file before vendoring).

## What this means for Covalence

- The **KORE RPC protocol + KCFG JSON** are the natural seams: small, JSON,
  documented, stable. A Covalence importer would replay KCFG **Edges** as
  internally derived relation steps, discharge **Covers/Splits** with
  internally checked implications, and re-certify the SMT-discharged side
  conditions.
- The SMT surface is deliberately tiny — **QF_LIA + UF** — which makes
  re-verification (or proof-logging Z3 and replaying) tractable; everything
  hard (bytes, maps) is K-level `simplification` lemmas, i.e. more rewrite
  rules of the same shape we'd already be replaying.
- The **symbolic proof-object gap is real and uncontested**: RV's own
  proof-generation line covers only concrete traces, and Pi Squared's
  continuation is proprietary. An internal Covalence certifier for the
  *symbolic* pipeline (KCFG replay + implication discharge) would be filling a
  hole nobody upstream fills.
- The archived Metamath formalization of matching logic + Kore is directly
  reusable ground truth for an internal `Derivable_ML`/`Derivable_Kore`
  relation — and Metamath replay is machinery we already have.

## Sources consulted

- https://github.com/runtimeverification/haskell-backend
- https://github.com/runtimeverification/llvm-backend
- https://github.com/runtimeverification/haskell-backend/blob/master/docs/introduction.md
- https://github.com/runtimeverification/haskell-backend/blob/master/docs/2022-07-18-JSON-RPC-Server-API.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/docs/booster.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/library/Booster/SMT/Translate.hs
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/kore/src/Kore/Rewrite/SMT/Translate.hs
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/tools/booster/Server.hs
- https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/proof/reachability.py
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/kcfg/kcfg.py
- https://github.com/runtimeverification/proof-generation
- https://docs.pi2.network/proof-of-proof/core-technologies/formal-semantics-and-the-k-framework
- https://link.springer.com/chapter/10.1007/978-3-030-81688-9_23
