# ACSet Datalog → Datafun (sketch)

Forward-looking note on where a Datafun-style language slots into the
`covalence-acset` recursive-query engine. Status: sketch.

## What we have

`covalence-acset::datalog` evaluates a `Program` (derived relations + rules,
bodies conjoining instance morphism/attribute atoms and recursive relation
atoms) to a **least fixpoint** by naive bottom-up iteration. Semantically this
is a **monotone map on the powerset lattice of tuples** (ordered by ⊆), iterated
to its lfp. Parts are finite, so the lattice is finite and the iteration
converges. Each `Rule` is one disjunct of that transformer.

What the engine *assumes but does not check*: that the transformer is monotone
(true here because rules are positive — no negation), and it re-derives
everything every round (naive, not semi-naive).

## What Datafun is

Datafun (Arntzenius & Krishnaswami, ICFP'16) is a typed functional language for
Datalog. Its core: **semilattice types**, a **monotone function space**
`A →⁺ B`, and a fixpoint `fix : (L →⁺ L) → L` over a suitable (finite-height /
pointed) semilattice `L`. Crucially, **monotonicity is tracked in the type
system**, so `fix` is only applied to provably-monotone maps — which is exactly
the side condition our engine assumes.

## The seam

Our engine is the **denotation**; Datafun would be the **surface**:

- A Datafun term of type `Rel →⁺ Rel` denotes a monotone transformer; it
  compiles to a rule set (or directly to a transformer closure the loop drives).
- Datafun's `fix` compiles to our fixpoint loop (naive now; semi-naive later).
- Datafun's **monotonicity-in-types** *replaces* our "assumed monotone, positive
  rules only" with a static guarantee — and it safely admits user-defined
  recursive analyses (provenance closure, trust propagation, impact analysis)
  written in a total language, compiled to the same engine that *validates* the
  interchange.

## Why it matters here

- **Semilattices beyond sets.** Generalising relation values from "set of
  tuples" to arbitrary semilattices (boolean reachability, min-plus shortest
  paths, provenance semirings) is the natural `AttrVal`-lattice generalisation —
  Datafun's typing makes it principled.
- **Incremental evaluation (the Coln/DBSP angle).** Monotone semantics is the
  basis for semi-naive and differential (DBSP-style) evaluation. Coln's storage
  lineage is already DBSP/Automerge; a Datafun front-end over an incremental
  backend is the convergence point.

## Concrete next steps (rough order)

1. **Semi-naive evaluation** — delta rules, only fire on newly-derived tuples.
2. **Semilattice-valued relations** — values, not just membership; `AttrVal`
   lattices (bool / min-plus / set).
3. **Stratified negation** — needed for anything beyond positive Datalog.
4. **Tiny Datafun-ish AST → `Program` compiler** — monotone lambda + `fix` +
   comprehensions, with a monotonicity checker.
5. **Differential/incremental backend** — DBSP-style, matching Coln's substrate.
