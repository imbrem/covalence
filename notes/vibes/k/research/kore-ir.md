+++
id = "N000R"
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

# KORE: K's kompiled IR, as an ingestion surface

> **STATUS: RESEARCH SURVEY (AI-drafted, web-sourced).** Researched 2026-07-13
> via live fetches of primary sources; claims individually marked with
> certainty. Cross-checked by an independent verification pass; corrections
> applied.

Scope: the KORE textual language (sentences, patterns), what a real kompiled
`definition.kore` contains (prelude, cells, injections, axiom shapes,
attributes including priority/owise), the JSON encodings, stability, the
hooked-sorts caveat, and the case that `definition.kore` is the right surface
for a Covalence K frontend. Companion to
[`k-framework-today.md`](./k-framework-today.md). Concrete axiom shapes below
were verified against a real K 7.1.288 `definition.kore`
([xsts-semantics](https://raw.githubusercontent.com/domino-1/xsts-semantics/main/kompiled/definition.kore),
1.14 MB) and cross-checked against pyk's emitter.

## The textual language

The canonical spec is
[haskell-backend/docs/kore-syntax.md](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/kore-syntax.md)
("the syntax of Kore, as admitted by the Haskell Backend") — one page of BNF
**[high]**. A definition is a leading attribute list followed by a sequence of
modules, topologically sorted by imports; each module contains **sentences**,
each ending in a bracketed attribute list (attributes are themselves
application patterns) **[high]**:

- `import`, `sort` / `hooked-sort`, `symbol` / `hooked-symbol`
  (`symbol <symbol>(<sorts>) : <sort> [<attributes>]`),
- `alias … where lhs := rhs`,
- `axiom {SortVars} <pattern> [<attributes>]`, and `claim` (same shape —
  kprove compiles spec modules to claims, so one reader covers proof
  obligations too).

**Patterns** **[high]**: element variables `X:Sort`, set variables `@X:Sort`,
applications `sym{SortArgs}(args)`, string literals, domain values
`\dv{Sort}("…")`, and the matching-logic connectives `\top \bottom \not \and
\or \implies \iff \exists \forall \mu \nu \ceil \floor \equals \in \next
\rewrites` (plus `\left-assoc`/`\right-assoc` sugar). `\equals{S1,S2}(p1,p2)`
takes operand + result sort parameters; `\mu`/`\nu` take no sort parameter;
`\rewrites{S}(l,r)` relates two same-sort patterns **[high]**.

Two verified corrections to common lore:

- **Textual `\and`/`\or` are n-ary**, not binary: the grammar was updated to
  multiary `\and{S}(<patterns>)` on 2025-01-15 (haskell-backend PR #4086),
  aligning it with the JSON encoding **[high]** (the researcher pass initially
  reported them as binary; verified against the current kore-syntax.md).
  Binary is merely the common emitted form — **a parser must accept n-ary from
  day one**.
- "Set variables occur only under fixpoints" is a usage observation, not a
  spec constraint — the grammar admits a set variable anywhere a variable
  pattern may occur **[high]**.

**Binders**: the logic's only binders are `\exists`/`\forall` (element vars)
and `\mu`/`\nu` (set vars). K *object-language* binders (lambdas etc.) compile
to ordinary application symbols carrying a `binder` attribute, with
capture-avoiding substitution implemented by backend hooks (haskell-backend
`Kore/Variables/Binding.hs`, llvm-backend `runtime/meta/substitution.cpp`);
the K manual's attribute index lists `binder` with "No reference yet" — it is
effectively undocumented **[medium]** *(backend binder semantics inferred from
file locations, not read line-by-line; verify before implementing
substitution)*. For a consumer, binder symbols look like plain first-order
applications whose first argument is a variable; the binding discipline must
be reconstructed from the attribute.

## What a kompiled `definition.kore` contains

The file is fully elaborated and first-order-flavored **[high]**:

- **Header**: a definition-level attribute list naming the configuration
  initializer — `[topCellInitializer{}(LblinitGeneratedTopCell{}()), …]`
  **[high]**.
- **Prelude**: BASIC-K/KSEQ — `kseq{}`/`dotk{}` build the `~>` K sequence;
  cell contents of sort K are wrapped via `kseq`/`dotk` and
  `inj{S,SortKItem}` **[high]**.
- **Hooked builtins**: e.g. `hooked-sort SortMap{}
  [concat{}(Lbl'Unds'Map'Unds'{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
  unit{}(Lbl'Stop'Map{}()), hook{}("MAP.Map")]` with hooked-symbols carrying
  `hook{}("MAP.concat")` etc. — the semantics live in backend hooks, **not**
  axioms **[high]** (attribute order is never significant per the spec).
- **Cells**: every configuration cell becomes a sort plus a constructor
  symbol tagged `cell{}()`, e.g. `sort SortKCell{}` and `symbol
  Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [cell{}(), constructor{}(),
  functional{}(), injective{}()]`, plus `…CellOpt` and `…CellFragment`
  sorts/symbols for partial configurations **[high]**.
- **Subsorting**: a single parametric injection `symbol inj{From,To}(From) :
  To [sortInjection{}()]` plus per-pair axioms `axiom{R} \exists{R}(Val:To,
  \equals{To,R}(Val, inj{From,To}(X:From))) [subsort{From,To}()]` **[high]**.
- **Constructor discipline**: no-confusion axioms (same-constructor
  `\implies(\and(c(X),c(Y)), c(\and(X,Y)))`; different-constructor
  `\not(\and(c1(…),c2(…)))`) and no-junk axioms (`\or` of constructor
  images), tagged `[constructor{}()]`; plus `functional` axioms **[high]**.
  Quirk: `\dv`-carrying sorts (SortBool, SortInt, …) get a trivial
  `\or(\top,\bottom)` no-junk axiom with a literal `// no junk (TODO: fix bug
  with \dv)` comment — present in emitted output for years **[high]**.

### Rewrite-rule axioms

A top-level K step rule compiles to **[high]**:

```
axiom{} \rewrites{SortGeneratedTopCell{}}(
  \and{Top}(LHS-configuration-term, requires-predicate-or-\top),
  \and{Top}(RHS-configuration-term, ensures-predicate-or-\top))
```

Side conditions are lifted to predicates as `\equals{SortBool,Top}(cond,
\dv{SortBool}("true"))`; trivial `requires true` becomes `\top`; K `#as`
aliases appear as term-level `\and` inside the LHS. Each axiom is preceded by
a `// rule …` comment showing the original KAST rule and source location
**[high]**. (Verified both in pyk's `krule_to_kore` and in the K 7.1.288
sample; one nuance: pyk emits a bare RHS when there are no ensures
constraints, while the Java-frontend output always writes `\and(RHS, \top)`
**[high]**.)

### Function-rule axioms

A K function rule compiles to a sort-parametric equational axiom **[high]**:

```
axiom{R} \implies{R}(
  \and{R}(requires-pred, \in{ArgSort,R}(X0, arg-pattern-0), …),
  \equals{RetSort,R}(f(X0,…,Xn), \and{RetSort}(rhs, ensures-or-\top)))
```

Seen verbatim in both sampled definitions (e.g. the KSEQ `append` axioms);
pyk's emitter uses a simpler `\implies{R}(\equals(requires,true),
\equals(lhs, \and(rhs,ensures)))` variant for functional rules **[high]**
*(the `\in`-based Java emission has been stable across K 5→7; the Python
pipeline may diverge slightly when it becomes the emitter of record)*.
Simplification rules (attribute `simplification`) use a related
`\implies`/`\equals` shape directly over symbolic arguments **[high]**.

### Attributes: identity, priority, owise

Axioms carry load-bearing metadata **[high]**: `UNIQUE'Unds'ID{}("<sha256>")`
(stable rule identity), `label{}("MODULE.name")`, `priority{}("N")`,
`simplification`, and `org'Stop'kframework…Location/Source` provenance.
Semantics that matter:

- **Default priority 50; `owise` becomes priority 200; the simplification
  default is also 50** **[high]** (the researcher pass initially reported the
  simplification default as 100; verified as 50 in the K user manual,
  `Kore/Attribute/Simplification.hs`, and the booster's attribute reader).
- **`owise` generates NO negated-condition axioms** — it is encoded purely as
  a priority, so priority ordering is a *backend convention*, extra-logical: a
  certifying consumer must model "lower-priority rules apply only when no
  higher-priority rule does" itself **[high]**. Defaults are also conventions:
  the file shows `simplification{}("")` etc., not resolved numbers.
- **Name mangling**: `'Unds'`=`_`, `'-LT-'`=`<`, `'-GT-'`=`>`, `'Stop'`=`.`,
  `'Pipe'`=`|`, with `Lbl`/`Sort`/`Var` prefixes (so `Lbl'-LT-'k'-GT-'` is
  `<k>`) **[high]**.
- Collection symbols carry semantic attributes (`assoc`/`comm`/`unit`/
  `element`, `binder`) that a consumer cannot ignore **[high]**.

### The kompiled directory, per K's own README

[K's kompiled-dir README](https://raw.githubusercontent.com/runtimeverification/k/master/k-frontend/src/main/resources/org/kframework/utils/file/README.md)
lists **[high]**: `definition.kore` ("the actual input for the backends"),
`syntaxDefinition.kore` (parsing subset), `macros.kore`,
`parsed.txt`/`compiled.txt` (human-readable), `backend.txt`,
`mainModule.txt`, `compiled.bin`, `haskellDefinition.bin`, the LLVM
`interpreter`, and warns verbatim: contents are **"subject to change without
warning and they should not be relied on for automation outside of what is
already tested on CI"**. It also warns definitions must be kompiled per
backend — mixing backends "can cause the backends to crash or, worse, give
unsound results" **[high]**.

## JSON encodings: kore-json and KAST JSON

Two distinct formats, both pyk-defined:

- **kore-json**: envelope `{"format":"KORE","version":1,"term":{…}}`, used by
  the kore-rpc / booster JSON-RPC servers
  (execute/simplify/implies/get-model/add-module, per
  [the RPC API doc](https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/2022-07-18-JSON-RPC-Server-API.md))
  and pyk **[high]**. Tags: `SortApp`/`SortVar`, `EVar`/`SVar`, `String`,
  `App{name,sorts,args}`, `DV{sort,value}`, `Top`/`Bottom`, `Not`,
  `Implies`, n-ary `And`/`Or` (`{tag,sort,patterns:[…]}`),
  `Exists`/`Forall`, `Mu`/`Nu`, `Ceil`/`Floor`,
  `Equals{argSort,sort,first,second}`, `In`, `Next`,
  `Rewrites{sort,source,dest}` **[high]**. Version pinned at 1 since 2022 —
  but note the n-ary And/Or change happened *without* a version bump, so
  expect occasional silent evolutions **[high]**.
- **KAST JSON** (frontend terms, pre-KORE): envelope
  `{"format":"KAST","version":4,"term":…}` on current master; nodes keyed by
  `node`: `KApply`, `KToken`, `KVariable`, `KSort`, `KLabel`, `KAs`,
  `KRewrite`, `KSequence` **[high]**. Whole compiled definitions are
  available as KAST JSON via `kompile --emit-json` → `kompiled/compiled.json`
  **[high]** *(the KAST version has bumped over time — was 2/3 in older pyk —
  pin per K version if consumed)*.
- **The booster is not a third format** **[high]**: `kore-rpc-booster` parses
  the same `definition.kore` and internalizes it into restricted custom term
  types (CNF requires-clauses, priority-bucketed rules indexed by `<k>`-cell
  head symbol), rejecting rules outside its subset and falling back to the
  full kore engine. The standalone hs-backend-booster repo is archived;
  booster lives inside haskell-backend now (active, its accepted subset
  shifts).

## Stability assessment

KORE has been remarkably stable **[high]**: kore-syntax.md had only 9 commits
from 2019-10-08 to 2025-01-15; the KSEQ prelude and function-axiom shapes are
essentially byte-identical between a ~2021-era kompilation and the K 7.1.288
sample; kore-json has stayed at version 1 since 2022. Both
runtimeverification/k and haskell-backend are BSD-3-Clause (licenses fetched
and verified) **[high]**. Set against this: the official
"subject-to-change-without-warning" caveat, and the multiary-`\and` episode as
a concrete instance of KORE evolving without a version bump. *(Version
numbers here — K v7.1.337, 2026-06-18 — rot within weeks; the format does
not.)*

## Hooked sorts/symbols: the caveat

Hooked sorts and symbols (INT, BOOL, MAP, SET, LIST, BYTES, …) get their
semantics from **backend hooks, not axioms** — the spec's aspiration that "all
semantic information contained in attributes should correspond to axioms
declared explicitly" is not fully true for hooks **[high]**. A certifying
consumer must supply its own theories for the (small, slowly-growing) hook
vocabulary, and treat hook-defined functions the way Covalence already treats
computation: construct certificates against internally-defined `Int`/`Map`/…
theories rather than trusting the hook.

## Why `definition.kore` is the right ingestion surface

The assessment, grounded in the findings above **[medium]** (the shape facts
are all [high]; the verdict is design judgment):

- **Elaborated**: configuration concretization, heating/cooling, macro
  expansion, and sort inference are already applied — every rule is an
  explicit `\rewrites` or `\implies/\equals` axiom.
- **Tiny grammar**, effectively S-expression-shaped, with an existing
  [tree-sitter-kore](https://github.com/runtimeverification/tree-sitter-kore)
  grammar and pyk's full textual parser (`pyk.kore.parser`) to crib from
  **[high]**.
- **Identity and provenance preserved**: `UNIQUE_ID` (sha256) and
  Source/Location attributes survive into the file **[high]**.
- **The alternative is bad**: parsing `.k` directly means reimplementing K's
  outer+inner parsers and ~32 compilation passes
  ([pyk pipeline.md](https://raw.githubusercontent.com/runtimeverification/k/master/pyk/docs/pipeline.md);
  KORE emission is stage 4 of 5, and the Java `ModuleToKORE.java` remains the
  emitter of record) **[high]**.
- **Claims come for free**: `claim` sentences use the same pattern language,
  so the same reader later covers kprove proof obligations **[high]**.

Costs to budget: (1) hooked sorts/symbols need our own axiomatization; (2)
priority/owise semantics is extra-logical and must be modeled; (3) name
demangling; (4) binder-attributed symbols; (5) accept n-ary `\and`/`\or`
everywhere; (6) pin a K version and snapshot-test sample `.kore` files against
the "subject to change" caveat.

## What this means for Covalence

`definition.kore` is a flattened matching-logic theory — exactly the
relations-as-axioms shape our Metamath and SpecTec frontends already consume.
The concrete plan it supports: parse the one-page KORE grammar (n-ary
connectives, mangled names), map each `\rewrites` axiom to a clause of a
`Derivable_Step`-style relation and each function axiom to a defining
equation, supply internal theories for the hook vocabulary, and reify
priority/owise ordering explicitly rather than inheriting it as convention.
Rule `UNIQUE_ID`s give us stable content-addressable rule identity for
incremental re-ingestion. Pin one K release, vendor a couple of kompiled
samples (BSD-3-Clause throughout) as golden fixtures, and treat pyk's
`kore/syntax.py` + `konvert/_kast_to_kore.py` as the de-facto spec where
kore-syntax.md is silent.

## Sources consulted

- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/kore-syntax.md
- https://raw.githubusercontent.com/domino-1/xsts-semantics/main/kompiled/definition.kore
- https://raw.githubusercontent.com/vishal-shukla11/csc_403/master/Supplement/k/calc-bool-kompiled/definition.kore
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/konvert/_kast_to_kore.py
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/kore/syntax.py
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/kast/kast.py
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/src/pyk/kast/inner.py
- https://raw.githubusercontent.com/runtimeverification/k/master/pyk/docs/pipeline.md
- https://raw.githubusercontent.com/runtimeverification/k/master/docs/user_manual.md
- https://raw.githubusercontent.com/runtimeverification/k/master/k-frontend/src/main/resources/org/kframework/utils/file/README.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/2022-07-18-JSON-RPC-Server-API.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/2024-10-18-booster-description.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/2020-06-22-Rewrite-Rule-Priorities.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/docs/2020-06-30-Combining-Priority-Axioms.md
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/kore/src/Kore/Attribute/Simplification.hs
- https://raw.githubusercontent.com/runtimeverification/haskell-backend/master/booster/library/Booster/Definition/Attributes/Reader.hs
- https://github.com/runtimeverification/tree-sitter-kore
- https://api.github.com/repos/runtimeverification/hs-backend-booster
- https://api.github.com/repos/runtimeverification/k / …/haskell-backend (metadata, licenses)
