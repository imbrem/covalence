+++
id = "N001Z"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Parsing as relations, not gas functions (discussion draft, agent-authored)

Response to: "why is the S-expr parser a gas function and not a relation (which we can
prove lifts to a partial function)? Parsing relations give a parser *and* a deparser for
free by symmetry (regexp-style)." I agree; this note argues it and ties it to the
relation-calculus base + the K/atoms plans. Not committed.

## Why it's a gas function today (the honest reason)

HOL is a logic of **total functions**. The reader `parseSexpr : nat → bytes → option
(sexpr × bytes)` (`init/sexpr_parse.rs`) recurses on the *bytes being consumed*, with
mutual expr/list recursion — that is not structural recursion on a single decreasing
argument, so a HOL *function* definition needs a termination justification. The options:

- **(a) fuel/gas** — add a `nat` bound and define via `natRec`: total by construction,
  *no termination proof*. This is what we do.
- **(b) well-founded / measure recursion** on remaining-input length — the principled
  total-function route, but that machinery **is not built** (see `inductive-support.md`
  §7.10: no measure/ordinal recursion).
- **(c) an inductive relation** + a functionality/determinism proof to extract a
  (partial) function.

So gas is the cheapest scaffold given (b) is missing. It is a *pragmatic artifact*: the
`sexpr_parse` SKELETONS already list "total-parse invariant" and "reader associativity"
as follow-ons — exactly the obligations a relational formulation subsumes.

## The relation formulation, and why it's better

Define the grammar as a **relation** `Parse ⊆ bytes × (sexpr × bytes)`
(`Parse inp (tree, rest)` = "reading `inp` yields `tree`, leaving `rest`"), or
`ParseAll ⊆ bytes × sexpr` for full consumption. Key facts:

1. **The machinery already exists.** An inductively-defined relation in HOL is the same
   impredicative-least-fixpoint shape we already use everywhere: the recursion engine's
   `Graph` (`init/inductive/graph.rs`), the prop-logic-in-HOL relations, the carved
   `Wf`. `Parse` is `∀R. Closed_grammar(R) ⟹ R inp out`, with one closure clause per
   grammar production. No new kernel machinery.
2. **No fuel artifact.** The relation *is* the declarative grammar; termination isn't a
   parameter of the object, it's a *theorem* about it (well-foundedness of the
   consumed-prefix order), proved once.
3. **Lift to a partial function by a determinism proof.** Prove `Parse` is
   right-unique (`Parse inp o1 ⟹ Parse inp o2 ⟹ o1 = o2`) — this is exactly the
   `graph_det`/uniqueness technique, and it is *easy* for S-expressions (the grammar is
   unambiguous / LL). Then either `parse inp := ε o. Parse inp o`, or — better — **keep
   the gas function as a certified executable accelerator** (below).

## The deparser "for free by symmetry" — precisely

The deparser is the **converse relation** `Parse°`, and the base relation calculus
*already has this as a primitive*: `transpose` (Phase 0). So parse and deparse are **one
object and its transpose** — you don't define two things.

The one honest subtlety: parsing is functional text→struct (deterministic) but **not
injective** — whitespace and redundant parens mean many texts parse to the same tree.
So `Parse°` (struct→text) is a genuine *relation* (one tree, many valid renderings). The
symmetry therefore gives you, for free:

- the entire **deparse relation** `Parse°` (every well-formed rendering of a tree), and
- the round-trip: `Parse (deparse s) = s` reduces to `deparse s ∈ Parse° s`, which is
  *immediate* once `deparse` is a section of `Parse°`.

A concrete `deparse : sexpr → bytes` is then a **functional section** of `Parse°` you
*choose* (canonical printer — minimal whitespace, canonical parens) and prove is a
section (`∀s. Parse° s (deparse s)`). That's the only "real work" the symmetry doesn't
hand you — and it's small and canonical. (This is the standard invertible-syntax story:
one description → parser + printer; the printer picks a canonical inverse.)

## The payoff: the base relation calculus IS a parser-combinator algebra

This is the part that makes me think it's the *right* direction, not just a nicety. The
positive relation calculus you already built (`rel.rs`: `compose`/`join`/`meet`/
`transpose`) is exactly the algebra of grammars:

| Grammar / regexp op | Base relation op |
|---|---|
| sequencing `p q` | `compose` (thread the `rest`) |
| alternation `p \| q` | `join` (union) |
| intersection / "and-predicate" | `meet` |
| **deparse** (printer) | **`transpose`** (converse) |
| negative lookahead / complement | `complement` — *gated* (needs the admitted-axiom discipline; you can't refute a parse by executing, only by an axiom — which is *correct*: "this input does NOT parse" is a negative fact) |
| Kleene star / repetition | least fixpoint (the same impredicative-relation shape) |

And it lands *exactly* on two things you already wrote down:

- **`atoms.md` line 4–5**: "define syntax and generate parsers **as relations and as
  functions**." The relation is the spec; the gas/executable function is the derived
  accelerator; `execute` (base) bridges them by witnessing `Parse(input, output)` from
  running the untrusted parser. Same object, two forms — which is the K-framework story.
- **`atoms.md` literal zoo**: each numeral base (bin/oct/dec/hex/LEB128/fixed-width) is a
  parse relation `bytes ↔ nat`; **"mixed" (`0xABC ∪ 123 ∪ 0b101` as one relation) is a
  `join`** of the per-base relations; each base's **deparser is its `transpose`**; the
  int literals are `compose(sign, nat-relation)`. The whole atom table becomes an
  algebra of relations closed under the base operations.

So "parsing relations" isn't a separate feature — it's the relation-calculus base
*applied to syntax*, and it unifies the parser, the deparser, the literal atoms, and the
K "syntax as relations and functions" goal under one calculus.

## The executor story (why the gas function doesn't disappear)

Keep the fuel parser — it becomes the **executable witness**. In the base's terms it's
an untrusted `Rel(parse_fn) : (bytes, sexpr×bytes) → bool`; `execute` runs it and mints
the positive membership `Parse(input, output)`. The *trusted spec* is the HOL relation;
the gas function is the *fast oracle*. This is precisely the base's execute-vs-spec
asymmetry (positive-only: running the parser proves `it parses to X`, never `it does
not parse` — negation needs the grammar relation + an axiom/derivation). So:

- **spec** = the inductive `Parse` relation (declarative, trusted, transpose gives
  deparse),
- **executor** = the gas function (`Rel(f)`, untrusted, fast, certified by `execute`),
- **derived partial function** = `parse := ε o. Parse inp o`, proved to agree with the
  executor on its domain.

Three views of one grammar, bridged by `execute` + the determinism theorem — which is
the whole point of the relation-calculus base.

## What it would take (concretely) — and a suggested first cut

1. Define `Parse` for the S-expr grammar as an inductive relation (reuse the
   `Graph`-style impredicative fixpoint; one clause per production: atom-run, `(`, list
   tail, `)`, whitespace).
2. Prove **determinism** (right-uniqueness) — grammar is unambiguous; `graph_det`
   technique.
3. Prove **termination / totality-on-well-formed-input** (well-founded on consumed
   prefix) → lift to `parse : bytes → option sexpr`.
4. Define the **canonical `deparse`** as a section of `Parse°` (`transpose`), prove
   `∀s. Parse° s (deparse s)` ⟹ round-trip `parse (deparse s) = some s`.
5. Prove the **gas parser agrees** with `Parse` on its domain (`execute`-certified), so
   the existing `sexpr_parse` becomes the accelerator rather than the definition.

**Suggested first demo** (small, high-signal): do this for a *single numeral base* first
— `ParseNat_dec ⊆ bytes × nat` — since it's the atom the literal zoo needs anyway, the
determinism/termination proofs are trivial, and it exercises the full loop (relation +
transpose-deparse + gas-executor + `join` for "mixed"). Then S-expressions, then the
grammar-combinator layer that the K plan wants.

## Open questions for us

- **Where does the relational grammar layer live** — **`crates/lang/grammar`
  (`covalence-grammar`) is already the right home.** v0 ships *proper regexes*
  `Regex<A>` over a generic alphabet (concat/alt/class/star/plus/rep), dependency-light,
  wasm-clean, forbids `unsafe`, and its own docs say it's meant to be "lifted into
  kernel-verified computations" (CFG/PEG classes are planned). So the plan writes
  itself: (1) the regex *algebra* already mirrors the base relation calculus
  (concat→`compose`, alt→`join`, class→atom relation, star→least-fixpoint); (2) "lift
  into the kernel" = give each `Regex<A>` (and later CFG) a HOL **`Parse` relation**
  semantics; (3) the executable matcher is the gas/`Rel(f)` accelerator; (4) `transpose`
  gives the deparser. This crate + the base `rel.rs` calculus are two halves of the same
  thing — the surface grammar datatype and the relational semantics it lifts to.
- **Canonical-printer policy**: is `deparse` always the minimal canonical rendering, or
  do we want a *family* of sections (pretty vs compact)? The relation supports all; we
  pick which are functions.
- **How much do we lean on `transpose` vs. a separately-proved printer?** For an
  unambiguous grammar the transpose-section is clean; for whitespace-rich or layout
  grammars (Haskell!) the printer is more than a section of the parser's converse — it's
  its own canonicalization. Worth deciding the boundary.
- **Relation to K's matching**: K's "syntax as relations, simple vs full matching
  fragment" is the same idea one level up (matching = relational rewriting). Is the
  parsing-relation layer a special case of the K matching machinery, or its foundation?
  (Same open question as the `SExprRep`/Lisp note — probably the parsing relations are
  the *ground case* K generalizes.)
