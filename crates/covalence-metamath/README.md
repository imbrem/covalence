# covalence-metamath

The **`.mm` format / IO reader** for the theory-agnostic Metamath proof checker
whose expressions are [`covalence-sexp`] `SExpr`s.

> **Crate split.** Because a Metamath database *is* the substrate for defining a
> logic (`notes/theories-models-and-logics.md` §5.6), the substitution **engine**
> — the expression model, substitution, the frame/database model, and the RPN
> proof checker — lives first-class in [`covalence_hol::metamath`]. *This* crate
> is the messy reader on top of it: `.mm` tokenising, scoping, comments, and (as
> north stars) compressed-proof decoding, file inclusion, and `set.mm`
> ingestion. The engine types are re-exported here, so
> `covalence_metamath::{Database, parse, verify_all, …}` keeps working.

## Why this exists — Metamath as the shared logic-definition substrate

The primary goal is to **define logics _inside_ Covalence**: Metamath's pure
metavariable-substitution metalogic is a universal, theory-agnostic substrate in
which any standard logic (propositional calculus, FOL, ZFC, PA, a group theory,
…) is written down as a database — constants, typed variables, and its axioms
and inference rules as substitution schemas. It is a **shared syntax everyone can
use**: a common medium for *stating* and *deriving* across many logics.

Under this view, **everything else is an optimization**. When Covalence asserts
`P` relative to a Metamath-defined logic, the claim is precisely *"there exists a
Metamath derivation of `P`"* — a pure existence statement; the derivation itself
may be astronomically long and impractical to construct. A short HOL-kernel
proof, a WASM-oracle discharge, or a replayed `set.mm` proof is then just a *more
practical certificate of that existence*. Metatheorems take the shape *"if a ZF
derivation of `A` exists, a GT derivation of `S(A)` exists"* — existence-transport
between databases witnessed by a rewriting function `S` on Metamath terms
(relative interpretation, proved by induction on derivations, native to the
substrate).

The link to our native machinery is **one correspondence theorem used both
ways**. Proving **Metamath-PA ≅ our manual PA** (a) *validates downward* that the
Metamath model means what we expect — it certifies the `.mm` definition is
faithful to the logic — and (b) *accelerates upward*: the very same `≅` lets our
manual PA, the HOL kernel, and WASM decision procedures discharge hard
Metamath-PA goals by running fast and transporting the result across the
correspondence, certifying the giant derivation exists without building it. The
bridge into the HOL kernel (`notes/theories-models-and-logics.md` §5.5,
**pillar 2**) is the special case where `S` lands in HOL's `IsThm`; that bridge
uses the same untrusted-frontend → kernel-recheck pattern as `covalence-alethe`.

## What Metamath is

Metamath is a *metalogic*: its only proof primitive is **metavariable
substitution**. A database is a flat list of declarations:

| keyword | meaning |
|---------|---------|
| `$c`    | constant symbols |
| `$v`    | variable symbols |
| `$f`    | floating hypothesis — a variable's typecode (its "type") |
| `$e`    | essential hypothesis — a logical premise |
| `$a`    | axiom (a schema: mandatory hyps ⊢ conclusion) |
| `$p`    | theorem (an axiom plus an RPN proof) |
| `$d`    | distinct-variable side condition |
| `${ $}` | scoping for hypotheses and `$d` |

A proof is a reverse-Polish sequence of labels. Applying an assertion pops its
mandatory hypotheses off a stack, unifies the floating hypotheses to build a
variable→expression substitution, checks the essential hypotheses and the
distinct-variable conditions, and pushes the substituted conclusion. The
verifier core is famously small — this crate keeps it that way.

## The expression encoding (flat-sequence vs structured-tree)

Real Metamath manipulates flat *symbol strings*; their *structure* comes from a
separate grammar that the trusted verifier never consults. We mirror that: an
expression is an `SExpr` **list whose head is the typecode and whose tail is the
flat math-symbol sequence** — e.g. `( wff ( ph -> ps ) )` is the flat list
`(wff "(" ph "->" ps ")")`, **not** the nested tree `(wff (-> ph ps))`.

We deliberately chose this **faithful-flat-sequence** encoding over a
**structured-tree** one. Flat sequences are bit-for-bit faithful to `set.mm`
substitution (a substituted variable *splices* its replacement body into the
parent list), sidestep grammar ambiguity (the checker never needs to know that
`( ph -> ps )` parses as an implication), and keep the substitution engine
trivially correct. Structured trees are nicer for the downstream *metatheory*
(substitution becomes a plain tree rewrite) but require the grammar to build,
reintroducing the ambiguity Metamath was designed to avoid — so that encoding is
deferred to the future `covalence-hol` bridge layer, where the grammar lives in
the (untrusted) representation rather than the checker. We use `SExpr` rather
than a bare `Vec<Symbol>` because it is the project's canonical expression
medium: turning today's flat list into tomorrow's structured tree is one
`map`/grammar pass on a shared type, not a reparse.

## API sketch

```rust
use covalence_metamath::{parse, verify_all};

let db = parse(source_mm)?;        // parse an uncompressed .mm string
let n  = verify_all(&db)?;         // kernel-recheck every $p; returns #verified
```

* [`parse`] — uncompressed `.mm` subset (`$c $v $f $e $d $a $p $. ${ $}`,
  `$( … $)` comments).
* [`Database`] / [`Assertion`] / [`Frame`] — the frame model.
* `apply_subst` — the substitution engine (the heart of "Metamath rewrite").
* [`verify_all`] / [`verify_assertion`] — schematic rule application + RPN proof
  checking, with genuine typecode and `$d` checking.

## Status

Implemented: the engine (frame/database model, substitution, schematic rule
application, distinct-variable checking, the RPN proof checker — now in
[`covalence_hol::metamath`]), this crate's uncompressed `.mm` parser, and ≥3
hand-encoded example theories (propositional calculus, the Metamath-book "demo0"
arithmetic/logic theory, a small binary-operation theory, and a distinct-variable
theory) with proofs that verify and bad proofs that are rejected. Deferred for
this reader (see [`SKELETONS.md`](./SKELETONS.md)): the compressed proof format,
`$[ $]` file inclusion, and `set.mm`-scale streaming. Engine-side deferrals (the
`#logic` correspondence layer, the import tactic + representation-equivalence
metatheorem) are tracked in `covalence-hol/src/metamath/SKELETONS.md`.

[Metamath]: https://us.metamath.org/
[`covalence-sexp`]: ../covalence-sexp
