# covalence-metamath

A tiny, theory-agnostic [Metamath] proof checker whose expressions are
[`covalence-sexp`] `SExpr`s. This is **pillar 2** of the project's metatheory
program (`docs/theories-models-and-logics.md` §5.5): a substitution /
representation engine we can later prove equivalent to our locally-nameless HOL
syntax as a metatheorem, and use to replay untrusted Metamath proofs through the
kernel (the same untrusted-frontend → kernel-recheck pattern as
`covalence-alethe`).

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

Implemented: the frame/database model, the substitution engine, schematic rule
application, distinct-variable checking, the RPN proof checker, an uncompressed
`.mm` parser, and ≥3 hand-encoded example theories (propositional calculus, the
Metamath-book "demo0" arithmetic/logic theory, a small binary-operation theory,
and a distinct-variable theory) with proofs that verify and bad proofs that are
rejected. Deferred (see [`SKELETONS.md`](./SKELETONS.md)): the compressed proof
format, `set.mm` scale, file inclusion, and the `covalence-hol` import tactic +
representation-equivalence metatheorem.

[Metamath]: https://us.metamath.org/
[`covalence-sexp`]: ../covalence-sexp
