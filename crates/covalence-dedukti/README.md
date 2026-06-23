# covalence-dedukti

A reader for the [Dedukti] `.dk` format — the concrete syntax of the
**λΠ-calculus modulo rewriting** (LF + user rewrite rules). This is the lower,
**HOL-free** crate: it depends on nothing in the kernel, so the future HOL
bridge in `covalence-hol` depends on *this* crate, mirroring how
[`covalence-metamath`](../covalence-metamath) sits below `covalence-hol`.

Dedukti is a logical framework: many systems (Coq/Rocq, Matita, HOL, Agda, …)
export their proofs to `.dk` via translators, encoding their source logic as a
Dedukti signature of declarations + rewrite rules. That makes a `.dk` file a
uniform carrier for derivations from very different logics.

## What it does today

Lexes and parses a `.dk` source into a faithful, queryable [`Signature`]:

- **terms** — `Type`, identifier references (unresolved: variable vs. constant
  is not distinguished syntactically), application, λ-abstraction (`x => t`,
  `x : A => t`), and (dependent) products (`x : A -> B`, `A -> B`);
- **declarations** — `name : ty.`, `injective …`, `defac`/`defacu …`;
- **definitions** — `def name [: ty] [:= body].` — and **opaque theorems** —
  `thm name [: ty] := body.`;
- **rewrite rules** — `{name} [ctx] lhs --> rhs.` (grouped + optionally named);
- **commands** — `#NAME #REQUIRE #EVAL #INFER #CHECK/#ASSERT(+NOT) #PRINT #GDT`,
  plus a catch-all for other directives.

```rust
use covalence_dedukti::parse;

let sig = parse("Nat : Type. zero : Nat. succ : Nat -> Nat.\n\
                 def plus : Nat -> Nat -> Nat.\n\
                 [m] plus zero m --> m.").unwrap();
assert_eq!(sig.declarations().count(), 3);
assert_eq!(sig.rules().count(), 1);
```

It performs **no** scope resolution, type checking, or rewriting — the `.dk` is
assumed already checked by Dedukti. See [`SKELETONS.md`](./SKELETONS.md) for the
roadmap: a λΠ-modulo checker, the `covalence-hol` internalisation of Dedukti
derivations, and the end goal of cross-theory (MLTT ↔ set-theory) metatheorems.

[Dedukti]: https://deducteam.github.io/
