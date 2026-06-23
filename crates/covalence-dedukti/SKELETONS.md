# Skeletons — covalence-dedukti

Intentional placeholders and deferred work in this crate. Its scope is the
**`.dk` reader** for the λΠ-calculus modulo rewriting: the term model
([`term`](src/term.rs)), the top-level entry / signature model
([`entry`](src/entry.rs)), and the lexer + parser ([`lex`](src/lex.rs),
[`parse`](src/parse.rs)) — the lower, **HOL-free** crate, mirroring
[`covalence-metamath`](../covalence-metamath). The *consumer-side* bridge — the
HOL-backed internalisation of Dedukti signatures and derivations, and the
cross-theory metatheorems — is `covalence-hol` work and is tracked below as the
north star (it will live in `covalence-hol`'s `metalogic` registry once started,
alongside the `mm_*` modules it parallels). See the repo
[`CLAUDE.md`](../../CLAUDE.md) § Skeletons for the policy.

## Done (no longer deferred)

- **Lexer.** ✅ [`lex`](src/lex.rs) tokenises the full surface: identifiers
  (including digit-led names like `1`/`65536`, and `{| … |}` quoted identifiers
  used by translators), `module.name` qualified identifiers, nestable
  `(; … ;)` comments, string literals, the `#WORD` directive heads, and every
  operator/punctuation token (`:` `:=` `->` `=>` `-->` `==` `,` `.` `()[]{}`).

- **Parser.** ✅ [`parse`](src/parse.rs) is a hand-written recursive-descent
  parser following Dedukti's Menhir grammar: declarations (`name : ty.`,
  `injective …`, `defac`/`defacu …`), definitions (`def name [: ty] [:= body].`),
  opaque theorems (`thm name [: ty] := body.`), curried `(x : ty)` parameters,
  grouped + named rewrite rules (`{name} [ctx] lhs --> rhs`), and the command
  family (`#NAME #REQUIRE #EVAL #INFER #CHECK/#ASSERT(+NOT) #PRINT #GDT`, plus a
  catch-all for other directives). Operator precedence (application binds
  tighter than `->`/`=>`; `->` right-associates) and the binder/application
  lookahead are handled; `{ … }` dot-patterns parse only in rule-LHS position so
  an rhs never absorbs the next rule's `{name}`.

- **Term model + Display.** ✅ [`Term`](src/term.rs) faithfully captures `Type`,
  unresolved references, application, λ-abstraction (with/without annotation),
  and (dependent) products, with a precedence-correct `Display` that
  round-trips. AST helpers (`unfold_app`, `apply`, …) and a [`Signature`] query
  surface (`declarations`/`definitions`/`theorems`/`rules`/`commands`/
  `symbol_names`/`module_name`) are in place.

- **Real-file validation.** ✅ The parser was checked against real Dedukti
  sources (e.g. the upstream `tests/OK/sharing.dk` and `dotpat.dk`: dependent
  products in declarations, `_` wildcard patterns, empty rule contexts, numeric
  symbol names, grouped rules) in addition to the vendored hand-written
  `tests/fixtures/nat.dk` and the inline `tests/parse.rs` suite. (Upstream test
  files are *not* vendored, to avoid carrying third-party licences; `nat.dk` is
  original to this repo.)

## Deferred features (north stars) — reader scope

- **`.dk` module system / `#REQUIRE` resolution.** The reader parses one source
  string into one [`Signature`]; `#REQUIRE other.` is recorded as a
  [`Command`](src/entry.rs) but **not resolved** — there is no cross-file loader
  (the `covalence-metamath` `SourceResolver` analogue). A multi-module loader
  that resolves `#REQUIRE` and qualifies imported names is a north star.

- **Scope resolution.** A [`Term::Ref`](src/term.rs) is deliberately
  *unresolved*: a bare identifier is the same node whether it is a λ-bound
  variable, a rewrite-rule context (pattern) variable, or a global constant.
  Resolving references against binders + the signature (and the locally-nameless
  / de-Bruijn conversion the kernel wants) is deferred to the consumer.

- **Dot/guard patterns are syntactic only.** `{ t }` on a rule LHS parses to
  [`Term::Bracket`](src/term.rs) but carries **no matching semantics** here
  (Dedukti treats it as a convertibility-checked subterm). Interpreting it
  belongs with the type/rewrite layer below.

- **Richer error locations.** [`DkError`](src/error.rs) carries byte offsets but
  not line/column; a span→line/col renderer (and multi-error recovery) is a
  nicety, not yet implemented.

- **Canonical `.dk` serializer.** `Display` on [`Term`] round-trips terms, but
  there is no whole-[`Signature`] emitter / pretty-printer.

- **Symbol interning / scale.** [`Symbol`](src/term.rs) is an owned `SmolStr`
  with no interning or arena; fine for current inputs, a memory/throughput north
  star for very large exports (Logipedia-scale libraries).

## Deferred features (north stars) — semantics / the end goal

These are **not** in this crate (they need the kernel); they are the reason the
crate exists, recorded here so the trajectory is discoverable. They will be
implemented in `covalence-hol` (paralleling `metalogic/mm_*`) and tracked in its
registry once started.

- **λΠ-calculus-modulo type checker.** A checker for the parsed signature:
  scope resolution → conversion modulo the user rewrite rules (WHNF/SNF
  normalisation, higher-order/Miller pattern matching, and AC/ACU matching for
  `defac`/`defacu` symbols) → bidirectional type checking of `def`/`thm` bodies
  against their declared types. This is the HOL-free "sanity check" analogue of
  `covalence-metamath`'s RPN verifier; it can live here (behind a feature) or in
  the bridge.

- **HOL internalisation of Dedukti signatures + derivations.** The analogue of
  `metalogic::mm_database`/`mm_import`: realise a `.dk` signature as a
  first-class object in HOL and each well-typed derivation as a genuine
  `⊢ Derivable_…` theorem — the `Derivable_L` correspondence for the
  λΠ-modulo framework rather than for Metamath substitution.

- **Cross-theory metatheorems (the end goal).** With signatures + derivations
  internalised, exhibit translations *between encodings* — e.g. a sufficiently
  strong MLTT encoding and a sufficiently strong set-theory encoding — as a
  **single syntactic metatheorem** in HOL (theory transport / interpretation),
  the way `metalogic::relations` transports between Metamath-style logics. This
  is what makes "metatheory on internalised Dedukti derivations" concrete.

## Notes

- No `unsafe` (project rule).
- The crate is **parse-only today**: it does not type-check or rewrite. A `.dk`
  source is assumed already checked by Dedukti; this crate gives a faithful,
  queryable syntactic image to build the semantics layers on.
