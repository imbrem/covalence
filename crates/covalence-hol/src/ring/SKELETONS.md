# Skeletons — `covalence-hol/src/ring`

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../SKELETONS.md).

**Ring rewriter** (`normalize.rs` — `RingNormalizer` / `RingOps`).

**In place:** a general `(+, ·, 0, 1)` normalizer to a canonical
**sum-of-monomials** form, built on the AC tactic (`crate::ac`). Decides
distributivity (left + the *derived* right), `+`/`·` associativity +
commutativity, and the `0`/`1` identities — so two expressions equal as *formal*
polynomials over their atoms get `⊢ e₁ = e₂` (tested over `nat` and `int`). Every
step is a kernel-checked equality.

**Deferred:**

- **coefficient collection** — like monomials are *not* combined: `x + x` stays
  `x + x` (not folded to `2·x`), and `x·y + y·x` stays two summands (not
  `2·(x·y)`). Needs literal-coefficient arithmetic on monomials and a "merge
  equal monomials" pass over the sorted sum.
- **negation / subtraction** — `neg` / `sub` are treated as opaque atoms, not
  expanded through the `Ring` (`add_neg` / `sub_def`) axioms; an expression
  mentioning them normalizes only down to its `+`/`·` structure.
- **literal folding inside monomials** (e.g. `2·3·x → 6·x`).

The rewriter is currently a HOL-`Term`/`Thm` instance (`RingOps` over a catalogue
carrier); a fully `Semiring`/`Ring`-trait-generic version (so it runs against any
model, not just the shallow HOL one) is a later step.
