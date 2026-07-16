# Verified I/O — parse/deparse as a certified pair over hashed dialects

> Status: **aspirational design note.** Frontier detail for §8 of
> [`../vision/development-vision.md`](../vision/development-vision.md). The goal:
> emit bytes/strings (MathML, DOT, …) *certified* to denote a specific internal
> object under a specific, hashed **dialect**, with proofs relating dialects.

## The idea

Covalence already turns untrusted bytes *into* kernel objects — Lisp
S-expressions, `.mm`, SpecTec, OpenTheory articles. The untrusted input drives a
kernel-checked construction, so a successful parse is a proof the bytes denote
the object. **Verified output is the dual**: given an internal object, emit bytes
that are *certified to parse back to it*. Parse and deparse become a verified
pair on raw bytes, and the thing that gives "denote" a precise meaning is the
**dialect**.

## Dialects (first-class, hashed)

A **dialect** is a mapping from a concrete syntax tree (the MathML tree, the DOT
AST, …) to a mathematical object. Different applications need different — and
sometimes mutually **incompatible** — dialects (how a `<mfrac>` maps to a term;
what a DOT `label` means). So a dialect is not hard-wired: it is a **first-class,
content-addressed object** with a hash `$DIALECT_HASH`. Objects likewise hash to
`$DEFINITION_HASH` (the same content-addressing as the base layer, vision §0).

The base certificate we want to mint is:

> **`Renders(bytes, $DEFINITION_HASH, $DIALECT_HASH)`** — parsing `bytes` as the
> dialect's concrete syntax and applying the dialect's interpretation yields
> exactly the object `$DEFINITION_HASH`.

i.e. a **MathML box tagged "verified to correspond to definition D under dialect
Δ"**. The tag is not decorative — it is backed by a kernel theorem.

## Proofs relating dialects

Because dialects are objects, we can state and prove **relationships between
them**: a translation `τ : Δ₁ → Δ₂` with `⊢ ∀o. render_{Δ₁}(o) ≈ render_{Δ₂}(o)`
(renderings agree, or agree up to a stated equivalence). Then a rendering is
**portable** across applications *with a proof*, not a hope — critical when
dialects proliferate and are individually incompatible.

## Round-trips

The parse/deparse pair should satisfy round-trip theorems where they hold:

- `parse_Δ (deparse_Δ o) = o` — deparse is a section of parse (always meaningful);
- `deparse_Δ (parse_Δ b) =_Δ b` — up to the dialect's byte-level equivalence
  (whitespace, ordering), where the concrete syntax is canonical.

A verified deparser is exactly a `deparse` with the first theorem attached.

## First targets

- **MathML** for equations/definitions: emit a fragment `Renders`-certified
  against a math dialect. Start narrow (a fixed fragment of MathML and a small
  dialect covering arithmetic/relations), widen later.
- **DOT / graphs**: a verified **parser + deparser** for DOT relating bytes to a
  **graph + metadata** (vision §3, `covalence-graph`). Round-trip theorems make a
  rendered diagram a *checked* view of an internal graph.
- **Lisp** already exercises the pattern in the small: parsing S-expressions
  *out* of their HOL representation is a deparse; the "parse out" tactic paired
  with the "parse in" tactic is a verified round-trip
  ([`../lisp/README.md`](../lisp/README.md),
  [`../../plans/sketch-separation.md`](../../plans/sketch-separation.md)).

## Scope guard

Stop at **structured text** (MathML, DOT, SVG-as-AST) for the foreseeable future.
Pixel-level rendering — proving what a rasteriser draws — is far-future and out of
scope. The value now is a trustworthy bytes-↔-object boundary, mediated by hashed
dialects, reusing the same content addressing and parsing-relation machinery as
the rest of the system.

## Related

Base-layer content addressing: [`../vision/development-vision.md`](../vision/development-vision.md) §0.
Parsing relations: [`../lisp/initial-ideas/parsing-relations.md`](../lisp/initial-ideas/parsing-relations.md)
and [`../lisp/initial-ideas/relational-parsing-framework.md`](../lisp/initial-ideas/relational-parsing-framework.md).
Bytestring encodings (shared with [`computation-theory.md`](./computation-theory.md)).
