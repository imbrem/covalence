# Sketches

Forward-looking design sketches and raw research notes that feed the canonical
docs in `notes/vibes/` but aren't themselves load-bearing. Aspirational and informal —
when one of these graduates into a real plan, it moves up to `notes/vibes/` and its
sketch is deleted.

## Design sketches (forward-looking)

- [`covalence-ml-naive-compiler.md`](./covalence-ml-naive-compiler.md) — a
  maximally-naive SML→WASM compiler as the *silvered node* of the ML→WASM
  executor graph; mature compilers ride alongside as untrusted mirrors.
  (Deferred; revisit when an ML program needs the trusted pipeline.)

## Research notes (background / raw brainstorm)

- [`OBSERVERS.md`](./OBSERVERS.md) — the observer/validator/precondition
  substrate behind `notes/vibes/observers.md` (witness → observer → validator →
  facts).
- [`MAPS.md`](./MAPS.md) — theory-interpretation transport across PA/HOL/ZFC
  behind `notes/vibes/metatheory.md`'s two pillars.
- [`SAMPLE.md`](./SAMPLE.md) — sample surface syntax (`#tydecl`/`#decl`/
  `#clause` for `option`) and the spec-question forms (entailment, uniqueness,
  categoricity) for the surface-syntax direction.
