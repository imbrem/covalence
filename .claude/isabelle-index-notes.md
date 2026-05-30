# Isabelle Index Refactoring Notes

## Summary

Refactored `covalence-isabelle` from Arc-based to index-based design, matching `covalence-hol`'s pattern:
- `TypId(u32)`, `TermId(u32)`, `ThmId(u32)` lightweight Copy handles
- `PureArena` with `Vec<TypDef>`, `Vec<TermDef>`, `Vec<ThmDef>`
- Clone-on-read pattern: `get_*` methods clone small defs to avoid borrow conflicts
- Trait associated types are now `Copy` (was `Clone`)
- Constructors take `&mut self` (was `&self` with Arc)
- Change detection via `id == original_id` instead of `Arc::ptr_eq`

## Improvements Applied to Isabelle (that HOL could also benefit from)

1. **De Bruijn eliminates alpha-equivalence machinery** — Isabelle's `terms_eq` is just structural comparison, no need for HOL's `aconv` + environment stack. HOL could use de Bruijn internally to simplify.

2. **Simpler `free_in` check** — With de Bruijn, checking if a free variable occurs is just recursive pattern matching. No bound-variable shadowing to track.

3. **Trait methods take `Copy` values by value** — Cleaner signatures like `fn mk_app(&mut self, f: Self::Term, x: Self::Term)` instead of passing references to 4-byte handles. HOL's traits already do this but could be more consistent.

4. **Arena exposed via accessor** — `PureKernel::arena()` / `arena_mut()` allows external code (like HOL bootstrap) to allocate directly when building complex terms, avoiding round-trips through trait methods. HOL could benefit from this for its `HolKernel`.

## Potential Future Improvements (for both crates)

1. **Hash-consing** — Dedup at insertion time so that structurally equal types/terms get the same ID. Would make `types_eq`/`terms_eq` O(1) by just comparing indices. Significant complexity cost but huge perf win for large proofs.

2. **Cached type_of** — Store the computed type alongside each term (or in a parallel vec) to make `type_of` O(1) read-only. Currently the Abs case requires allocation.

3. **Interned sorts** — Sorts (`Vec<NameId>`) are small but heap-allocated inside `TypDef`. Could intern them in a separate table if they become a bottleneck.
