# Skeletons — covalence-acset

## Minor

- **Only Δ (pullback) migration.** `Instance::pullback` implements the pullback
  functor `Δ_F` (objects, morphisms, and mapped attributes). The left/right
  adjoints **Σ_F / Π_F** (left/right Kan extensions) are not implemented — they
  are colimit/limit-based and were deliberately deferred rather than shipped
  half-right.
- **Compile-time names only.** Objects/morphisms/attributes are `&'static str`,
  so schemas are static. Dynamic / runtime-loaded schemas would need owned
  names.
- **Conjunctive queries only; no Datalog completeness.** `query` supports
  conjunctions of morphism/attribute atoms (answers = homomorphisms), evaluated
  by naive backtracking with forced-join candidate pruning. No negation,
  aggregation, disjunction, recursion (fixpoints), or projection/distinct; no
  query planner or indexing.
- **No (co)limits or schema composition.** Acyclicity is an instance-level check
  the caller invokes, not a schema law; no schema colimits / pushouts.
