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
- **No query layer or (co)limits.** Pure instance machinery — no
  conjunctive-query / Datalog layer, no schema colimits, no schema composition.
  Acyclicity is an instance-level check the caller invokes, not a schema law.
