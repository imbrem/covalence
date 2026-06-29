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
- **Query/Datalog evaluation is naive; positive only.** `query` (conjunctive)
  and `datalog` (recursive, least-fixpoint over derived relations) both evaluate
  by naive backtracking — no **semi-naive** delta evaluation, no indexing/planner.
  `datalog` is **positive** (no negation/stratification), set-valued only (no
  semilattice/aggregation values), and assumes rule monotonicity rather than
  checking it. The Datafun surface that would enforce monotonicity and add these
  is sketched in `notes/sketches/acset-datalog-datafun.md`.
- **No (co)limits or schema composition.** Acyclicity is an instance-level check
  the caller invokes, not a schema law; no schema colimits / pushouts.
