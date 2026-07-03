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
  `datalog` is **positive** (no negation/stratification) and set-valued; its
  rule language does not yet aggregate into a `JoinSemilattice` (only the
  standalone `lattice::lfp` does). The Datafun surface that would enforce
  monotonicity is sketched in `notes/vibes/sketches/acset-datalog-datafun.md`.
- **`lattice::lfp` assumes monotonicity + termination.** The step's monotonicity
  and the lattice's ascending-chain condition are the caller's obligation, not
  checked. `datalog::solve` is not yet *implemented* on top of `lfp` (only proven
  equal to it by a test).
- **No (co)limits or schema composition.** Acyclicity is an instance-level check
  the caller invokes, not a schema law; no schema colimits / pushouts.
