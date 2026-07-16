# Skeletons — `covalence-init::init::acl2` (ACL2 soundness ladder)

Open work for the staged ACL2 embedding (`notes/vibes/lisp/acl2-full-plan.md`,
design `notes/vibes/lisp/acl2-s0-s3-design.md`). S0 (the carrier,
`carrier.rs`), S1 (the primitives, `prims.rs`), and S2 (deep terms +
semantics, `term.rs`, incl. `subst_sema`) are complete. Parent index:
[`../SKELETONS.md`](../SKELETONS.md).

## Severe

- **S3 `ladder.rs`/`derivable.rs` not built** — unary `derive_mixed` twin +
  β-bridge helpers (generalize `peano/pa.rs`:455–:523 / `metalogic/toy.rs`:251,
  promotion target `metalogic/`), `Acl2Env` + clause set + `soundness` +
  `transport_equal`; gate `(+ 2 2) = 4` transported into base HOL.

## Minor

- **S2/S3 fragment boundaries** (`term.rs`, by design §5): `lambda` terms are
  not in the eval/subst fragment (S4's definitional principle); unknown heads
  evaluate to `anil` — the S3 clause set derives nothing about them.

- `alt` (`<`) and `ale` (`<=`, the not-`<` macro shape) are *defined only* —
  no computation/ordering laws yet (deferred per design §9: the S3 gate is
  `+`-only; lift `lt_trichotomy` etc. from `init/int.rs` when needed).
- Ground literal folding exists for `+` only (`Prims::plus_lit`); `times`/
  `neg`/`lt` analogues are the same one-seam pattern, add at S3 `derive_comp`.
- Lifted-axiom set is the design's demonstration pair (`plus_comm`/
  `plus_assoc`); `times_comm`, distributivity, etc. lift the same way on
  demand.
- `aappend` + its associativity (the S0 induction-gate theorem) live in
  `carrier.rs` *tests* only; promote to a module surface when S4's
  definitional principle lands (it will re-derive them via admission).
