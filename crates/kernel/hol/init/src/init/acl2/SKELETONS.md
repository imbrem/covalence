# Skeletons — `covalence-init::init::acl2` (ACL2 soundness ladder)

Open work for the staged ACL2 embedding (`notes/vibes/lisp/acl2-full-plan.md`,
design `notes/vibes/lisp/acl2-s0-s3-design.md`). S0 (the carrier,
`carrier.rs`) is complete. Parent index: [`../SKELETONS.md`](../SKELETONS.md).

## Severe

- **S1 `prims.rs` not built** — model primitives (`consp`/`atom-p`/`symbolp`/
  `integerp` as `A`-valued catamorphisms, `aequal`/`aif` via `cond`, arithmetic
  through `intval : A → int`) + ACL2 completion axioms proved + the lifted
  arithmetic set (`plus_comm` etc. from `init/int.rs` via `intval_int`). The
  carrier, recursor and `sym_ne` seam it needs are all landed in `carrier.rs`.
- **S2 `term.rs` not built** — metacircular pseudo-terms (terms *are* carrier
  values), pair-valued `ev`/`eval`/`evlis` + `subst`/`lsubst` paramorphisms,
  `subst_sema` (the hard lemma; case plan in the design §5).
- **S3 `ladder.rs`/`derivable.rs` not built** — unary `derive_mixed` twin +
  β-bridge helpers (generalize `peano/pa.rs`:455–:523 / `metalogic/toy.rs`:251,
  promotion target `metalogic/`), `Acl2Env` + clause set + `soundness` +
  `transport_equal`; gate `(+ 2 2) = 4` transported into base HOL.

## Minor

- `aappend` + its associativity (the S0 induction-gate theorem) live in
  `carrier.rs` *tests* only; promote to a module surface when S4's
  definitional principle lands (it will re-derive them via admission).
