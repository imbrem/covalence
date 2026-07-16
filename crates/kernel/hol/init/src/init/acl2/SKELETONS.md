# Skeletons — `covalence-init::init::acl2` (ACL2 soundness ladder)

Open work for the staged ACL2 embedding (`notes/vibes/lisp/acl2-full-plan.md`,
design `notes/vibes/lisp/acl2-s0-s3-design.md`). S0 (the carrier,
`carrier.rs`), S1 (the primitives, `prims.rs`), S2 (deep terms + semantics,
`term.rs`, incl. `subst_sema`), and S3 **complete incl. soundness/transport**
(`ladder.rs` + `derivable.rs`: clause set, `Derivable_ACL2`, derivation
constructors, `soundness` by rule induction, `project_*`/`transport_equal`,
the `⊢ aplus (aint 2) (aint 2) = aint 4` gate). This unblocks S4 (defun as new
env clauses — `Acl2Env` + `discharge_closed` are the extension points), S5
(ordinals, independent), and S6 (induction clause + its discharge).
Parent index: [`../SKELETONS.md`](../SKELETONS.md).

## Severe

- **S4+ axiom-schema discharges**: `discharge_axiom` dispatches on the five
  S3 ground schema names only; any new `Acl2Env` axiom (per-defun defining
  equations, book axioms) makes `soundness` error until its own discharge is
  added (fails safe — no theorem minted).

## Minor

- `eval_open`/`evlis_open` cover the S2/S3 fragment (symbols, `aint`
  literals, quotes, `IF`, table applications; unknown heads/free vars stay
  symbolic via the `refl` fallback); `transport_equal` therefore transports
  **ground `EQUAL` forms only** — quantified/`IMPLIES` conclusions and
  `lambda` await S4/S6.
- `soundness(env)` is re-proved per call (29 clause discharges); callers
  projecting many derivations should prove it once and use `project_with`.
  If S4's per-defun clause growth makes this hot, switch to the cfg
  `family_soundness` packaging (the recorded escape hatch).
- `ladder.rs` is metalogic-shaped but ACL2-homed (that area is outside the
  current edit scope) — promote to `metalogic/` and migrate `peano/pa.rs` /
  `metalogic/toy.rs` onto it (their `br`/`bridge_eq`/`expand_to_pred` are
  per-instance copies).
- `derivable.rs::subst_ground`/`lsubst_ground` cover the ground fragment
  only (literal symbols/ints, quotes, literal-symbol heads) with a literal
  cond-chain σs (`finite_sigma`); arbitrary σs / open φ fall back to the raw
  `derive_inst` conclusion.

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
