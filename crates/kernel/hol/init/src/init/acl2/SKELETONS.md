# Skeletons — `covalence-init::init::acl2` (ACL2 soundness ladder)

Open work for the staged ACL2 embedding (`notes/vibes/lisp/acl2-full-plan.md`,
designs `notes/vibes/lisp/acl2-s0-s3-design.md` + `acl2-s4-s6-design.md`).
S0–S4 **and S6-structural** complete: `defun.rs` admits user defuns; the
S6 env (`derivable::s6_env`) carries the IND structural-induction clause,
the `prop-k`/`prop-s` Hilbert axioms, the structural pack, the `CongImpl`
family, the `hilbert.rs` deduction compiler, and `transport_equal_open`
(gate: `⊢ ∀x y z. app (app x y) z = app x (app y z)` derived through the
object logic and transported). Open: S5 (ordinals), S7 (general
measures). Parent index: [`../SKELETONS.md`](../SKELETONS.md).

## Severe

- **S5/S7 recursion tiers not started**: ordinal measures, non-structural
  and mutual recursion, deeper `car`/`cdr` descent, multi-formal
  structural recursion, `lambda` pseudo-terms (still outside eval/subst).
  The S4 admissibility template (consp-guarded single-formal depth-1
  `(IF (CONSP xr) STEP BASE)`) is the whole recursive fragment.
- **`lang/lisp` is not on the S6 kernel path**: `crates/lang/lisp`'s
  `defthm` still uses its hypothesis-style dictionary over `ground_env`;
  wiring its surface `defthm`/induction onto `s6_env` + `derive_ind` +
  `hilbert::derive_under` is future work.

## Minor

- **Open transport is `EQUAL`-only** (`transport_equal_open`);
  IMPLIES-form open transport (conditional model theorems) deferred
  (design §15).
- **No classical propositional axiom** (NOT-elimination /
  transposition): the deduction compiler emits only K/S/MP and the gate
  proofs are positive — add as a `Schema` arm when a book needs it
  (design §7.2).
- **Deduction-compiler blowup is quadratic-ish** per discharged
  hypothesis (design risk register): fine at gate scale (~40 s for the
  app-assoc premises); derived-rule caching / lazier K-weakening before
  book-scale replay.
- Defthm-as-new-axiom feedback (admitting a transported theorem as a
  `ModelEq`/`ModelHolds` row for later derivations, design §5.3) is not
  built; derivation monotonicity across env generations likewise —
  re-derive per generation (soundness is cached per `Acl2Session`
  generation; the cfg `family_soundness` packaging stays the recorded
  escape hatch — the S6+APP env's 50-clause soundness runs ≈ 20 s).
- **S4 formal-name restriction**: formals may not be `b`/`h`/`t`/`sg` or
  start with `__` (induct binder hints / internal frees).
- **`defun::fold_ground` covers the S4 gate fragment only**: values,
  `CONS`, `BINARY-+` on int literals, user rows. `aif`-guard deciding,
  `times`/`neg`/`lt` folds, and `car`/`cdr`/`consp` on literals error
  (fails safe); add heads at the single match site on demand.
- `ladder.rs` is metalogic-shaped but ACL2-homed (that area is outside
  the current edit scope) — promote to `metalogic/` and migrate
  `peano/pa.rs` / `metalogic/toy.rs` onto it (their `br`/`bridge_eq`/
  `expand_to_pred` are per-instance copies).
- `derivable.rs::subst_ground`/`lsubst_ground` cover the ground fragment
  only (literal symbols/ints, quotes, literal-symbol heads) with a
  literal cond-chain σs (`finite_sigma`); arbitrary σs / open φ fall
  back to the raw `derive_inst` conclusion.
- `alt` (`<`) and `ale` (`<=`) are *defined only* — no
  computation/ordering laws yet (S3 design §9; lift `lt_trichotomy` etc.
  from `init/int.rs` when needed). Ground literal folding exists for `+`
  only (`Prims::plus_lit`); `times`/`neg`/`lt` analogues are the same
  one-seam pattern. Lifted-axiom set is the demonstration pair
  (`plus_comm`/`plus_assoc`).
