# Skeletons — `covalence-init::init::acl2` (ACL2 soundness ladder)

Open work for the staged ACL2 embedding (`notes/vibes/lisp/acl2-full-plan.md`,
designs `notes/vibes/lisp/acl2-s0-s3-design.md` + `acl2-s4-s6-design.md` +
`acl2-s5-design.md`). S0–S4, **S6-structural**, and **all of S5** complete:
`defun.rs` admits user defuns; the S6 env carries IND, the Hilbert
axioms/compiler, and `transport_equal_open`; `ordinal.rs` has `o-p`/`o<`
as carrier functions with ACL2's defining equations proved, `ord_fold`,
`Acc`, the `nat ↪ int` bridge (`init/int.rs`), THE S5 theorem
`wf : ⊢ ∀x. ¬(op x = anil) ⟹ Acc x` for **all** CNF notations
(+ `main_ord`/`graded_wf`/`wf_induct`), `with_ordinals` /
`install_user_rows` (the seven ordinal rows as env `UserRow`s, pinned to
`model_image`), the S5 axiom pack (classical `cases` + `equal-mp` /
`contra` / `truth` + the `ModelImplies` typed-arithmetic rows),
`transport_implies_open`, and **S5d**: the IND-ORD clause family
(`Acl2Env::ind_ord` + `derive_ind_ord`, soundness by `wf_induct`) with
the G4 gate (`gate_s5d.rs`: `ACL2-COUNT` admitted + `NATP`/`O-P`/
`O<`-decrease obligations derived in-object + app-assoc by measure).
Open: S7 (general measured recursion). Parent index:
[`../SKELETONS.md`](../SKELETONS.md).

## Severe

- **Premise-builder P0 is PARTIAL** (agent stopped mid-task; binding design
  `notes/vibes/lisp/acl2-premise-builder.md`, handoff
  `notes/vibes/lisp/acl2-campaign-handoff.md`): hilbert.rs `Script`/`KCache`/
  `derive_under_cached` landed + tested; `simplify.rs` planner/emitter is an
  in-progress torso (compiles, NO gate tests, not wired); arith env rows
  (`with_arith_rules`), the P0 gates (app-assoc AUTO, len2-app, measured
  variant, negative controls), and docs not started.

- **S7 recursion tiers not started**: measured/mutual defuns via
  wf-recursion (design §10 recipe: `init/recursion.rs` graph method with
  `wf_induct` replacing `nat_induct`), deeper `car`/`cdr` descent,
  multi-formal structural recursion, `lambda` pseudo-terms (still outside
  eval/subst). The S4 admissibility template (consp-guarded single-formal
  depth-1 `(IF (CONSP xr) STEP BASE)`) is the whole recursive fragment.
  S5 hands S7 its complete substrate (design §10): `wf`/`wf_induct` +
  `install_user_rows` + `transport_implies_open` (obligation consumer)
  + the single-IH IND-ORD clause with its generic-in-`k` discharge —
  S7's defun-derived induction schemes register new `ind_ord` shapes and
  measured defuns enter through the hand-row seam with `def_eq_model`
  proved by wf-recursion; the G4 obligation scripts (`gate_s5d.rs`) are
  the per-defun obligation-discharge prototype.
- **`lang/lisp` is not on the S6 kernel path**: `crates/lang/lisp`'s
  `defthm` still uses its hypothesis-style dictionary over `ground_env`;
  wiring its surface `defthm`/induction onto `s6_env` + `derive_ind` +
  `hilbert::derive_under` is future work.

## Minor

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
- `ale` (`<=`) is *defined only*; `alt` (`<`) now has `lt_lit` +
  `alt_iff` (S5), but `times`/`neg` ground folds are still absent (same
  one-seam pattern as `plus_lit`). Lifted-axiom set is the demonstration
  pair (`plus_comm`/`plus_assoc`).
- `ordinal.rs` heads (`op`/`olt`/`natp`/`posp`/`ofe`/`ofc`/`ors`) fold
  only through `Ordinals::ord_fold`; `defun::fold_ground` errors on them
  (fails safe) — add head dispatch there if a later stage wants one
  entry point (design §2.3).
- `o<` order theory beyond wf (trans/irrefl/trichotomy on `o-p`s) and
  ordinal arithmetic (`o+`, `o*`) are out of scope until a book states
  them (design §13); the `=`/`eql` → `EQUAL` normalization deviation is
  recorded in design §1.1.
