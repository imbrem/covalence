# Skeletons — `covalence-init::init::acl2` (ACL2 soundness ladder)

Open work for the staged ACL2 embedding (`notes/vibes/lisp/acl2-full-plan.md`,
designs `notes/vibes/lisp/acl2-s0-s3-design.md` + `acl2-s4-s6-design.md` +
`acl2-s5-design.md`). S0–S4, **S6-structural**, and **S5a/S5b (ordinal
model + full-ε₀ well-foundedness)** complete: `defun.rs` admits user
defuns; the S6 env carries IND, the Hilbert axioms/compiler, and
`transport_equal_open`; `ordinal.rs` has `o-p`/`o<` as carrier functions
with ACL2's defining equations proved, the `ord_fold` ground normaliser,
`Acc` + its three rules, the `nat ↪ int` bridge (`init/int.rs`), and THE
S5 theorem `wf : ⊢ ∀x. ¬(op x = anil) ⟹ Acc x` for **all** CNF notations
(+ `main_ord`/`graded_wf`/`wf_induct`). Open: S5c/S5d (env integration +
IND-ORD), S7 (general measures). Parent index:
[`../SKELETONS.md`](../SKELETONS.md).

## Severe

- **S5c/S5d not started** (design §3, §7–§9, §11 G3–G4): the ordinal env
  rows (`install_user_rows` hand-row seam, `with_ordinals`, the seven
  `UserRow`s with `def_eq_model` = `ordinal.rs`'s proved defining
  equations pinned to `model_image` output), the S5 axiom pack (`cases` /
  `equal-mp` / `contra` / `truth` schema arms + `ModelImplies` typed-
  arithmetic rows), `transport_implies_open`, the **IND-ORD clause
  family** (`env.ind_ord`, `derive_ind_ord`, the §7.3 `wf_induct`-routed
  soundness discharge), and the G4 gate (`ACL2-COUNT` admission, its
  `O-P`/`O<` obligations in-object, app-assoc re-derived by measure).
  `wf`/`wf_induct` (proved) are the termination substrate S7 consumes.
- **S7 recursion tiers not started**: measured/mutual defuns via
  wf-recursion (design §10 recipe: `init/recursion.rs` graph method with
  `wf_induct` replacing `nat_induct`), deeper `car`/`cdr` descent,
  multi-formal structural recursion, `lambda` pseudo-terms (still outside
  eval/subst). The S4 admissibility template (consp-guarded single-formal
  depth-1 `(IF (CONSP xr) STEP BASE)`) is the whole recursive fragment.
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
