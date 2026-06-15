# Skeletons

Authoritative registry of intentional placeholders in the repo: empty/stub
modules, removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and tests that are commented out, `#[ignore]`d, or
deleted "for later".

See `CLAUDE.md` § Skeletons for the rules: **add an entry whenever you leave a
skeleton; delete the entry when you fill one in.** Keep this list complete —
it is how unfinished work stays discoverable.

## Empty / stub modules

- **`crates/covalence-kernel/src/facts.rs`** — empty module. The *observer*
  layer that records and content-addresses proven `covalence-hol` theorems
  will land here as the HOL-on-store stack comes online. See the
  `covalence-kernel` crate-root docs and `docs/roadmap.md`.

## Postulates pending proof

- **The `int` ordered-ring theory** in
  `crates/covalence-hol/src/init/int.rs` is **mostly postulated** via the
  module's `axiom` helper (`Thm::assume`, each carrying its statement as a
  self-hyp). `add_comm` and `mul_comm` are now **proved** (the op-unfolding
  + representative-rewrite pattern below; both commute *on the nose* as the
  ops are componentwise `nat` add/mul on representatives); 15 postulates
  remain: the commutative-ring axioms (`add_assoc`, `add_zero`, `add_neg`,
  `mul_assoc`, `mul_one`, `mul_zero`, `distrib`, `sub_def`), the linear
  order (`lt_irrefl`,
  `lt_trans`, `lt_trichotomy`, `le_def`), ordered-ring compatibility
  (`lt_add_mono`, `lt_mul_pos`), and discreteness (`lt_succ`:
  `a < b ⟺ a + 1 ≤ b`). Since `int := (nat × nat) / ~` (Grothendieck), each is
  a HOL theorem derivable from the `nat` Peano facts through the quotient;
  filling the proofs in does not change the public `fn` surface. These are
  the ingredients the Alethe `la_generic` / `la_mult_*` checker will consume.

  **Status: the lifting API now exists; applying it to `int` is the work.**
  The `nat` half is available and **fully proved** — `init::nat` proves
  `add_zero`/`add_succ_r`/`add_comm`/`add_assoc` by induction (the `induct`
  helper); `rec_holds` is now a genuine theorem (recursion theorem), so these
  carry no hypotheses. And `init::quotient` now provides the lifting machinery:
  `TypeSpec::quot` is a subtype of the powerset, so the kernel's subtype
  laws *do* apply (the "rejected" case is only for specs whose `tm` is a
  raw relation; `quot`'s `tm` is the `close` predicate). `quotient::class_intro`
  derives the **forward** law `Γ ⊢ rel a b → Γ ⊢ mkClass a = mkClass b`,
  the workhorse for proving `int` *equations*.

  Progress: `int_rel` is a **proven equivalence**
  (`init::int::int_rel_refl`/`_symm`/`_trans`); `quotient::class_intro`
  lifts `⊢ int_rel p q` to `mkClass p = mkClass q`; **`add_comm` and
  `mul_comm` are proved** (on the nose); and the **round-trip**
  (`quotient::round_trip`: `⊢ rel a (rep_class (mk_class a))`, via
  `close_pred_holds` + `spec_rep_abs_fwd` + `select_ax`) is **done and
  tested on the real `int_ty_spec`** — the keystone for the nested-op
  axioms.

  The path for the remaining ring-equation axioms (`add_assoc`, `add_neg`,
  `mul_assoc`, `distrib`):
  - Unfold both sides with `delta_all(int_add/int_mul)`; a *nested* op like
    `int.add a b` unfolds to `mk_int P_ab` (a *proper* class), and the
    outer op sees `rep_pair(mk_int P_ab)`.
  - `round_trip(P_ab)` + the β-bridge `mk_class p = mk_int p` (verified:
    `beta_nf(λx. int_rel p x) == defs class_of p`) give
    `int_rel (rep_pair(mk_int P_ab)) P_ab`, i.e. the chosen representative
    of `a+b` is `~` its componentwise pair.
  - `class_intro` on a `nat`-algebra combination of those `~`-facts closes
    the axiom.
  - ⚠️ **No quotient induction.** `a = mk_int(rep_pair a)` is *false* for a
    free `int` var: `quot` = `close` admits junk (unions of classes), so a
    free `a` need not be a single class. The axioms work because the *ops*
    always produce `mk_int` (proper) values — route the round-trip through
    those intermediates, never through the free variables.
  - 🛑 **`int` has junk → three axioms are currently *false*.**
    `close_predicate` is just `nonempty ∧ upward-closed`, and since
    `int_rel` is an equivalence, an upward-closed set may be a *union* of
    classes. So `Type::int()` contains junk like `abs(class 0 ∪ class 1)`,
    a valid-but-non-class element. For such `a`, `a + int.zero` normalises
    to a single class `≠ a`, so **`add_zero`, `mul_one`, `mul_zero` are not
    theorems** (they cannot be proved hypothesis-free; they must stay
    `Thm::assume` postulates). The *provable* ring axioms are the junk-safe
    ones: `add_comm`/`mul_comm` (done), `add_assoc`/`mul_assoc`/`distrib`
    (all-ops, true for junk), and `add_neg`/`sub_def` (the op result is
    always the proper `0`-class). **The proper fix is upstream**: make
    `defs/quotient.rs`'s `quot` junk-free — predicate `λS. ∃a. S = classOf
    a` (S is *exactly* one class), not "nonempty upward-closed". That also
    revalidates quotient induction. Until then, only the junk-safe axioms
    are dischargeable.
  - The `0`/`1` axioms (`add_zero`, `mul_one`, `mul_zero`, `sub_def` uses
    `neg`) additionally need **literal coherence**: relating `int_lit 0` /
    `int_lit 1` to their quotient representatives (`(0,0)` / `(1,0)`), a
    separate lemma.

  Older remaining-list (still accurate for the order axioms):
  - (a) the **β reconciliation** — `class_intro`'s `classOf a = λx. rel a x`
    vs `defs/int.rs`'s β-reduced `mk_int`;
  - (b) **unfold each `int` op** to its representative-pair body (δ + the
    quotient coercions), so an axiom like `add_comm` reduces to a `nat`
    fact lifted through `class_intro` — this discharges the 10 ring-equation
    postulates;
  - (c) the **converse** `mkClass a = mkClass b ⟹ rel a b` in
    `init::quotient` (recipe + η gotcha in that module's docs; needs
    `Thm::spec_rep_abs_fwd` + the `close`-predicate proof) — for the
    *order* axioms (the other 7);
  - still-needed `nat` facts for the *order/multiplicative* `int` axioms:
    `mul_succ_r` / `mul_comm` / `mul_assoc` / `distrib`, and the `le`/`lt`
    order facts. `init::nat` already has the additive theory, `add_cancel`,
    `add_interchange`, and `mul_zero`.

## Pending theorems

- **`nat.le` transitivity** in `crates/covalence-hol/src/init/nat.rs`.
  The order theory proves reflexivity, irreflexivity, successor
  cancellation, the zero facts, **totality** (`le_total`),
  **antisymmetry** (`le_antisym`), and the `<`/`≤` bridge
  (`lt_iff_succ_le`) — but **not** transitivity `∀a b c. a≤b → b≤c → a≤c`.
  It is a triple case-analysis: induct on the middle `b` (base `b = 0`
  closes by `le_zero_iff` + `le_zero`), and in the `S b'` step run
  `induct_forall2` over `(a, c)` — case `a = 0` closes by `le_zero`, case
  `c = 0` is vacuous (`S b' ≤ 0` is false), and `a = S a' ∧ c = S c'`
  cancels all three successors (`le_succ_succ`) and applies the
  outer induction hypothesis at `(a', c')`. Alternatively prove the
  additive characterisation `le_iff_add : (a ≤ b) = (∃k. a + k = b)` and
  get transitivity/antisymmetry uniformly from `+`.

## Partial subsystems

- **`covalence-alethe` rule coverage.** `HolAletheBridge` (in
  `crates/covalence-alethe/src/hol.rs`) checks the QF_UF core (`assume`,
  `resolution` / `th_resolution`, `refl`, `trans`, `symm`, `cong`,
  `equiv_pos2`, `false`), the propositional family (`equiv1`, `equiv2`,
  `implies`, `and`, `and_intro`, `not_not`, `evaluate`,
  `equiv_simplify`), the integer term layer (`Int`, literals,
  `+ - * < <= > >=`), and `hole` / rewrite re-derivation by
  `reduce`+`simp`. The following return `BridgeError::NotImplemented` (or
  `UnknownRule`) and still need wiring:
  - **`hole` beyond closed arithmetic / propositional.** The recompute
    hook (`hol.rs::hole` → `normalize`) discharges a hole whose two sides
    share a `reduce`+`simp` normal form — closed `int` arithmetic
    (`1+2=3`), literal `=`, connective identities (`¬true=false`). A hole
    needing *variable-level ring normalisation* (`x+1 = 1+x`, distributes
    `*`) has no shared normal form yet → reported. Needs proved `int`
    ring identities (`add_comm`/`assoc`/`mul_distrib`) from the Peano/int
    theory + a linear normaliser. Likewise disequality-reflexivity holes
    over uninterpreted terms.
  - **Linear-arithmetic core** — `la_generic`, `la_mult_pos`/`la_mult_neg`,
    `la_rw_eq`, `la_disequality`, `la_tautology`, `la_totality`. The LIA
    proper: Farkas certificates over rational coefficients. Blocked on the
    **ordered-ring theory of `int`** (`le`/`lt` transitivity, add-
    monotonicity, sign rules) that the `high-hol` Peano build-up is
    producing. This is the major remaining undertaking.
  - **Subproofs** — `anchor` and any `step` carrying `:discharge`
    (`subproof`, `bind`, `let`, …). The bridge rejects `:discharge`.
  - **The rest of the propositional rule family** — `equiv_pos1`,
    `equiv_neg1`/`equiv_neg2`, `and_pos`/`and_neg`, `or`/`or_pos`/`or_neg`,
    `implies_pos`/`implies_neg`, `contraction`, `tautology`, `ite*`, plus
    the equality lemmas `eq_reflexive`/`eq_transitive`/`eq_symmetric`/
    `eq_congruent`. Each is a `clause_intro` of an intuitionistic sequent,
    a `simp`/`tauto`, or a direct equality derivation — the
    `init/logic.rs` machinery is in place; they just need cases in
    `hol.rs::step` (cf. the `equiv1`/`implies`/`and` cases already there).
  - **Parametric sorts** (`declare-sort` arity > 0) — rejected with
    `ParametricSort`.

## Registry maintenance

- **`SKELETONS.md` itself is incomplete.** This file was created to fix the
  missing `facts` module and currently records only the `covalence-kernel`
  skeletons surfaced there. It still needs a full repo audit — empty/stub
  modules, `todo!()` / `unimplemented!()` / `NotImplemented` stubs, and
  disabled / deleted tests across all crates — to become the authoritative
  registry `CLAUDE.md` describes.

## Declaration-only catalogue ops (no definitional body yet)

These `covalence-core` `defs/` term-specs carry `tm = None`: they are **sound
and complete on literals** (reduced by `builtins.rs`) but have no open-form
definitional body, so nothing about them is provable by `unfold_term_spec`.
Each should become a `let_term!` / `spec_term!` definition (see
`docs/roadmap.md`). When you add a body, delete it here AND — if the body is
reducible — add it to the `audit_reduce.rs::audit_reduce_matches_body`
coupling guard.

- **`sN.shr` (arithmetic right shift), `crates/covalence-core/src/defs/int_ops.rs`**
  — `op_body` returns `None` for the *signed* `Shr`. Needs a floor-division
  (round toward −∞), which `int` does not yet expose (`int.div` truncates
  toward zero). The *unsigned* `uN.shr` and every other `uN`/`sN` op
  (add/sub/mul/neg/and/or/xor/not/lt/le/gt/ge/shl/div/rem) are now defined.
- **`nat` ops, `crates/covalence-core/src/defs/nat.rs`** — `natBitAnd/Or/Xor`,
  `natToBytesLe/Be`, `natFromBytesLe/Be` are `term_decl!`
  (declaration-only). (`natDiv` now carries a def-style Euclidean selector
  predicate; it is not let-style, so its `builtins` reduction is checked
  against the predicate by `nat_div_mod_satisfy_euclidean_law` rather than
  the unfold-based `audit_reduce_matches_body` coupling guard.)
- **`bytes` ops, `crates/covalence-core/src/defs/blob.rs`** — `bytesConsNat`,
  `bytesAt` are declaration-only (need a `nat ↔ u8` conversion).
- **Fixed-width conversions** (`toNat`/`toInt`/`fromNat`/`fromInt`/`zext`/
  `sext`, `int_ops.rs`) are **intentionally** declaration-only — the
  primitive reducible interface the ops above are built on, not a stub.

## Removed-pending-rewrite subsystems

- **`covalence-kernel` legacy prover** — the arena + e-graph + union-find
  prover kernel that used to live in `covalence-kernel` was removed in the
  kernel rewrite. What remains is the content-addressed store wiring
  (`backend.rs`, `store.rs`) plus the empty `facts` module above. Recover the
  old prover from the `backup/pre-hol-cleanup` branch if needed.
