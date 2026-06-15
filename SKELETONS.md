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
  `crates/covalence-hol/src/init/int.rs` is **entirely postulated** via the
  module's `axiom` helper (`Thm::assume`, each carrying its statement as a
  self-hyp). Seventeen theorems: the commutative-ring axioms (`add_comm`,
  `add_assoc`, `add_zero`, `add_neg`, `mul_comm`, `mul_assoc`, `mul_one`,
  `mul_zero`, `distrib`, `sub_def`), the linear order (`lt_irrefl`,
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

  Progress: `int_rel` is now a **proven equivalence**
  (`init::int::int_rel_refl`/`_symm`/`_trans`, `trans` via
  `nat::add_interchange` + `nat::add_cancel`), and `quotient::class_intro`
  already lifts `⊢ int_rel p q` to `mkClass p = mkClass q` over the real
  `int_ty_spec` (tested). Remaining for `int`:
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
## Partial subsystems

- **`covalence-hol` list theory** in `crates/covalence-hol/src/init/list.rs`.
  Only the **`nil`-side computational foundation** is proved so far — the
  `abs`/`rep` seam (`rep_abs_finite`), the finiteness gate (`finite_const_none`,
  `finite_nonempty`), element-access unfolding (`index_unfold`), and the empty
  list facts (`index_nil`, `head_nil`). All are genuine (hypothesis- and
  oracle-free). Still missing:
  - **`cons`-side computations** — `index`/`head`/`tail` of `cons x xs`. Each
    needs `finite (cons-stream)`, a finiteness-*preservation* lemma that rests
    on `nat` **ordering** theory (`nat_le` successor/predecessor lemmas) not yet
    developed in `init/nat.rs` (which currently has only `add`/`mul` facts). Add
    the `nat_le` lemmas first, then `finite_cons`, then the `cons` element
    lemmas follow the `init::stream` `at_of` pattern.
  - **`tail_cons` / list extensionality / induction** — `tail (cons x xs) = xs`
    needs extensionality on the carrier stream (pointwise-equal ⟹ equal),
    re-discharging finiteness; list induction is the structural-recursion
    companion.
  - **Structural recursors `list_foldr` / `list_foldl`** — pinned by Hilbert-ε
    selector predicates (defined in `defs/list.rs`), so their defining equations
    (`fr f z nil = z`, `fr f z (cons x xs) = f x (fr f z xs)`, and the left-fold
    mirror) need a **list recursion theorem** — the analogue of
    `crate::init::recursion` for `nat` (graph construction → existence →
    uniqueness → assemble via ε). This is the major undertaking.
  - **Ops riding on the recursors** — `length`/`cat`/`filter`/`flatten`
    (factored through `foldr`) and the pointwise `map`/`take`/`skip`/`repeat`
    (need the `cons`-side stream computations). No `*_nil`/`*_cons` clauses for
    any of these yet.

- **`covalence-hol` product theory** in `crates/covalence-hol/src/init/prod.rs`.
  The core is **complete and genuine** (oracle-free): the `abs`/`rep` seam
  (`rep_pair`), both projection clauses (`fst_pair`/`snd_pair`), surjective
  pairing (`pair (fst p) (snd p) = p`), and pair injectivity (`pair_inj`).
  Not yet covered:
  - **`signed1` / `signed2`** (`defs/prod.rs`) are *separate* `TypeSpec`s reusing
    the same singleton `prod_predicate` over `prod bit α`. Their constructors /
    projections aren't built; once added they mirror `prod` exactly (the
    `singleton_pred` / `determines` engine is type-agnostic — only the spec
    handle differs).
  - **The reverse of `pair_inj`** (`a = c ∧ b = d ⟹ pair a b = pair c d`, trivial
    by congruence) and the packaged `⟺` form are not exposed.
  - **A product recursor / `prod.case`** (`(α → β → γ) → prod α β → γ`) is not in
    the `defs/` catalogue; surjective pairing + the projections are enough to
    define and reason about one downstream when needed.

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
- **`nat` ops, `crates/covalence-core/src/defs/nat.rs`** — `natDiv`,
  `natBitAnd/Or/Xor`, `natToBytesLe/Be`, `natFromBytesLe/Be` are
  `term_decl!` (declaration-only). `natDiv` in particular is *reducible*, so
  when it gets a body it must be added to the coupling guard.
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
