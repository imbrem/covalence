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

- **`crates/covalence-hol/src/surface/`** — design sketch of the surface
  syntax (the "generalized Haskell" authoring layer, `docs/surface-syntax.md`).
  The AST (`surface::ast`), the `#`-builtin registry (`surface::Builtin`), and
  the parser (`surface::parse` / `parse_str`, pure S-expr → directive AST) are
  implemented, but the layers above remain stubs: the **elaborator** (surface
  → low-level S-expr → kernel object), the **`#by` tactic grammar** (proof
  steps are kept as raw `SExpr`s in `Proof::steps`), and **`#import` content
  addressing** (`#import` resolves names only; by-hash addressing is unbuilt)
  are all future work.

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
  The `int` semiring/ring embedding (`crate::semiring::Int` /
  `crate::ring::Int`) forwards its axioms here, so it inherits these
  postulates (and their self-hyp audit trail) until they are discharged; the
  `nat` semiring embedding (`crate::semiring::Nat`), by contrast, is fully
  proved.

  **Status: the lifting API now exists; applying it to `int` is the work.**
  The `nat` half is available and **fully proved** — `init::nat` proves
  `add_zero`/`add_succ_r`/`add_comm`/`add_assoc` by induction (the `induct`
  helper); `rec_holds` is now a genuine theorem (recursion theorem), so these
  carry no hypotheses. And `init::quotient` now provides the lifting machinery:
  `TypeSpec::quot` is a subtype of the powerset, so the kernel's subtype
  laws *do* apply (the "rejected" case is only for specs whose `tm` is a
  raw relation; `quot`'s `tm` is the image predicate `λS. ∃z. S =
  classOf z`). `quotient::class_intro`
  derives the **forward** law `Γ ⊢ rel a b → Γ ⊢ mkClass a = mkClass b`,
  the workhorse for proving `int` *equations*.

  Progress: `int_rel` is a **proven equivalence**
  (`init::int::int_rel_refl`/`_symm`/`_trans`); `quotient::class_intro`
  lifts `⊢ int_rel p q` to `mkClass p = mkClass q`; the **converse**
  `quotient::class_elim` lifts it back (`mkClass a = mkClass b ⟹ rel a b`,
  needs only `refl`); **`add_comm` and `mul_comm` are proved** (on the
  nose); and the **round-trip** (`quotient::round_trip`: `⊢ rel a
  (rep_class (mk_class a))`, via `quot_pred_holds` + `spec_rep_abs_fwd` +
  `select_ax`) is **done and tested on the real `int_ty_spec`** — the
  keystone for the nested-op axioms.

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
  - ✅ **`quot` is now junk-free** (`defs/quotient.rs`). The carving
    predicate is `λS. ∃z. S = classOf z` (S is *exactly* one class), **not**
    the old "nonempty ∧ upward-closed" (`= close ∘ symmetric-closure`),
    which admitted every *union* of classes — e.g. `abs(class 0 ∪ class 1)`.
    With that junk gone, `Type::int()` contains exactly one inhabitant per
    `int_rel`-class, so **quotient induction is valid** (`a =
    mk_int(rep_pair a)` for *every* `int`, not just op-results) and the
    three formerly-false axioms — **`add_zero`, `mul_one`, `mul_zero`** —
    are now genuine theorems. They remain `Thm::assume` postulates only
    because the *derivation* (quotient induction + literal coherence) is not
    yet wired; they are no longer unsound to claim. The keystones are all in
    place: `class_intro` (forward), `class_elim` (converse), `round_trip`
    (representative-in-class), and `quot_pred_holds` (every `classOf a` is a
    valid class).
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
  - (c) the **converse** `mkClass a = mkClass b ⟹ rel a b` — **done**:
    `init::quotient::class_elim` (needs `Thm::spec_rep_abs_fwd` +
    `quot_pred_holds` + `refl`). Available for the *order* axioms (the
    other 7); the work left there is applying it, not building it;
  - still-needed `nat` facts for the *order* `int` axioms: the `le`/`lt`
    order facts. The additive **and** multiplicative theory is now in place —
    `init::nat` proves the additive theory, `add_cancel`, `add_interchange`,
    and the full commutative-semiring multiplicative theory (`mul_succ_r`,
    `mul_one`, `mul_comm`, `mul_assoc`, `distrib`, `distrib_r`, `mul_zero`),
    consumed by the `nat` semiring embedding in `crate::semiring`. The `nat`
    `le`/`lt` order theory is now developed too — reflexivity, irreflexivity,
    successor cancellation, the zero facts, totality, antisymmetry, the
    `<`/`≤` bridge, and **transitivity** (`le_trans`).
- **The `rat` quotient + ordered-field theory** in
  `crates/covalence-hol/src/init/rat.rs`. `rat := (int × int.pos) / ~`
  (cross-multiplication). Proved outright: `rat_rel_refl`, `rat_rel_symm`
  (pure `int`-equation `refl`/`sym`); `of_nat_via_int` (the ℕ↪ℚ
  embedding factors through ℤ↪ℚ, by β); and `add_comm` / `mul_comm` —
  proved **on the nose**, exactly as `init::int`'s are: `ratAdd`/`ratMul`
  are componentwise on representatives, so the two representative pairs are
  provably equal (numerator + denominator each by the proved `int`
  commutativity facts) and equal representatives lift to equal classes by
  congruence under `mkRat`; no quotient relation and no `int` cancellation
  are involved. **Postulated** via the module's `axiom` helper (each
  carrying its statement as a self-hyp):
  - `rat_rel_trans` — transitivity of the cross-multiplication relation.
    Needs `int` *multiplicative cancellation by a positive* (cancel the
    common positive denominator), an `int` fact not yet discharged. Once
    that lands, this becomes the int-analogue of `int_rel_trans`.
  - The remaining ordered-field axioms over `rat_zero`/`rat_one`/`rat_add`/
    `rat_neg`/`rat_mul`/`rat_lt` (commutative-ring `add_assoc`/`add_zero`/
    `add_neg`/`mul_assoc`/`mul_one`/`mul_zero`/`distrib`, multiplicative
    inverse `mul_inv`, the linear order `lt_*`/`le_def`, and the base
    strictness fact `zero_lt_one` — `ratLt` picks ε-representatives, so
    `0 < 1` is not reducible). Each is a HOL theorem derivable from the
    `int` ordered-ring theory through the quotient; filling them in does
    not change the public `fn` surface. They depend transitively on the
    `int` postulates above. (The `≤` toolkit
    `le_refl`/`lt_imp_le`/`le_trans`/`not_one_le_zero` is **not**
    postulated — it is *derived* from `le_def` + the strict-order facts.)
  - The two **mediant inequalities** `mediant_gt` / `mediant_lt` — the
    only postulated leaves of `dense` (which is itself *derived* from
    them via the mediant `(a+c)/(b+d)`, no division needed). Each unfolds
    to an `int` order fact (`a·d < c·b ⟹ a·(b+d) < (a+c)·b`, etc.)
    lifted through the quotient — blocked on the same `int` order theory.

- **The `real` Dedekind-cut theory** in
  `crates/covalence-hol/src/init/real.rs`. `real := close rat ratLe`
  (upper cuts). **Proved**: `is_cut` (every principal up-set `ratLe q` is a
  genuine cut, from the `rat` `≤` toolkit) and `zero_ne_one` (`⊢ ¬(0 = 1)`,
  via distinct principal cuts transported through the subtype `rep`/`abs`).
  Both are genuine *modulo* the `rat` order postulates they consume.
  **Postulated** via the module's `axiom` helper (self-flagged):
  - `sup_is_ub` / `sup_is_least` — the two least-upper-bound properties of
    the supremum cut `real_sup A` (the intersection of the members'
    cut-sets). Each unfolds to a set/order fact about the cuts, blocked on
    the same `rat`/order theory. `complete` (the least-upper-bound property,
    "the reals are complete") is itself **derived** from these two, with
    `real_sup A` as the witness — the direct analogue of how `rat::dense`
    is derived from its mediant postulates.

## Partial subsystems

- **`covalence-hol` inductive-type engine** in
  `crates/covalence-hol/src/init/inductive/`. The shared infrastructure for
  basic inductive types (single-sorted, parametric, first-order,
  strictly-positive, directly-recursive). **Only the term layer is in place:**
  `sig.rs` is the signature data model (`InductiveSig` / `Constructor` /
  `Arg`), and `graph.rs` builds the impredicative recursion graph
  (`closed` / `graph`) generically from a signature. `nat`'s construction in
  `init/recursion.rs` consumes these builders (its `nat_sig`), which validates
  them. Still missing — the **proof layer**, currently hand-specialised to
  `nat` in `init/recursion.rs`:
  - **Generic per-constructor inversion lemmas** — the abstraction of
    `graph_base_inv` (nullary) and `graph_step_inv` (recursive) to an arbitrary
    constructor: `Graph (Cᵢ x⃗) a ⟹ ∃b⃗. (⋀ Graph rⱼ bⱼ) ∧ a = fᵢ x⃗ b⃗`, via the
    per-constructor "determinizing" / "good" instances (`det_zero` / `good`).
  - **Generic totality / determinacy** — fold the supplied induction principle
    over the inversion lemmas (the bodies of `graph_total` / `graph_det`), then
    ε-assemble (`recursion_theorem`) into `⊢ ∃rec. P_rec rec`.
  - **The two feeders** — the engine *consumes* an induction principle plus
    constructor freeness (injectivity + disjointness). For `nat` these are the
    kernel primitives (`nat_induct`, `succ_inj`, `zero_ne_succ`); for `list`
    they must be *derived* from the `stream (option α)` carrier (list induction
    is the blocker — see the list theory entry below).

- **`covalence-hol` list theory** in `crates/covalence-hol/src/init/list.rs`.
  Only the **`nil`-side computational foundation** is proved so far — the
  `abs`/`rep` seam (`rep_abs_finite`), the finiteness gate (`finite_const_none`,
  `finite_nonempty`), element-access unfolding (`index_unfold`), and the empty
  list facts (`index_nil`, `head_nil`). All are genuine (hypothesis- and
  oracle-free). Still missing:
  - **`cons`-side computations** — `index`/`head`/`tail` of `cons x xs`. Each
    needs `finite (cons-stream)`, a finiteness-*preservation* lemma that rests
    on `nat` **ordering** theory (`nat_le` successor/predecessor lemmas). That
    order theory is now developed in `init/nat.rs` (the `le`/`lt` foundation:
    `le_succ_succ`, `le_zero`, `zero_lt_succ`, `le_total`, `le_trans`, …), so
    `finite_cons` is unblocked; build it, then the `cons` element lemmas follow
    the `init::stream` `at_of` pattern.
  - **`tail_cons` / list extensionality / induction** — `tail (cons x xs) = xs`
    needs extensionality on the carrier stream (pointwise-equal ⟹ equal),
    re-discharging finiteness; list induction is the structural-recursion
    companion.
  - **Structural recursors `list_foldr` / `list_foldl`** — pinned by Hilbert-ε
    selector predicates (defined in `defs/list.rs`), so their defining equations
    (`fr f z nil = z`, `fr f z (cons x xs) = f x (fr f z xs)`, and the left-fold
    mirror) need a **list recursion theorem**. The target is to obtain it from
    the generic inductive engine (`init/inductive/`) once its proof layer is
    generalised and `list`'s induction principle + `cons`/`nil` freeness are
    derived to feed it — rather than re-deriving the `nat` graph route by hand.
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
