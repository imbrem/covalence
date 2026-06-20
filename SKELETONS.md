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

- **The `rat` quotient + ordered-field theory** in
  `crates/covalence-hol/src/init/rat.rs`. `rat := (int × int.pos) / ~`
  (cross-multiplication). Proved outright: `rat_rel_refl`, `rat_rel_symm`
  (pure `int`-equation `refl`/`sym`); `of_nat_via_int` (the ℕ↪ℚ
  embedding factors through ℤ↪ℚ, by β); and `add_comm` / `mul_comm` —
  proved **on the nose**, exactly as `init::int`'s are: `ratAdd`/`ratMul`
  are componentwise on representatives, so the two representative pairs are
  provably equal (numerator + denominator each by the proved `int`
  commutativity facts) and equal representatives lift to equal classes by
  congruence under `mkRat`. `rat_rel_trans` is now **proved too** — the
  Grothendieck cross-multiplication cancellation argument — *modulo* two
  **postulated `int` facts** (stubbed in `init::rat` via `axiom`, **to be
  relocated to / discharged in `init::int`**, now that the `int` ordered ring
  is fully proved both are derivable: cancellation from `lt_mul_pos` +
  `lt_trichotomy`, nonzero-positivity from the `int.pos` carving predicate):
  - `int_mul_rcancel` — `∀x y d. ¬(d = 0) ⟹ x·d = y·d ⟹ x = y` (`int` is an
    integral domain; right-cancellation by a nonzero factor).
  - `int_pos_nonzero` — `∀p:int.pos. ¬(rep p = 0)` (positive denominators
    are nonzero).

  So `rat_rel` is now a full equivalence and `quotient::class_intro` /
  `recon` are available for the remaining `rat` axioms.
  The **quotient-lifting machinery is now built** (the rat analogue of
  int's): `rat_recon` (quotient induction), `round_trip`, `recon_mk` (MK
  component form `MK(f,d) = mk_rat(pair f d)`, `f:int`, `d:int.pos`), the
  per-op computation rules `add_class`/`mul_class` + `add_mk`/`mul_mk` +
  `*_via_components`, the well-definedness lemmas `add_pair_cong` (distrib +
  interchange) / `mul_pair_cong` (interchange), `rel_of_pairs` (prod-
  projection bridge), and `imul_interchange`. It rests on two postulated
  `int.pos` round-trips for the `to_pos` denominators (**to discharge in
  `init::int`**): `pos_prod_rt` (`rep(to_pos(rep a · rep b)) = rep a · rep b`)
  and `one_pos_rt` (`rep(one_pos) = 1`).

  **Proved** through that machinery (over the operations `rat_zero`/`rat_one`/
  `rat_add`/`rat_sub`/`rat_neg`/`rat_mul`/`rat_inv`/`rat_div`/`rat_lt`, all
  defined at the representative level): the full additive group + commutative
  monoid fragment plus distributivity — the **full commutative ring**:
  `add_comm`, `mul_comm` (on the nose), `add_assoc`, `add_zero`, `add_neg`,
  `mul_assoc`, `mul_one`, `mul_zero`, `distrib` — and the order `lt_irrefl`
  (on the nose from `int::lt_irrefl`). All genuine *modulo* the `int.pos`
  round-trip + `rat_rel_trans` int stubs. `distrib` is the one *non*-
  componentwise ring axiom (`a·(b+c) = N/D` while `a·b + a·c = (rda·N)/(rda·D)`,
  the same rational scaled by the common factor `rda`), so its
  cross-multiplication collapses to comm/assoc and lifts by `class_intro`.

  **Still postulated** via the module's `axiom` helper:
  - The field inverse `mul_inv` (`¬(a=0) ⟹ ∃b. a·b = 1`), realisable via
    the defined `rat_inv` (sign-normalised so the denominator stays positive).
  - The order axioms `lt_trans`/`lt_trichotomy`/`le_def`/`zero_lt_one`.
    `le_def` is definitional (pins the opaque `ratLe`); the rest unfold
    `ratLt` to the `int` comparison on cross-products. The `int` ordered
    ring is **now fully proved** (`lt_*`/`lt_mul_pos` all discharged), so the
    `int` order facts these lean on are all available; the remaining work is
    the rat-quotient lifting. (The linear-order toolkit
    `le_refl`/`lt_imp_le`/`le_trans`/`lt_asymm`/`lt_imp_ne`/`le_antisym`/
    `le_total`/`not_one_le_zero` is **not** postulated — it is *derived* from
    `le_def` + the strict-order facts.)
  - The two **mediant inequalities** `mediant_gt` / `mediant_lt` — the
    only postulated leaves of `dense` (which is itself *derived* from
    them via the mediant `(a+c)/(b+d)`, no division needed). Each unfolds
    to an `int` order fact (`a·d < c·b ⟹ a·(b+d) < (a+c)·b`, etc.)
    lifted through the quotient — now unblocked (the `int` order theory it
    needs is fully proved); the remaining work is the rat-quotient lifting.

- **The `real` Dedekind-cut theory** in
  `crates/covalence-hol/src/init/real.rs`. `real := close rat ratLe`
  (upper cuts) — **shell-defined**: the `real` `TypeSpec` lives in
  `init::real` (`real_spec`/`real_ty`), *not* in the kernel catalogue
  (`covalence-core`), since the reals are not needed for the kernel's
  float substrate (rationals suffice). It is an ordinary derived `close`
  spec, so the kernel's witness-free subtype laws apply with no kernel
  support. **Proved with no postulates**: the `realLe` partial-order
  laws `le_refl` / `le_trans` / `le_antisym` — `realLe` is reverse inclusion
  of cut-sets, so reflexivity/transitivity are pure logic and antisymmetry
  is pure subtype structure (mutual inclusion ⟹ pointwise-equal cut-sets by
  function extensionality ⟹ equal reals by the round-trip
  `Thm::spec_abs_rep`); none touch the `rat`/order postulates. **Proved
  *modulo* the `rat` order postulates** they consume: `is_cut` (every
  principal up-set `ratLe q` is a genuine cut, from the `rat` `≤` toolkit),
  `of_rat_mono` (the principal-cut embedding is monotone, by `rat::le_trans`
  + the round-trip), and `zero_ne_one` (`⊢ ¬(0 = 1)`, via distinct principal
  cuts transported through the subtype `rep`/`abs`).
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
  strictly-positive, directly-recursive). **In place:**
  - `sig.rs` — the signature data model (`InductiveSig` / `Constructor` / `Arg`).
  - `data.rs` — the `Inductive` **trait**, the lifting seam: the engine
    consumes structural induction **and constructor freeness** (`injective` /
    `distinct`) only through it, never calling a kernel rule directly. `nat`'s
    `NatTheory` adapter sources them from `Thm::nat_induct` / `Thm::succ_inj` /
    `Thm::zero_ne_succ`.
  - `graph.rs` — the impredicative recursion graph (`closed` / `graph` /
    `ctor_instance`), generic over a signature.
  - `existence.rs` — `graph_intro` (per-constructor introduction) and
    `graph_total` (`⊢ ∀t. ∃a. Graph t a`, by the supplied induction). Generic
    over `Inductive`; `nat` consumes them (`init/recursion.rs`).
  - `uniqueness.rs` — `graph_inv` (per-constructor inversion: `Graph (Cᵢ x⃗) a
    ⟹ ∃b⃗. (⋀ Graph rⱼ bⱼ) ∧ a = fᵢ x⃗ b⃗`), via the generic `Good = λk c.
    Graph k c ∧ wit` determinizing relation whose closedness is discharged by
    `distinct` (other constructors) and `injective` (`Cᵢ` itself). Generic over
    `Inductive`; `nat`'s `graph_base_inv` consumes it.
  - `determinacy.rs` — `graph_det` (`∀t a b. Graph t a ⟹ Graph t b ⟹ a = b`):
    folds the supplied induction over `graph_inv` (invert both graphs, then the
    IH equates the recursive images). Generic over `Inductive`; `nat`'s
    `graph_det` consumes it.
  - `recursor.rs` — `recursion_theorem` (`⊢ ∃rec. P_rec rec`): builds the
    recursor `λ(steps). λt. ε a. Graph t a` by Hilbert choice over the graph,
    proves its per-constructor equations (`rec (Cᵢ x⃗) = fᵢ x⃗ (rec r⃗)`) from
    totality + determinacy, and `∃`-introduces over a caller-supplied `defs`
    recursor predicate. Generic over `Inductive`; `nat`'s `recursion_theorem` /
    `rec_holds_proof` consume it.
  - `util.rs` — shared conjunction-proof plumbing.

  The construction is **complete**: `init/recursion.rs` is now just the
  `NatTheory` adapter + assembly wiring, consuming the engine end to end.
  Remaining engine work:
  - **Port the engine onto the abstract `Hol` interface** (`inductive/hol.rs`),
    so the same machinery drives any HOL backend (native today; internal /
    object-level HOL later — "prove induction inside HOL"). `Hol` is the
    value-typed HOL Light surface (assoc `Type`/`Term`/`Thm` + connective
    builders + the derived rule set), distinct from the arena-style
    `HolLightKernel`. The pattern is **generic impl + native shim**: each
    function's logic moves to a generic-over-`Hol` version, with the concrete
    engine function a thin [`NativeHol`] shim so callers are unchanged.
    **Done:** the `Hol` trait covers the **full proof-layer surface** — types,
    term builders, queries, the rule set, and the hard derived rules (`beta_nf`,
    `exists_intro`/`exists_elim`, `rw_all`) as trait methods; the easy derived
    rules (`cong_arg`/`conjuncts`/`beta_reduce`/`beta_expand`/`beta_nf_concl`/
    `beta_nf_expand`/`rewrite`) and the conjunction plumbing as generic helpers.
    `NativeHol` forwards each to the existing `covalence-core` / `init::eq` /
    `init::logic` impl; the surface is validated generically (the `hol` tests).
    Also done: the **data model** (`sig`: `GenArg<Ty>`/`GenConstructor<Tm,Ty>`/
    `GenSig<Tm,Ty>` with native aliases `Arg`/`Constructor`/`InductiveSig`),
    the **`graph` term builders** (`gen_app2`/`gen_ctor_instance`/`gen_closed`/
    `gen_graph` + `GenCtorInstance<Tm>`, bare names are `NativeHol` shims), and
    the **`Inductive` trait** (now `Inductive<H: Hol = NativeHol>` — the default
    type param keeps `NatTheory`'s impl and the proof modules' `I: Inductive`
    bounds unchanged). `util` + `graph::conj` + `graph::{graph,closed,…}` are
    shims. **Still concrete (next):** the proof modules `existence` /
    `uniqueness` / `determinacy` / `recursor` — each ports to
    `<H: Hol, I: Inductive<H>>(hol, …)` using the `gen_*` graph builders + the
    `Hol` rule methods + the generic β/∃ helpers, with a `NativeHol` shim
    keeping its `nat`-facing signature. Then `recursion.rs`'s entry points can
    flip to any backend.
  - **The multi-recursive-argument / multi-constructor-argument paths** in
    `existence.rs`, `uniqueness.rs`, `determinacy.rs`, and `recursor.rs`
    (conjunctive IHs / antecedents, componentwise injectivity, nested
    `∃`-witnessing) are partial: `existence` / `uniqueness` handle the general
    shape but are only *exercised* by `nat`'s ≤1-arg / ≤1-rec-arg cases, while
    `determinacy::det_case` and `recursor::rec_equation` explicitly **error** on
    a constructor with ≥2 recursive arguments. A binary-tree or `list`
    signature is the first real test. The strict
    `wit`-binder naming discipline (`_wx_` / `_wb_` prefixes, disjoint from a
    constructor's own binders) is load-bearing — see the `uniqueness.rs` docs.

  **Lifting to internal HOL (future).** The trait seam exists precisely so the
  proofs can be re-targeted: today `nat` is a kernel primitive, but we may later
  define `nat` from `ind` the standard HOL way (`0`/`SUC` carved out of an
  infinite type via `NUM_REP`), where induction and freeness are **derived
  theorems**. That presentation supplies the same `Inductive` interface and so
  drives the same engine — lifting these proofs into internal HOL becomes
  writing one new `Inductive` impl, not re-deriving the graph route. Keeping
  every engine entry point generic over `I: Inductive` (never a concrete `nat`)
  is the standing constraint that keeps this open.

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

- **`covalence-hol` ring rewriter** in
  `crates/covalence-hol/src/ring/normalize.rs` (`RingNormalizer` / `RingOps`).
  **In place:** a general `(+, ·, 0, 1)` normalizer to a canonical
  **sum-of-monomials** form, built on the AC tactic (`crate::ac`). Decides
  distributivity (left + the *derived* right), `+`/`·` associativity +
  commutativity, and the `0`/`1` identities — so two expressions equal as
  *formal* polynomials over their atoms get `⊢ e₁ = e₂` (tested over `nat` and
  `int`). Every step is a kernel-checked equality. **Deferred:**
  - **coefficient collection** — like monomials are *not* combined: `x + x`
    stays `x + x` (not folded to `2·x`), and `x·y + y·x` stays two summands
    (not `2·(x·y)`). Needs literal-coefficient arithmetic on monomials and a
    "merge equal monomials" pass over the sorted sum.
  - **negation / subtraction** — `neg` / `sub` are treated as opaque atoms,
    not expanded through the `Ring` (`add_neg` / `sub_def`) axioms; an
    expression mentioning them normalizes only down to its `+`/`·` structure.
  - **literal folding inside monomials** (e.g. `2·3·x → 6·x`).
  The rewriter is currently a HOL-`Term`/`Thm` instance (`RingOps` over a
  catalogue carrier); a fully `Semiring`/`Ring`-trait-generic version (so it
  runs against any model, not just the shallow HOL one) is a later step.

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

## Proof-script layer (`covalence-hol/src/script`)

The S-expression authoring + replay layer (`Env`/prelude, the `infer`
type-inference elaborator, the `check` replayer + derivation registry, the
`rw`/`tauto` rules, and the `cov_theory!` loader macro). The
**parse → replay** direction is built and tested; `init::logic`'s `truth`/`and_comm`/`or_comm` (and the reified
`exists.intro`, with the Rust `exists_intro` rule rewired onto it) are now
**loaded from `init/logic.cov`** via `cov_theory!` (replacing the hand-written Rust proofs — the whole crate's
~225 tests still pass, since everything downstream of `truth()` re-checks).
`run(src, resolver)` resolves `(open NAME)` against caller-supplied envs and
returns a `Theory` whose **export** env — built explicitly by `(export NAME …)`
directives — is `open`-able by other scripts; the macro binds it as a
`static ENV: LazyLock<Env>`. These are deliberately deferred:

- **Inference is best-effort (untrusted).** `infer.rs` does Hindley–Milner
  unification for free-variable and binder-domain types; it is not complete
  and need not be sound — `check` re-validates every elaborated term against
  the kernel. Known partials: the `ε`/`select` result type is approximated;
  generalisation of leftover metavariables names type vars positionally
  (`'a`, `'b`, …), so a conclusion and proof that independently generalise
  must coincide in order (fine for the single-tvar cases today). `all-intro` /
  `abs-rule` still take an **explicit** binder type — their var isn't
  usage-constrained across the independently-elaborated sub-proof terms;
  inferring it would need either threading one metavar arena through the whole
  derivation or a check-time `find_free_type` pass.
- **Lemma application + `rw` unify (first-order); the pluggable unifier is not
  built.** `apply` (a dual-mode inference) instantiates a lemma by first-order
  matching its conclusion against the goal/target (`Env::apply_unify`), and `rw`
  instantiates a quantified `∀x⃗. L = R` by matching `L` against a subterm of the
  target (`Env::rw_unify` → `script/unify.rs::find_match`), so neither needs a
  hand-written `all-elim` prefix; bare lemma names (`(N w…)`) replaced the old
  `lemma` keyword. `rw` takes several equations
  (`(rw E1 E2 …)` / `(rw E… TARGET)`), applied in sequence; bare atom names work
  (`(rw sub_zero)`). Still TODO: (a) the unifier is hard-coded — a **registerable
  custom handler** (the stated motivation for routing through `Env` methods) is
  not wired; (b) a third inference facet **`rewrite(a) -> ⊢ a = b`** (a
  *rewriter*, what `rw` consumes — a lemma casts to one via `rw_unify`) is not a
  first-class kind yet; (c) the matcher is purely first-order (no higher-order
  patterns); (d) `rw` matches the FIRST (leftmost-outermost) subterm — no
  "rewrite at occurrence-N" control yet.

- **No proof/`Term` pretty-printer (serialization-out).** `script` only
  *parses* the named syntax and *replays* it; there is no printer from a
  proof / `Term` back to the surface S-expression. This blocks content-addressing
  (hashing a proof term) and lemma-by-hash references — both noted as
  future in `docs/surface-syntax.md` §7. Authoring (the immediate goal —
  porting the Rust `init/` theorems) needs only the parse direction. When
  added, reuse/extend the low-level printers in `crates/covalence-hol/src/sexp.rs`
  and the hasher in `hash.rs` (which today cover terms/types but **not** proofs).
- **`rw` does not descend under binders.** `rewrite_conv` in `script/drv.rs`
  rewrites through `App` and at leaves but returns `refl` for `Abs`, so it
  cannot rewrite inside `λ`/`∀`/`∃` bodies. Adequate for the quantifier-free
  goals it targets now; going under binders needs de-Bruijn-aware shifting of
  the equation.
- **Prelude `Env::core()` covers only logic + nat.** The name→catalogue
  resolvers are a starting set (the connectives, `=`, `nat.add/mul/sub/le/lt`,
  `succ`). int/rat/real/list/option/prod/coprod/set catalogue names are not yet
  bound; add entries to `script/env.rs::Env::core` (the `defs/` churn
  boundary) as those theories are ported.
- **Async core: types + tokio in place; the open-obligation (hole) feature was
  removed, pending a channel-based rebuild.** `script/mod.rs::run_async` is
  `async`; `run`/`resolve_blocking` block via a tokio **current-thread** runtime
  (`block_on`). `run` returns a `TheoryHandle` (in-progress) and
  `TheoryHandle::resolve` (async) forces it to a `Theory` (resolved) — but with
  no obligations, every `#thm` is checked inline (eagerly) and `resolve` is
  trivial, so the in-progress/resolved split is currently only nominal. The
  earlier `#hole`/`#fill` machinery (pending theorems, `splice_holes`,
  `collect_holes`, the manual `prove`/`poll_once` drive, `obligations`/
  `is_resolved`, `UnresolvedObligation`) was **deleted** — it was the wrong
  shape and is to be rebuilt cleanly. Target rebuild:
  - **Env channels + holes-as-yields.** A top-level `(#channel NAME)`
    declaration adds a **channel** to the environment; `(#fill NAME DRV)`
    **pushes** to it; `(#hole NAME)` in a proof **receives** from it. Because a
    future cannot mutate the env, the channel is the async-safe bridge: when
    `prove()` hits an unfilled hole it awaits the channel → genuinely **yields**.
  - **`ThmHandle` + manual poll.** `prove()` returns a future; `poll_once` it
    (one poll, noop waker — single-threaded, no spawn); if it **completes**
    store the `Thm`, if it **yields** stash a `ThmHandle = Ready(Thm) |
    Pending(future)` and move on, driving it later at force. Parallelism stays
    an explicit opt-in (`tokio::spawn` / multi-thread runtime), not the default.
    (`covalence_core::Error` + `ScriptError` are now `Clone`, so a `Pending`
    handle can be a multi-consumer `Shared` future.)
  - **`EnvHandle` (in-progress env).** Mirror of `TheoryHandle`: a fully-resolved
    `Env` holds no futures, but an in-progress one's **imported** lemmas/consts
    ARE futures (an import need not be fully proved to start proving importers);
    `EnvHandle::resolve().await -> Env`, `#import` resolver returns `EnvHandle`s,
    `#dep` becomes a real `await`. A failed import yields a *partial* theory
    that is still importable (wanted for BLAKE3-range partial verification).
- **`(#dep NAME)` is a synchronous availability guard, not an await.**
  `script/mod.rs` accepts `(#dep NAME)` and errors if `NAME` is not already a
  known lemma/const/tactic/import. Its real semantics — *force the enclosing
  task to block until `NAME` completes* (forward references included) — depend
  on the cooperative scheduler above.
- **`ScriptError` is flat strings — no source spans or traces.** Errors carry
  only a message (e.g. the cycle error stringifies theorem names; kernel errors
  wrap `covalence_core::Error`). Eventually the error type should carry **source
  extents** (byte/line spans, threaded from parsing) and **traces** — the chain
  of rules/tactics/obligations that led to a failure. **Very important for
  LLM-assisted proofs**, where the model needs precise, localized, structured
  feedback to repair a proof. Pairs with the typed-pipeline note below (extents
  come from preserving spans through every stage).
- **Typed `Stmt` exists for directives, but the pipeline + extents don't.**
  `run_async` now parses every directive into a typed `Stmt` enum (`parse_stmt`)
  in a first pass, then executes — but `#thm` bodies are still raw `SExpr`
  (typed elaboration of the proof is deferred), and **no source extents** are
  carried. The full pipeline — **parse → untyped elaboration → typechecking →
  typed elaboration → execution**, with a typed term/proof IR and spans threaded
  through every stage — is still TODO. The spans are the prerequisite for the
  rich, well-located errors above and good editor/LSP feedback.
- **Async tactics + async `check` + a uniform derivation registry all exist.**
  `Tactic` is an `#[async_trait]` trait (`apply` async; `Interp::run`/`prove`/
  `run_thm` async; recursing tactics are structs, goal-closers stay sync `fn`s
  via the blanket). `drv.rs::check` is **async** (returns `BoxFuture`); both
  tactic-mode and tree-mode (`#proof`) can **await mid-proof** (tests
  `async_tactic_can_yield_mid_proof`, `registry_rule_in_tree_mode_can_await`).
  There is no separate `Rule` trait: `Tactic` has **two** async methods —
  `apply` (tactic mode) and `rule` (tree mode), each defaulting to a "wrong
  mode" error — so ONE registered object serves either/both. `check` dispatches
  **every** `#proof` head through `Env::lookup_rule` (alias of `lookup_tactic`)
  and calls `.rule()`; `drv.rs::core_rules()` installs the ~30 forward rules
  into `Env::core` (override only `rule`), and dual-mode `refl`/`sym`/`not-intro`/
  `rw` (+ `tauto` in logic) are single structs overriding both. The old
  hardcoded `Drv` AST + `parse_drv` pass are gone — `Tactic::rule(&[SExpr], &mut
  CheckCtx)` **self-parses** its term/type/name/sub-derivation args (a
  `CheckCtx` gives `term`/`ty`/`name`/`push_var`/`check`), so a custom rule has
  the same power as a built-in. No remaining TODO for this item.
- **Lemma lookup is async; const lookup is sync (the data model is ready, the
  accessor + elaborator aren't).** `Env` is now ONE unified `entries:
  LazyMap<Entry>` (`Entry` = `Const|Lemma|Tactic`), so EVERY kind is already
  future-capable — a const *can* pend, no new machinery needed.
  **`Env::lookup_lemma` is `async`** (awaits a still-`#spawn`-ing
  `Entry::Lemma`); the old boundary-await `lemma_refs`/`await_computed_deps` was
  deleted. `#spawn` binds NAME via `define_spawned` → `insert_pending`; a later
  reference (or the force) just awaits it. The remaining half of **"all env
  accesses async"** (user) is now just the *accessor*: `lookup_const`/
  `lookup_tactic`/`lookup_rule` are still SYNC `get_ready` peeks. Making
  `lookup_const` async makes the **elaborator (`infer.rs`) async** (recursive
  `BoxFuture` + const-lookup await) → `parse_term`/`CheckCtx::term`/
  `elaborate_concl` async — that's the unbuilt step for *one async task per
  definition* (a `const` loaded from the network, like `#spawn` for a theorem).
  The non-async `lemma_ready(name)` peek stays for the sync `Theory::lemma` macro
  accessor (a forced theory's lemmas are all Ready).
  - **`#spawn` replaced `#compute`.** A `#spawn`ed proof is a *deferred
    cooperative async task* (a pending `BoxFuture` stored via `insert_pending`,
    polled when first awaited) — **no `spawn_blocking`, no nested `block_on`**.
    Because it shares the cooperative runtime, a `#spawn` CAN `await` a *prior*
    sibling lemma (the env clone structurally shares its pending `Shared`
    futures). Still snapshot-scoped, so it cannot see siblings declared *after*
    it. **Genuinely blocking work is deferred to the FFI tactic's own
    responsibility** (an FFI call that must block should manage that itself) —
    the script layer no longer owns a blocking-thread pool.
- **`Term` futures (term-level holes) not represented.** Terms are eagerly
  built — there is no `Term` future (and proof holes were removed, see above).
  A key target use case: represent a **unification hole** as a term future
  (optionally asserting a fixed type up front), letting the elaborator explore
  unification variants and resolve holes lazily — and, with content-addressing,
  fetch a term's contents on demand. Needs a future-carrying `Term`/elaborator
  value wired into `script/infer.rs`.
- **No WASM/WIT kernel API.** The longer-term goal of authoring proofs in WASM
  guests and importing them through a WIT kernel interface (driving the proof
  replay path across the component boundary) is not started. `check` is
  intentionally the single kernel-coupled entry point such an interface would
  sit behind.
