# Skeletons — `covalence-hol::init` (theory catalogue)

Intentional placeholders for the `init/*` theories. See `CLAUDE.md` § Skeletons
for the rules, the [crate index](../../SKELETONS.md), and the [root
index](../../../../SKELETONS.md).

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

- **`covalence-hol` list theory** in `crates/covalence-hol/src/init/list.rs`
  + `list_recursion.rs` + `list.cov`. The **full structural foundation** is now
  proved and genuine (hypothesis- and oracle-free): the `abs`/`rep` seam, the
  finite-∧-contiguous selector facts (`pred_*`/`finite_*`/`contig_*`), the
  per-constructor element computations (`index_nil`/`index_cons_zero`/
  `index_cons_succ`/`head_nil`/`head_cons`/`tail_cons`/`index_tail`),
  constructor freeness (`cons_inj`/`nil_ne_cons`), extensionality (`list_ext`)
  + reconstruction (`cons_head_tail`/`nil_from_allnone`/…), and **list
  induction** (`list_induct`). On top, `list_recursion.rs` derives the `list`
  `Inductive` adapter, the paramorphic recursion theorem, the `list_foldr`
  discharge (`foldr_holds`), and the `foldr`/`length`/`cat` nil/cons recursion
  clauses (`foldr_nil`/`foldr_cons`, `length_nil`/`length_cons`,
  `cat_nil`/`cat_cons`). `list.cov` re-exports those clauses and proves the
  **append monoid laws** (`cat_nil_r`, `cat_assoc`) + the **length
  homomorphism** (`length_cat`) + `cat_cons_singleton` over the `listprim`
  seam env, driven by the new `list-induct` tactic (the genuine `list_induct`
  theorem, registered in `core`/`script::tactic`). Still missing:
  - **`list_foldl`** — the left-fold recursor's defining equations (the
    `foldr` mirror) are not yet discharged from the recursion theorem.
  - **`filter` / `flatten` clauses** — also `foldr`-factored, so their
    nil/cons clauses follow the `length`/`cat` pattern but are not built.
  - **Pointwise ops `map` / `take` / `skip` / `repeat`** — defined directly on
    the carrier stream (not via `foldr`); their `nil`/`cons` clauses need the
    `cons`-side *stream* computations applied to the pointwise body (the
    `index_cons_*` machinery is in place, but the per-op derivations are not
    written).
  - **The `#inductive`-for-`list` path** — `script/inductive.rs` realises only
    the `nat` shape; a polymorphic/multi-recursive-arg `list` declaration still
    hits the engine's ≥1-type-param + carrier-construction gaps (see the
    inductive-engine entry). The `list-induct` *tactic* + `list_env` givens are
    the current `.cov`-facing surface instead.

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

- **Monoid / categorical rewriters** in `crates/covalence-hol/src/init/monoid.rs`
  + `cat.rs` (`cat_normalize` / `cat_prove_eq`). **In place:** the model-generic
  monoid normalizer (`Monoid::normalize` / `prove_eq`) over `(op, unit, assoc,
  left_id, right_id)`; models for `(nat,+,0)`, `(nat,×,1)`, the endomorphism
  monoid `(α→α, ∘, id)`; the function-category rewriter for heterogeneous
  objects; and a model-generic `monoid.cov` driven through `monoid_env`.
  **Not yet built:**
  - **Relation-category rewriter.** `rel.compose` / `rel.id` exist in
    `defs/rel.rs` with `holds_compose` / `holds_id` (init/rel.rs), but their
    **identity and associativity laws are unproved** — they need the existential
    one-point rule `(∃y. x = y ∧ P y) = P x` (flagged in `init/rel.rs`'s module
    docs). Once those laws land, `endo_monoid` has a `rel`-category analogue and
    `cat_normalize` generalizes to relations with no algorithm change.
  - **`(monoid-normalize)` / `(cat-normalize)` script inferences.** The Rust
    normalizers are not yet exposed as registered `.cov` rewriter tactics; today
    a `.cov` proof drives the laws one `(rw …)` at a time (see `monoid.cov`).
    This is the concrete first consumer of the planned **rewriter facet** on the
    `Tactic` trait (`script/tactic.rs` doc-note): a `rewrite(a) -> ⊢ a = b`
    method so `Monoid::normalize` plugs in directly as `(rw (monoid-nf))`.
  - **List monoid `(list, append, nil)`.** The append monoid laws are now
    proved in `list.cov` (`cat_assoc`, the left unit `cat_nil`, the right unit
    `cat_nil_r`), so "list is the free monoid" is provable; what remains is
    packaging them as a `Monoid` *value* (`list_append_monoid()`) — i.e.
    re-exporting the `.cov` theorems through Rust accessors and feeding them to
    `Monoid::new`, the way `nat_add_monoid` / `endo_monoid` are built.
- **Formal-languages / Kleene-algebra theory** in
  `crates/covalence-hol/src/init/lang.rs`. A *language over a monoid `M`* is a
  `set` of `M`-carrier words; concatenation lifts `M`'s `op`. **In place:** the
  operations (`empty_lang`, `epsilon`, `lang_union`, `lang_concat`,
  `lang_star`); the membership computations (`mem_concat`, `mem_epsilon`,
  `mem_empty_lang`, `mem_star`); the **union** Kleene-algebra fragment
  (re-exported `set` `union_comm`/`union_assoc`/`union_idem`/`union_empty`);
  `∅`-annihilation `concat_empty_l`/`concat_empty_r` (proved via the new
  existential tactics); and `star_contains_epsilon` (`ε ⊆ L*`). All genuine
  (hypothesis- and oracle-free), model-generic over any `Monoid`. **Not yet
  proved:**
  - **`concat` associativity** and the **`epsilon` concat identities**
    (`ε·L = L`, `L·ε = L`). The **existential one-point rule**
    `⊢ (∃x. x = t ∧ P x) = P t` is now proved (`logic::exists_one_point`,
    `init/logic.rs`) — the rule also flagged as missing in `init/rel.rs`. What
    remains is **existential/conjunction reshaping**: the concat membership
    formula is `∃x ∃y. (x=unit ∧ mem y L) ∧ w=op x y`, which must be reassociated
    into the one-point shape `∃x. x=unit ∧ (∃y. …)` before the rule fires, and
    then `op unit y = y` (the monoid `left_id`) applied under the surviving `∃y`.
    A small ∃/∧-normalizer (the `logic::exists_cong` body-rewriter is the seed)
    is the next increment; once it lands, `ε·L = L`, `L·ε = L`, and `rel`'s
    identity/assoc laws all fall out.
  - **`concat` over `union` distribution** (`L·(M∪N) = L·M ∪ L·N` and the
    right form): the membership identity is a propositional tautology over the
    unfolded concat existentials, blocked on the same ∃-pushing.
  - **The full star unfolding** `L* = ε ∪ L·L*` and the **least-fixpoint
    half** (`L* ⊆ S` for any `Closed L S`): `star_contains_epsilon` gives the
    `ε ⊆ L*` part of the closure direction; the concat-closure `L·L* ⊆ L*`
    needs the one-point rule, and `L* ⊆ ε ∪ L·L*` is the genuine induction over
    the impredicative star.
  - **A regex datatype** (`empty | eps | lit a | alt | seq | star`) with a
    denotation `⟦·⟧` into `lang` (the `init/prop.rs` reified-object-logic
    pattern): not built — deferred until the concat/star laws above make the
    denotation's homomorphism theorems provable.

- **`covalence-hol` text theory** in `crates/covalence-hol/src/init/char.rs`
  and `crates/covalence-hol/src/init/string.rs` (`char`/`string`/`bytes`).
  The **element types and `nil`-side facts** are proved and genuine
  (hypothesis- and oracle-free):
  - `char := { c : nat | c < 0xD800 ∨ (0xDFFF < c ∧ c < 0x110000) }` — Unicode
    **scalar values** (surrogates excluded; matches Rust `char`). The codepoint
    round-trips `code_mk` (conditional on the scalar-value premise — decided per
    literal by `reduce` for the `nat.lt` atoms + `prop_eq` for the `∧`/`∨`;
    **rejects surrogates and out-of-range**) and `mk_code` (the unconditional
    wrapper-side round-trip).
  - `string := list char` / `bytes := list u8` — the newtype `abs`/`rep`
    seam, the empty-sequence builders/facts (`bytes_empty`/`string_empty`,
    `*_rep_empty`, `*_head_empty`).

  Still missing — **all blocked on the in-flight `list` recursion work**
  (the `cons`-side computations / list recursion theorem in the list-theory
  entry above); do NOT build until `init::list` exposes the `cons`-side
  surface:
  - **Sequence `length`** — `bytes.len`/`string.len` reduce to `list.length`
    through the seam; blocked on `list.length`'s `cons` clause (which is
    blocked on the list recursion theorem).
  - **`cat` / `at` / `index` / `slice` / `consNat`** for `bytes` and the
    analogues for `string` — each bridges to the corresponding `list` op,
    blocked on the same `cons`-side list computations. (`defs/blob.rs`'s
    `bytesCat`/`bytesLen`/`bytesSlice` already carry definitional bodies over
    `list.cat`/`list.length`/`take`∘`skip`; their open-form *equational
    lemmas* still wait on the list recursors. `bytesConsNat`/`bytesAt` are
    additionally declaration-only pending a `nat ↔ u8` conversion — see the
    "Declaration-only catalogue ops" section.)
  - **Cons-side string/bytes induction & extensionality** — ride directly on
    list induction/extensionality once those land.
  - **Literal coherence for non-empty `Blob`s** — a `Blob` literal of length
    `n>0` denotes `cons b₀ (cons b₁ … (nil u8))`; proving that equality
    needs the `cons`-side `list.index`/`length` clauses. The element-level
    coherence (`Blob : bytes`, `u8_lit : u8`, ASCII `char.mk k`) is done.
  - **UTF-8 and UTF-16 codecs** in `crates/covalence-hol/src/init/utf8.rs` +
    `utf8.cov` and `crates/covalence-hol/src/init/utf16.rs`. The **encoders +
    per-character round-trip + the encoder homomorphism** are now built and
    genuine (hypothesis- and oracle-free); the **validating decoders + full
    inductive string round-trip** are deferred. Done:
    - `utf8.encodeChar : char → list u8` (1–4 bytes by codepoint range, RFC
      3629) and `utf16.encodeChar : char → list u16` (BMP → 1 unit; astral →
      a **surrogate pair**, `0xD800+m/0x400` / `0xDC00+m%0x400` — the surrogate
      code units `char` excludes as scalars). Each is a shell-defined constant
      (`TermSpec` with a `SmolStr` symbol, not in the kernel `defs/`). The
      **per-character reduction lemmas** `encode_char_lit(k)` reduce a *literal*
      scalar value all the way to its exact `cons … nil` of `u8`/`u16` literals
      (tested across ASCII / 2-/3-/4-byte / `€` / emoji / all range boundaries
      / surrogate pairs). The driver is δ-unfold + β + the `char::code_mk`
      round-trip + `reduce` (folds `nat.div`/`mod`/`add` + `int.fromNat[uN]`) +
      `cond::collapse_conds` (a new public conversion firing the `init::cond`
      `cond_true`/`cond_false` clauses innermost-first).
    - `utf8.encode : string → bytes` / `utf16.encode : string → list u16`
      (and the carrier-level `utf8.encodeBytes : list char → list u8`), each a
      `foldr` of the per-char encodings. Their `nil`/`cons` recursion clauses
      (`encode_nil`/`encode_cons`/`encode_bytes_nil`/`encode_bytes_cons`) are
      proved through the `init::list_recursion` `foldr`/`cat` machinery.
    - the **per-character UTF-8 round-trip** `decode_ascii1_round_trip(k)`
      (`⊢ decodeAscii1 (utf8EncodeChar (char.mk k)) = some (char.mk k)`) for
      the **ASCII fragment** (`k < 0x80`), via the carrier-level decoder
      `utf8.decodeAscii1` + the new `init::option::case_some`/`case_none`
      `optionCase` clauses + `list::head_cons`.
    - the **encoder monoid homomorphism** `utf8.cov`'s `encode_cat`
      (`⊢ ∀xs ds. encodeBytes (xs ++ ds) = (encodeBytes xs) ++ (encodeBytes
      ds)`), proved by `list-induct` — the analogue of `list.cov`'s
      `length_cat`. (`text` types `char`/`string`/`bytes`/`uN` are now
      `.cov`-parseable, added to `script::syntax::parse_type`.)

    Deferred (do NOT claim these are done):
    - **The validating decoders** `utf8Decode : bytes → option string` and
      `utf16Decode : list u16 → option string` past the single ASCII byte:
      the multi-byte continuation-byte validation (`0x80 ≤ b < 0xC0` checks),
      the over-long-encoding / lone-surrogate rejection, and the codepoint
      reassembly (`((b0 & mask) << 6·k) + …`) are a large `nat`-range case
      analysis not yet built. `decodeAscii1` only covers the 1-byte case.
    - **The full string round-trip** `⊢ utf8Decode (utf8Encode s) = some s`
      (and the UTF-16 analogue) by `list-induct` over the string: the cons
      case needs a **"decode peels exactly one char's bytes off the front"**
      lemma (decode reads `encode_char c ++ rest` and returns `c` + `rest`),
      which rests on the per-byte decode validation above. The induction
      *skeleton* is the `encode_cat` homomorphism + the per-char round-trip;
      the prefix-consumption step is the remaining work.
    - **`bytes`/`string` newtype wrappers** for the codecs (`utf8Encode` is
      `abs ∘ encodeBytes ∘ rep`; a `utf8Decode` over `bytes`/`option string`
      wrapping `decodeAscii1`) — the carrier-level lemmas are proved, the
      newtype-wrapped equational lemmas are not all surfaced.
  - **Bitvector ops on `u8`/`bytes`** (the eventual full bitvector support):
    `u8`/`uN` are `bits`-subtypes (`defs/bits.rs`) and `defs/nat.rs` already
    has `natShl/Shr/BitAnd/BitOr/BitXor` that reduce on literals — the future
    bitvector layer would expose width-respecting `and/or/xor/shl/shr/not`,
    `add`/`mul` mod `2^N`, and `nat ↔ uN`/`bytes ↔ uN` (LE/BE) conversions on
    these types. Not started.


- **`covalence-hol` reified object logic (S-expr → propositional logic)** in
  `crates/covalence-hol/src/init/sexpr.rs` + `crates/covalence-hol/src/init/prop.rs`
  (the first internal object logic, `docs/metatheory.md` §8). Both datatypes use
  a **Church / impredicative encoding** over a fresh result type `'r` (not the
  `init/inductive/` carve-a-subtype engine), which keeps everything rank-1 and
  TCB-free. **Complete and genuine** (all theorems hypothesis- and oracle-free):
  - `sexpr.rs` — `SExpr := atom bytes | snil | scons` with constructors, the
    recursor `rec`, and its three per-constructor equations (`rec_atom` /
    `rec_snil` / `rec_scons`, proved by β). End-to-end length-fold test passes.
  - `prop.rs` — `PropForm` (`var nat | ¬ | ∧ | ∨ | ⟹`), the denotation
    `⟦·⟧ : PropForm → (nat→bool) → bool`, the impredicative Hilbert-system
    `Derivable_Prop A := ∀d. Closed d ⟹ d A` (10 axiom schemas + MP), the
    LCF-style derivation constructors `derive_axiom` / `derive_mp`, and the
    **soundness theorem** `⊢ ∀v. Derivable_Prop A ⟹ ⟦A⟧ v` (proved by
    instantiating `d := λA. ⟦A⟧ v` and discharging each closure clause via
    `prove_taut` = β-normalise + complete Shannon decision `prop_eq`).
  - Not yet here:
    - **A genuine `SExpr` structural induction principle.** `sexpr::induct_note`
      is a doc placeholder: the bare Church encoding admits junk inhabitants, so
      `(∀b. P(atom b)) ⟹ P snil ⟹ (∀h t. P h ⟹ P t ⟹ P(scons h t)) ⟹ ∀s. P s`
      needs a `Wf` well-formedness predicate carving the well-founded encodings
      (the standard "reducibility" side condition). Soundness does **not** need
      it — `Derivable_Prop` is itself impredicative — so it was deferred. The
      recursor universal property / `Wf`-restricted induction is the next step
      if a downstream proof needs to induct over arbitrary `SExpr`s.
    - **`ToProp : HOLTm ⇀ PropForm`** (metatheory §8 step 4, the first *language
      morphism* translating a HOL propositional fragment into the object logic
      with `⟦ToProp t⟧ = t`) is not built.
    - **Propositional variables are `nat` indices, not `SExpr` atoms.** The
      `SExpr` carrier and `PropForm` are independent today; wiring `var` to carry
      an `SExpr` atom (so formulas are literally S-expressions) is a later
      unification, deliberately skipped for simplicity.

