# Skeletons — `covalence-init::init` (theory catalogue)

Open placeholders for the `init/*` theories. See `CLAUDE.md` § Skeletons for the
rules, the [crate index](../../SKELETONS.md), and the [root
index](../../../../../../SKELETONS.md).

## `defs/` re-home bridge (toHOL purge, `init/twins.rs`)

Bridge built (S9a); the flip is maintainer-gated. See
[`notes/vibes/defs-rehome-design.md`](../../../../../../notes/vibes/defs-rehome-design.md).

- **Polymorphic let-style specs are not yet twinned** — `twins::unfold_spec`
  falls back to `unfold_term_spec` for them. Instantiate the cached base
  `spec_eq` via `inst_tfree` (tvar order) to cover the poly case; pure-derivation
  change, no new kernel surface.
- **Def-style (ε-selector) and declaration-only specs get no body-twin** —
  their re-home route (`const := ε pred` via `define` + `spec_ax`; opaque `Def`
  for `term_decl!`) is designed but not built.
- **`TypeSpec` re-home is prototype-only** — `twins::unit_typedef()` re-homes
  `unit` via `new_type_definition` and S9b re-proves its full fact set through
  that rep (`unit_rep_abs_t` / `unit_rep_is_t` / `unit_singleton`). The other
  subtype/newtype specs follow the same shape (need a non-emptiness witness);
  the **`int` quotient** needs a *quotient-typedef helper* over `⊢ equivalence R`
  (design in `defs-rehome-design.md` §e). No accessor is flipped onto a twin.

## Ball arithmetic — enclosure theorems (F4)

- **`ball.add` containment unproved** (`init/ball.rs`, F2c groundwork = data +
  evaluation only): `x ∈ X ∧ y ∈ Y ⟹ x + y ∈ ball.add X Y` needs a real-side
  ball-membership predicate plus IEEE rounding-error lemmas over the typed
  `f64` ops. The outward-rounding formula (module docs) is **provisional**
  until that proof pins it.

## Postulates pending proof

- **`rat` field/order leaves** (`init/rat.rs`, postulated via the `axiom` helper).
  Two remain:
  - `mul_inv` (`¬(a=0) ⟹ ∃b. a·b = 1`) — witness is `rat_inv`; blocked on the
    `int.sgn` positivity lemma `¬(z=0) ⟹ 0 < sgn z · z` (no `sgn`/`abs` lemmas in
    `init::int` yet). Lifts through the existing `mul` quotient machinery once it lands.
  - `le_def` — *definitional*: pins the meaning of the declaration-only kernel
    `ratLe` (`defs/rat.rs` ships `ratLe` with `tm: None`). To make it a real
    `delta`/`define` theorem, give `ratLe` a representative-level body in the
    catalogue (re-threads `real`, which consumes `ratLe`).
- **`real` Dedekind-cut suprema** (`init/real.rs`, postulated via `axiom`, NOT
  ported to `real.cov`): `sup_is_ub` / `sup_is_least` (the two LUB properties of
  `real_sup A`). Each unfolds to a set/order fact about cuts, blocked on the same
  `rat`/order theory. `complete` is *derived* from these two.

## `.cov` ports deferred

- **`rat.cov` operators stay `ConstDef::Op` givens (no inline `#def`).** Inlining
  any rat operator requires rebuilding the entire seam-given layer over the
  `term_spec` forms (strict structural equality + shared `to_pos` coercion +
  concl-parity tests block it). Pervasive `recon`/component-computation/`class_intro`
  rewrite; deferred.
- **`real.cov` non-order theorems** — `of_rat_mono`, `zero_ne_one`, `is_cut` are
  not ported (proved *modulo* the still-postulated `rat` order facts). Needs the
  extra cut seam + `rat` order givens; deferred until the `rat` order postulates
  are discharged.
- **`stream.cov` wrapper-side round-trips** — `head_mk`, `tail_const`, `mk_at`
  are genuine Rust theorems (`init/stream.rs`) but not re-derived in `stream.cov`
  (written against a diverged `ext` signature; re-port on the current 5-arg `ext`).
  `stream.cov` ports only `const.at`/`head.const`/`tail.at`.

## Partial subsystems

- **Inductive-type engine** (`init/inductive/`). Construction is complete; remaining:
  - **Port onto the abstract `Hol` interface** (`inductive/hol.rs`) so the same
    machinery drives any HOL backend (internal/object-level HOL later). Pattern:
    generic impl + `NativeHol` shim. Trait surface + data model + `graph` builders +
    `Inductive<H>` are ported; **still concrete:** the proof modules `existence` /
    `uniqueness` / `determinacy` / `recursor` — each ports to `<H: Hol, I: Inductive<H>>`
    using the `gen_*` builders + `Hol` methods + generic β/∃ helpers, with a `NativeHol`
    shim. Then `recursion.rs` entry points flip to any backend. Standing constraint:
    keep every engine entry point generic over `I: Inductive`, never a concrete `nat`
    (so internal-HOL `nat`-from-`ind` lifts to one new `Inductive` impl).
  - **Full ≥2-rec-arg run** — `det_step`/`rec_equation` are general for `k ≥ 1`, but a
    full `graph_total`/`graph_det`/`recursion_theorem` run on a fresh ≥2-rec-arg type
    still needs a genuine `Inductive` adapter (the carrier/`Wf` seam `#inductive` reports).

- **List theory** (`init/list.rs` + `list_recursion.rs` + `list.cov`). Missing:
  - **`list_foldl`** — the left-fold recursor's defining equations not yet discharged.
  - **`filter` / `flatten` clauses** — `foldr`-factored; follow the `length`/`cat`
    pattern but not built.
  - **Pointwise ops `map` / `take` / `skip` / `repeat`** — defined on the carrier
    stream (not via `foldr`); per-op `nil`/`cons` derivations not written.
  - **The `#inductive`-for-`list` path** — `script/inductive.rs` realises only the
    `nat` shape; polymorphic/multi-rec-arg `list` hits the engine gaps above.

- **Product theory** (`init/prod.rs`). Core complete. Not covered:
  - **`signed1` / `signed2`** (`defs/prod.rs`) — separate `TypeSpec`s; constructors/
    projections not built (mirror `prod`; only the spec handle differs).
  - **Reverse of `pair_inj`** + the packaged `⟺` form — not exposed.
  - **Product recursor / `prod.case`** (`(α→β→γ) → prod α β → γ`) — not in `defs/`.

- **Monoid / categorical rewriters** (`init/monoid.rs` + `cat.rs`). Not built:
  - **Relation-category rewriter** — `rel.compose`/`rel.id` exist but their identity
    & associativity laws are unproved; need the existential one-point rule (now proved
    in `logic::exists_one_point`) plus ∃/∧ reshaping (see lang entry). Once landed,
    `cat_normalize` generalizes to relations with no algorithm change.
  - **`(monoid-normalize)` / `(cat-normalize)` script inferences** — Rust normalizers
    not exposed as registered `.cov` rewriter tactics (first consumer of the planned
    `Tactic` rewriter facet, `script/tactic.rs`).
  - **List monoid `(list, append, nil)`** — laws proved in `list.cov`; remaining is
    packaging them as a `Monoid` *value* (`list_append_monoid()`).

- **Formal-languages / Kleene-algebra theory** (`init/lang.rs`). Not yet proved:
  - **`concat` associativity** + **`epsilon` identities** (`ε·L = L`, `L·ε = L`).
    The one-point rule is proved; what remains is an ∃/∧-normalizer (seed:
    `logic::exists_cong`) to reshape the concat membership into one-point form and
    apply monoid `left_id`. Once landed, these + `rel`'s identity/assoc fall out.
  - **`concat` over `union` distribution** — blocked on the same ∃-pushing.
  - **Full star unfolding** `L* = ε ∪ L·L*` (assemble the closure half into a single
    `⊆`) and the **least-fixpoint half** `L* ⊆ ε ∪ L·L*` (induction over the
    impredicative star).

- **Regex on lists / `Matches`** (`init/regex/`). Deferred:
  - **`Matches`-completeness** `mem w ⟦r⟧ ⟹ Matches r w` — star case needs the
    least-fixpoint half of the star unfolding above.
  - **`.cov` soundness** — needs the rule-induction `inst` of the impredicative
    predicate + slow `lang`-membership discharge; kept Rust-proved. The `regex.cov`
    star example also leaves `cat [0x61] nil` unreduced (separate unported step).
  - **Ambiguity** (`Parse r w` parse-tree datatype + `yield`) and **sexpr lift/lower**
    (`regex_of_sexpr` / `sexpr_of_regex`). Sketched in `regex.rs` DESIGN NOTE.
  - **Performance** — soundness proof is slow (~70s debug); the `star` impredicative
    `∀S` makes terms large. Memoised/staged `beta_nf` or caching `denote` would help.

- **Text theory** (`init/char.rs`, `string.rs`). Surface the list ops
  (`init/list_recursion.rs`) through the `bytes`/`string` newtype seam:
  - **Sequence `length`** (`bytes.len`/`string.len`) — bridge to `list.length`.
  - **`cat`/`at`/`index`/`slice`/`consNat`** for `bytes`/`string` — bridge to `list` ops.
    (`bytesConsNat`/`bytesAt` additionally need a `nat ↔ u8` conversion — see
    declaration-only ops.)
  - **Cons-side string/bytes induction & extensionality** — ride on list induction once landed.
  - **Literal coherence for non-empty `Blob`s** — needs cons-side `list.index`/`length`.
  - **Bitvector ops on `u8`/`bytes`** — width-respecting `and/or/xor/shl/shr/not`,
    `add`/`mul` mod `2^N`, `nat ↔ uN`/`bytes ↔ uN` conversions. Not started.

- **UTF-8 / UTF-16 codecs** (`init/utf8.rs` + `utf8.cov`, `init/utf16.rs`). Deferred:
  - **Validating decoders** `utf8Decode`/`utf16Decode` past the single ASCII byte —
    multi-byte continuation validation, over-long/lone-surrogate rejection, codepoint
    reassembly (large `nat`-range case analysis). `decodeAscii1` covers only the 1-byte case.
  - **Full string round-trip** `⊢ utf8Decode (utf8Encode s) = some s` (+ UTF-16) by
    `list-induct`: cons case needs a "decode peels one char's bytes off the front" lemma,
    resting on the per-byte validation above.
  - **`bytes`/`string` newtype-wrapped codec lemmas** — carrier-level lemmas proved,
    newtype-wrapped equational lemmas not all surfaced.

- **Reified object logic (S-expr → prop logic)** (`init/sexpr.rs` + `init/prop.rs`,
  `notes/vibes/metatheory.md` §8). Open:
  - **SURFACE GAPS (the `.cov` stress-test findings)** — next-language-feature drivers,
    none block the proofs (all live in Rust):
    1. **Impredicative `inst d := P` not expressible in `.cov`** — `prop_induction` has
       no script surface (building the predicate `P` + `Closed P` discharge are Rust-only).
       → a `(prop-induct P axiom-cases mp-case)` tactic is the missing primitive.
    2. **Statements over a *bound* formula variable can't be re-stated** — the
       reduced↔applied-constant β-bridge (`tree::to_applied`) only rewrites under closed
       sub-terms, so soundness/`derive_axiom_i`/`derive_mp` `#concl`s can't be written
       (only `consistency` can). → an automatic β/η-aware `#concl` matcher, or exposing
       `Derivable_Prop`/`denote` as genuine `defs` constants with a δ-rule.
    3. **Seam-given/applied-constant mismatch is pervasive** — `#concl` checker should
       β-normalise both sides before comparing (`comp_default`-style equality seam).
  - **`ToProp : HOLTm ⇀ PropForm`** (metatheory §8 step 4, first language morphism) — not built.
  - **Prop variables are `nat` indices, not `SExpr` atoms** — wiring `var` to carry an
    `SExpr` atom (formulas literally S-expressions) is a later unification.

- **`tree` / `sexp` theory** (`init/tree.rs`, `sexp.rs`). Still deferred: `branch_inj`
  (rank-1 subtree-recovery wall — the inductive-API bundles report it honestly as
  `BackendCaps::rec_injective = false`; an exact-type backend is the route); the
  recursor `rec_leaf`/`rec_branch` `.cov` ports (blocked on polymorphic-result-type `'r`
  instantiation in the proof language — the TFree-clash `cat`/`coprod` document); and the
  `tree-induct`/`sexp-induct` script tactics. `tree.rs` is not yet a wrapper over the
  `ImpredicativeBackend` bundle (`Wf` induction is available by realizing a `tree` spec,
  but the module's own API doesn't surface it).

- **Inductive-types API backends** (`init/inductive/{api,church,engine}.rs`, over
  `covalence-inductive`). Open:
  - **Engine backend is `nat`-only** — a generic `Inductive`-impl → bundle adapter (and a
    `list` instance) is deferred until a second carved consumer exists.
  - **`Hol` trait ↔ `LogicOps` unification** — `inductive/hol.rs`'s `Hol` should extend
    `covalence_inductive::LogicOps` instead of duplicating its surface (`api.rs` forwards
    method-by-method today).
  - **Primitive-recursion (paramorphism) `comp` variant** — the bundle contract is
    iteration-only; exact-type backends could additionally serve raw recursive arguments.
  - **`covalence-sexp` quotation helper** — surface `SExp` → `sexpr_theory()` constructor
    terms, next to the backend (the Lisp pole's data path).

- **λ_iter deep embedding** (`init/lambda_iter.rs` + `.cov`, `init/cv_recursion.rs`).
  Tarski-style nat-encoding documented; **proved**: course-of-values induction
  (`strong.below`/`strong.induct`) and the full course-of-values *recursion*
  theorem — uniqueness (`cv.unique`) + existence (`cv_recursion::cv_exists`,
  `⊢ Hext F ⟹ ∃f. ∀n. f n = F n f`, by bounded iteration) — plus the supporting
  function-valued `natRec` equations and `nat` order helpers. Deferred:
  - **Encoding functions** — injective pairing `⟨·,·⟩`/`π₁`/`π₂` + strict-decrease
    laws, constructor `tag` constants, and `WfTyCode`/`WfExCode`/`WfCtxCode` +
    `El_*`, now definable via `cv_exists` (course-of-values recursion on codes).
  - **Reified judgements** — `Typed : nat→nat→nat→bool` (least relation closed
    under coded Fig 2 rules) and `Checks` (derivation-code well-formedness).
  - **Metatheorems** — subtyping reflexivity/transitivity (type fragment, no
    binders — the natural first target), then weakening (2.1.1.2.1) and
    substitution (2.1.1.2.2), each by `strong.induct` on the derivation code.
  - SSA⇔λ_iter equivalence is out of scope here (deferred separately).

## `nat.thy` — carrier-generic model deferred

`init/nat.sig`+`nat.thy` (checked by `nat_thy.rs`) are the canonical `nat` spec;
`nat.cov` proves kernel-nat satisfies it via the self model. Deferred:

- **Carrier-generic model** — specs are stated over the self-model vocabulary (kernel
  `nat.add`/`natrec-op`/literals), so `nat.thy` is not yet signature-abstract (the abstract
  `tfree`-sort elaboration can't type nat literals + the `natrec-op` special form). Lift the
  full theory to a carrier-abstract presentation, giving `nat/self` as one model among others
  (reified-PA, bool-stream coding) via `#sig`/`#thy`/`#model`/`#models`.
- **Haskell-like surface extraction** — `nat.sig`/`nat.thy` are hand-written; they are the
  eventual elaboration target of the declarative surface language (`notes/vibes/surface-syntax.md`),
  not yet produced by it.
