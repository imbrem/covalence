# Skeletons — `covalence-hol::init` (theory catalogue)

Open placeholders for the `init/*` theories. See `CLAUDE.md` § Skeletons for the
rules, the [crate index](../../SKELETONS.md), and the [root
index](../../../../SKELETONS.md).

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
  rewrite; deferred. Surface support (`spec-abs`/`spec-rep` in `infer.rs`) is done.
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

- **List theory** (`init/list.rs` + `list_recursion.rs` + `list.cov`). Foundation,
  recursion theorem, and append-monoid/length-homomorphism `.cov` laws are done. Missing:
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

- **Regex on lists / `Matches`** (`init/regex/`). Constructors, denotation, `Matches`,
  Rust soundness, and six `.cov` derivations are done. Deferred:
  - **`Matches`-completeness** `mem w ⟦r⟧ ⟹ Matches r w` — star case needs the
    least-fixpoint half of the star unfolding above.
  - **`.cov` soundness** — needs the rule-induction `inst` of the impredicative
    predicate + slow `lang`-membership discharge; kept Rust-proved. The `regex.cov`
    star example also leaves `cat [0x61] nil` unreduced (separate unported step).
  - **Ambiguity** (`Parse r w` parse-tree datatype + `yield`) and **sexpr lift/lower**
    (`regex_of_sexpr` / `sexpr_of_regex`). Sketched in `regex.rs` DESIGN NOTE.
  - **Performance** — soundness proof is slow (~70s debug); the `star` impredicative
    `∀S` makes terms large. Memoised/staged `beta_nf` or caching `denote` would help.

- **Text theory** (`init/char.rs`, `string.rs`). Element types + `nil`-side facts done.
  Missing — **all blocked on the in-flight `list` recursion (cons-side)**; do NOT build
  until `init::list` exposes the cons-side surface:
  - **Sequence `length`** (`bytes.len`/`string.len`) — blocked on `list.length`'s cons clause.
  - **`cat`/`at`/`index`/`slice`/`consNat`** for `bytes`/`string` — bridge to `list` ops.
    (`bytesConsNat`/`bytesAt` additionally need a `nat ↔ u8` conversion — see
    declaration-only ops.)
  - **Cons-side string/bytes induction & extensionality** — ride on list induction once landed.
  - **Literal coherence for non-empty `Blob`s** — needs cons-side `list.index`/`length`.
  - **Bitvector ops on `u8`/`bytes`** — width-respecting `and/or/xor/shl/shr/not`,
    `add`/`mul` mod `2^N`, `nat ↔ uN`/`bytes ↔ uN` conversions. Not started.

- **UTF-8 / UTF-16 codecs** (`init/utf8.rs` + `utf8.cov`, `init/utf16.rs`). Encoders +
  per-char round-trip + encoder homomorphism done. Deferred (do NOT claim done):
  - **Validating decoders** `utf8Decode`/`utf16Decode` past the single ASCII byte —
    multi-byte continuation validation, over-long/lone-surrogate rejection, codepoint
    reassembly (large `nat`-range case analysis). `decodeAscii1` covers only the 1-byte case.
  - **Full string round-trip** `⊢ utf8Decode (utf8Encode s) = some s` (+ UTF-16) by
    `list-induct`: cons case needs a "decode peels one char's bytes off the front" lemma,
    resting on the per-byte validation above.
  - **`bytes`/`string` newtype-wrapped codec lemmas** — carrier-level lemmas proved,
    newtype-wrapped equational lemmas not all surfaced.

- **Nat division / modulus theory** (`init/nat.rs`, `init/nat_div.{rs,cov,_facts.cov}`).
  The Euclidean facts are **proved** via the foundation-invariant `cv_exists`
  route and transferred to the `nat.div`/`nat.mod` selectors: `div.mul_le`
  (`(n/m)·m ≤ n`, all `m`), `div.mod` (`(n/m)·m + n mod m = n`, unconditional), and
  `mod.lt` (`m≠0 ⟹ n mod m < m`). Quotient uniqueness (`div.unique`),
  `(a·b)/b = a` (`div.mul_cancel`), the **division recurrence** as conditional
  equations (`div.lt`/`div.ge` + `nat.div.zero`), the iterated-division law
  `(a/b)/c = a/(b·c)` (`div.div`), and the **`shr` bridge** `shr a m = a/2^m`
  (`shr.eq_div_pow`) are done. Remaining:
  - **mod recurrence** — `n<m ⟹ n mod m = n` and `m≤n ⟹ n mod m = (n−m) mod m`
    (from `div.lt`/`div.ge` + `nat.mod.def`; the step needs `n−(m+x) = (n−m)−x`).
  - the `spec_ax` **seam itself** (`nat_div_spec`) — see the kernel `nat.div`
    redefinition skeleton in `covalence-core/SKELETONS.md`.
  - the `spec_ax` **seam itself** (`nat_div_spec`) disappears once `nat.div` is
    *defined* by the recursion — see the kernel `nat.div` redefinition skeleton in
    `covalence-core/SKELETONS.md`.

- **Reified object logic (S-expr → prop logic)** (`init/sexpr.rs` + `init/prop.rs`,
  `notes/metatheory.md` §8). Datatypes, recursors, soundness, rule induction, and the
  `prop.cov` surface are done. Open:
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
  - **Genuine `SExpr` structural induction** — `sexpr::induct_note` is a placeholder;
    the bare Church encoding admits junk inhabitants, so induction needs a `Wf`
    well-formedness predicate. Soundness doesn't need it; deferred.
  - **`ToProp : HOLTm ⇀ PropForm`** (metatheory §8 step 4, first language morphism) — not built.
  - **Prop variables are `nat` indices, not `SExpr` atoms** — wiring `var` to carry an
    `SExpr` atom (formulas literally S-expressions) is a later unification.

- **`tree` / `sexp` theory** (`init/tree.rs`, `sexp.rs`). Constructors, recursors,
  freeness/distinctness, and `.cov` surface done. Still deferred: `branch_inj`; the
  recursor `rec_leaf`/`rec_branch` `.cov` ports (blocked on polymorphic-result-type `'r`
  instantiation in the proof language — the TFree-clash `cat`/`coprod` document); and full
  structural `tree`/`sexp` induction (the `tree-induct`/`sexp-induct` tactic) — all need
  the recursor's subtree-recovery identity + the `Wf` carve `init/sexpr.rs` defers.

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
  eventual elaboration target of the declarative surface language (`notes/surface-syntax.md`),
  not yet produced by it.
