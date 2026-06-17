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
  congruence under `mkRat`; no quotient relation and no `int` cancellation
  are involved. **Postulated** via the module's `axiom` helper (each
  carrying its statement as a self-hyp):
  - `rat_rel_trans` — transitivity of the cross-multiplication relation.
    Needs `int` *multiplicative cancellation by a positive* (cancel the
    common positive denominator) — now derivable from the fully-proved `int`
    ordered ring (`lt_mul_pos` + `lt_trichotomy`: `a·c = b·c ∧ 0 < c ⟹ a = b`),
    just not yet packaged. Once that lands, this becomes the int-analogue of
    `int_rel_trans`.
  - The remaining ordered-field axioms over the operations
    `rat_zero`/`rat_one`/`rat_add`/`rat_sub`/`rat_neg`/`rat_mul`/`rat_inv`/
    `rat_div`/`rat_lt` (all **defined** at the representative level;
    `rat_sub`/`rat_inv`/`rat_div` are the additive/multiplicative
    companions — `rat_div x y = x · y⁻¹`, `rat_inv` sign-normalised so the
    denominator stays positive). The unproved laws: commutative-ring
    `add_assoc`/`add_zero`/`add_neg`/`sub_def`/`mul_assoc`/`mul_one`/
    `mul_zero`/`distrib`, the multiplicative inverse `mul_inv`
    (now realisable concretely via `rat_inv`), the linear order
    `lt_*`/`le_def`, and the base strictness fact `zero_lt_one` — `ratLt`
    picks ε-representatives, so `0 < 1` is not reducible. Each is a HOL
    theorem derivable from the **now fully-proved** `int` ordered-ring theory
    through the quotient; filling them in does not change the public `fn`
    surface. The `int` order facts they lean on are all discharged. (The `≤`
    toolkit
    `le_refl`/`lt_imp_le`/`le_trans`/`not_one_le_zero` is **not**
    postulated — it is *derived* from `le_def` + the strict-order facts.)
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
  - `util.rs` — shared conjunction-proof plumbing.

  Still **specialised to `nat`** in `init/recursion.rs`:
  - **ε-assembly** — `recursion_theorem` / `rec_holds_proof` generalised to emit
    `⊢ ∃rec. P_rec rec` from totality + determinacy for any signature. The only
    remaining piece; it couples to the recursor's `defs` selector predicate
    (`natRec`'s `P_rec`), so generalising it means deriving the per-constructor
    equation predicate from the signature.
  - **The multi-recursive-argument / multi-constructor-argument paths** in
    `existence.rs`, `uniqueness.rs`, and `determinacy.rs` (conjunctive IHs /
    antecedents, componentwise injectivity, nested `∃`-witnessing) are partial:
    `existence` / `uniqueness` handle the general shape but are only *exercised*
    by `nat`'s ≤1-arg / ≤1-rec-arg cases, while `determinacy::det_case`
    explicitly **errors** on a constructor with ≥2 recursive arguments. A
    binary-tree or `list` signature is the first real test. The strict
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
- **Lemma application is explicit, not by unification.** Applying a lemma
  means `(lemma N)` then manual `inst`/`inst-tfree`/`all-elim`. A higher-level
  `(apply N args…)` that unifies the lemma's conclusion against the goal /
  arguments (first-order matching) is the natural next tactic.

- **No proof/`Term` pretty-printer (serialization-out).** `script` only
  *parses* the named syntax and *replays* it; there is no printer from a
  proof / `Term` back to the surface S-expression. This blocks content-addressing
  (hashing a proof term) and `(lemma …)`-by-hash references — both noted as
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
  Every proof rule — built-in *and* extension — now lives in the **rule
  registry** (`Rule` async trait, `register_rule`/`lookup_rule`, merged like
  tactics): `check` dispatches **every** head through `Env::lookup_rule`;
  `drv.rs::core_rules()` installs the ~35 built-ins into `Env::core`. The old
  hardcoded `Drv` AST + `parse_drv` pass are gone — `Rule::apply(&[SExpr], &mut
  CheckCtx)` **self-parses** its term/type/name/sub-derivation args (a
  `CheckCtx` gives `term`/`ty`/`name`/`push_var`/`check`), so a custom rule has
  the same power as a built-in. No remaining TODO for this item.
- **Lemma lookup is async; const lookup is sync (the data model is ready, the
  accessor + elaborator aren't).** `Env` is now ONE unified `entries:
  LazyMap<Entry>` (`Entry` = `Const|Lemma|Tactic|Rule|TacticAndRule`), so EVERY
  kind is already future-capable — a const *can* pend, no new machinery needed.
  **`Env::lookup_lemma` is `async`** (awaits a still-`#compute`-ing
  `Entry::Lemma`); the old boundary-await `lemma_refs`/`await_computed_deps` was
  deleted. `#compute` binds NAME via `define_computing` → `insert_pending`; a
  later `(lemma NAME)` or the force just awaits it. The remaining half of **"all
  env accesses async"** (user) is now just the *accessor*: `lookup_const`/
  `lookup_tactic`/`lookup_rule` are still SYNC `get_ready` peeks. Making
  `lookup_const` async makes the **elaborator (`infer.rs`) async** (recursive
  `BoxFuture` + const-lookup await) → `parse_term`/`CheckCtx::term`/
  `elaborate_concl` async — that's the unbuilt step for *one async task per
  definition* (a `const` loaded from the network, like `#compute` for a
  theorem). The non-async `lemma_ready(name)` peek stays for the sync
  `Theory::lemma` macro accessor (a forced theory's lemmas are all Ready).
  - **A `#compute` can't depend on another `#compute`.** Its proof runs in
    `spawn_blocking` against a *sync snapshot* of `internal`, driven by a nested
    `block_on`, so it can't await a sibling. (Only ordinary `#thm`s can.)
  - **`#spawn`** (`tokio::spawn`, non-blocking) is the natural sibling of
    `#compute` for IO-bound / cooperative work.
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
