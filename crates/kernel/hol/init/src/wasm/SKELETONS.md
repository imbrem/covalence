# Skeletons — `covalence-init/src/wasm`

The SpecTec → kernel front end (WASM-spec acceleration). Input is SpecTec AST
S-expressions (`covalence_spectec::parse`); no `.watsup` frontend. Design +
phasing: [`notes/vibes/logics/wasm-spec.md`](../../../../../../notes/vibes/logics/wasm-spec.md);
the total-load push: [`notes/vibes/logics/spectec-total-load.md`](../../../../../../notes/vibes/logics/spectec-total-load.md).
Live coverage: `spec::coverage_report` (bundled WASM 3.0 spec — combined set:
558/558 rules + 804/804 Dec clauses loaded, 2374 clauses kernel-checked incl.
154 integer-builtin defining clauses + the ev.upd/ev.ext write families;
139-of-207 types use-site renderable). See
[CLAUDE.md](../../../../../../CLAUDE.md) § Skeletons, the
[crate index](../../SKELETONS.md), and the [root index](../../../../../../SKELETONS.md).

## Severe / blocking

- **Sortless-metavariable residue** (the over-approximation itself is FIXED
  for the total-load set — `lower/sortguard.rs`: per-case expansion +
  `ev.sort.*` guards, argument in `lower/mod.rs` docs; regression
  `decs::tests::default_expansion_refuses_wrong_sort`). Still open: the
  legacy v1 leg (`wasm/relation.rs`, kept as a frozen comparison path) is
  still sortless; payload-carrying guard clauses are head-level (payload junk
  is out of contract but un-audited payload-collision corners remain); the
  float-metavariable junk-witness argument is meta-level, not
  machine-checked; junk-point firing (premise-free rules on junk encodings)
  stays out of the faithfulness contract by design.
- **Mutually-recursive variant types.** `wasm::syntax` renders aliases /
  primitives / tuples / iteration / structs / **non-recursive variants**
  (`CoprodBackend`) / **self-recursive variants** (`ChurchBackend` `Φ⟨'r⟩`) /
  **parametric** type application incl. multi-instance dispatch + case-union
  join. Still deferred: the 9-type **mutually-recursive** SCC
  (`typeuse`…`rectype`; a sibling reference in the `rec` group cycles — the
  self-mapping only covers a type's own name; needs multi-variable Church
  encoding or the sealed recursion engine) — blocks 53 types incl.
  `instr`/`module`/`store`; **parametric cases** (non-empty `qs`:
  `fN`/`fNmag`/`ishape` + inherited `f32`/`f64` — also blocks
  `num_`/`lane_`/`lit_` joins and their `val`/`num`/`frame`/`result`/… heirs);
  and `text`/`rat`/`real`.
- **Slice-path store writes stay coarse.** `Upd`/`Ext` along `Dot`/`Idx`
  paths now evaluate (`ev.upd.*`/`ev.ext.*` write families,
  `lower/evalrel.rs`; writing steps ground —
  `total::tests::store_writes_fire_end_to_end`), but `$with_mem`'s
  `z[.MEMS[x].BYTES[i : j] = b*]` slice write refuses (needs an exact
  slice-write evaluator: split at `i`, splice a length-`j` replacement —
  `ev.slice` machinery) — blocks the `memory.*` writing `Step` rules.
- **Case/field refinement premises (`prs`) erased** — 56 across 29 spec types
  (`byte` renders as unconstrained `nat` without `< 256`). Rendered types
  over-approximate (faithfulness caveat, never soundness: no theorems derive
  from a `Type`); same class as the multi-instance case-union join.
- **Church types are polymorphic + term-free.** `ChurchBackend` gives `Φ⟨'r⟩` with a
  free result tvar (not a sealed monomorphic type) and defers the recursive
  constructor/fold terms (need handler-threading, `metalogic::toy`-style). A sealed
  `new_type_definition` backend + induction/recursion is the follow-on behind the
  same `VariantBackend` seam.
- **Constructor freeness lemmas not threaded.** `denote` renders variant `case`
  constructor *terms* (via `DenoteCtx::from_spec` + `CoprodBackend::ctor`), but the
  coproduct injectivity/disjointness *lemmas* aren't surfaced yet — needed once
  relations reason about constructors (case analysis / no-confusion). Also
  `uncase`/`case`-elimination and record field projection aren't rendered.
- **`Dec` graph-relation residue** (combined-set census, `spec::coverage_report`;
  all 804 clauses load; clean count per `coverage_report`): coarse-spine
  premises (zip/map iteration RHS — `subst_*` family + SIMD lane
  combinators; needs star-relation RHS — and the `$with_mem` slice write),
  `dec.order`
  (the clause-order complement — `Dec` clauses match IN ORDER, now enforced
  for every clause, `decs.rs` *Clause order* docs — where the earlier
  overlap's complement is a pattern disequality: `idiv_`/`irem_` trunc legs,
  `subst_*`/`free_*` catch-alls, `utf8`'s
  semantically-confluent-but-not-literal general clause) + else-pattern
  (same complement for explicit-`Else` clauses) — both need on-demand
  pattern-`Neq` clauses; iter-premises, else-nonif-guard; plus its share of
  the `cond.*` buckets below.
- **Builtin frontier after the integer leg** (`lower/builtins.rs` gives the
  16-op integer family 154 per-width defining clauses; oracle-tested vs Rust
  two's-complement): 85 of the 91 zero-clause tags remain clause-less —
  floats (`f*_`), SIMD lanes/serialisation (`lanes_`/`ibytes_`/`nbytes_`/
  `vbytes_`/`inv_*`), bitwise `iand_`/`ior_`/`ixor_`/`inot_`/`ipopcnt_`
  (need a bit-recursion `ev.*` family or per-byte tables; `inot_` alone is
  `2^N−1−a`, easy when wanted), `truncz`/`ieee_`, `iextend_`/`wrap__`/
  `extend__`.
- **Rule condition residue** (combined-set census; exact per-tag counts in
  `coverage_report`): `cond.cmp-nonnat` (int / `Cvt`-coerced comparisons —
  e.g. `Memarg_ok`'s `2^n ≤ N/8` elaborates through `Nat→Rat`),
  `cond.slice` + `cond.coarse-eq` (equation sides carrying value-dead
  `Slice`/`Cvt` spines — censused since R3-F1, previously silently-dead
  `Side`s counted as flat; firing them needs an `ev.slice`/conversion
  evaluation family), `cond.or-structural` (10 sites post Wave G — the
  `x =/= [] \/ y =/= []` frame guards lower via `ev.nonempty2` now; the
  remaining disjunctions mix `Eq`/`Ne`-vs-case shapes and need per-site
  or-relations), `cond.iter-map`, `cond.bin`, `cond.neq-open`, and 8 `else`
  (7 sibling-rule-premise + 1 sibling-undecided
  (`throw_ref-handler-next`, HANDLER_-group tag coarseness — refinement
  reviewed-and-refused in `else_::instr_tag` docs) — negation
  inexpressible, correctly opaque).
- **Encoding coarseness residue** (post R1-F1/F2 injectivity — iteration
  binders/domains/`ListN` bounds and `upd`/`ext` path exprs are now encoded):
  non-expression `call` arguments are still dropped from `call.*` tags
  (measured: all corpus `Typ` args are type variables, `Gram` never occurs);
  14 star sites' inner `Rule` premises carry coarse element-access spines
  (`S.FUNCS[i]`-style, the `Extend_store` family — `star_coarse_inner`
  census, R3-F2: sound syntactic keys, unevaluated; needs cond-mode
  flattening of star inner exprs).
- **Combined-set kernel ops need big stacks.** `Closed_L` over 1787 clauses is
  a ~1800-deep right-nested conjunction and kernel term walks recurse
  structurally (~16 MiB in debug) — whole-spec work must run under
  `lower::total::with_total_stack`. Long-term: iterative kernel walks / the
  term-arena direction.
- **`Dec` functions as real HOL `define`s** (the denotational mirror of the
  `fn.*` graph relations) still unstarted; `denote` covers value expressions
  only.
- **Relations → HOL predicates over those types (leg B) not started.** Once
  `syntax` (variants) + `function` land, lift each `Rel` to a real HOL inductive
  predicate (the denotational mirror of `relation`'s `Derivable_R`).

## Polish / increments

- **Preset slices are name-classified approximations** (`lower/slice.rs`:
  `wasm1`/`wasm2` classify instruction rules by rule-name key against
  hardcoded lists; non-instruction dependencies pull whole relations —
  tag-level closure granularity). Exact 1.0/2.0 subsets need per-rule feature
  annotations; v128 + exception handling deliberately excluded from both.
- **Transport is per-theorem.** `slice::transport` lifts one
  `⊢ Derivable_slice ⌜J⌝` at a time; the once-for-all theorem
  `⊢ ∀A. Derivable_slice A ⟹ Derivable_full A` (same moves under an assumed
  `Derivable_slice A`) isn't packaged yet — needed for the real
  `1.0 ⊆ 2.0 ⊆ 3.0` metatheorem statements.

- **`int` literals unaligned across legs.** `encode` carries `int` literals as a
  sign/magnitude `nat`-numeral pair inside `Φ = nat`; `denote` renders them at HOL
  `int` (`mk_int`). `nat` literals share one witness (same `mk_nat` term in both
  legs); `int` side conditions need a nat↔int coherence step or an int-in-Φ
  injection. `rat`/`real` literals stay opaque leaf constants (no kernel carrier).
- **No end-to-end `parse_defs` test.** Derivation tests build the `rel` AST
  directly; add one driving a real SpecTec S-expression through
  `covalence_spectec::parse::parse_defs → RelationEnv::spec → derive`.
- **Trace driver is an explicit chain API.** `lower/trace.rs` chains
  caller-derived `Step`s through `Steps/refl`/`trans` (+ `Step/pure`/`read`
  lifts, `ctxt-instrs` framing, ground `ev.*` helpers); automatic per-step
  rule *search* over a ground configuration (the `k::relation` matcher
  pattern) is not built — each step's rule + instantiation is supplied.
- **Trace certification (WASM acceleration payoff) not started.** Run a WASM engine
  (`covalence-wasm`) as an untrusted oracle and certify each step against the
  reduction relation (`Step`/`Step_pure`/`Step_read`) — the auto-search
  driver above is its natural seam (`notes/vibes/logics/wasm-spec.md` phase 4).
- **Mirror-principle cross-check not started.** `SpecTec ⟶ our-prover` vs
  `SpecTec ⟶ HOL ⟶ HOL-in-our-prover` commutative-diagram confidence
  (`notes/vibes/logics/wasm-spec.md` phase 5).
