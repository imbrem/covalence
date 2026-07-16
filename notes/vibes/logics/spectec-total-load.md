# Total-load: the entire WASM 3.0 SpecTec spec as one kernel-checked rule set

Status: **landed** (2026-07-17, `wasm-spec-total-load`; design of record below
unchanged). Companion to [spectec-fragment-api.md](./spectec-fragment-api.md)
(layering, the side-condition faithfulness analysis) and
[cfg-stratum-design.md](./cfg-stratum-design.md) (grammars). Corpus numbers
below are from the taxonomy sweep of the bundled 3.0 dump (125 relations / 558
rules, 462 functions / 804 clauses, 207 types, 231 grammars / 1431 productions).

## Landed (Wave C integration — final numbers)

`crates/kernel/hol/init/src/wasm/lower/total.rs::total_spec_clauses` is the
combined entry point (order contract in its module docs: rules → star aux →
Dec graphs → evaluators); `RelationEnv::spec` serves it through the Fragment
API. `wasm::spec::coverage_report` pins:

- **2216 combined clauses** (2026-07-17, post Wave-D fixes + Wave-E review
  fixes: encoding injectivity R1-F1/F2, value-dead-side census R3-F1, Dec
  clause-order R4-F1, mono-env-in-conditions R4-F2 + the Wave-F write
  families below), kernel-checked as one
  `RuleSet` = 558 rule clauses (**558/558 loaded**, 502 fully flattened;
  27/35 Else rewritten) + 184 star aux (**92/92 Iter sites**, 0 whole-site
  opaque) + 1117 `fn.*` Dec clauses (**804/804 source clauses loaded**,
  668 clean; 53 mono instances; 276 per-case sort-expansion copies) + 357
  `ev.*` evaluator clauses (139 `ev.neq` pairs; incl. the `ev.sort.*`
  families and 54 `ev.upd.*`/`ev.ext.*` write clauses over 27 path
  families), deduplicated across legs via one flattener pool.
- **321 opaque premises** total, censused by tag (biggest: `cond.iter-map`,
  `dec.order` — the clause-order complements, `dec.coarse-spine`,
  `cond.cmp-nonnat`, `cond.slice`/`cond.coarse-eq` — the value-dead-side
  buckets). Exact per-tag counts pinned in `coverage_report`.
- **Wave F — store-write evaluators (`ev.upd.*`/`ev.ext.*`).** `Upd`/`Ext`
  along `Dot`/`Idx` access paths evaluate through on-demand per-path-suffix
  clause families (`lower/evalrel.rs::upd_ext_families`): `Dot` levels
  rebuild the struct spine (hit/skip over the unique field key), `Idx`
  levels recurse like `ev.idx` with a real `ev.len` premise (out-of-bounds
  = underivable — SpecTec's partiality under-approximated), the empty tail
  substitutes (`upd`) or appends through `ev.cat` (`ext`) — exact at
  genuine points, so a consumer only ever sees the genuinely-updated
  encoding. Wired in `Flattener::enc` in **both** modes (children always
  cond-flattened): covers Dec RHSs (`$with_local` … via `expr_result`),
  Dec call arguments (`$with_locals`' recursion), and conditions consuming
  writes. Measured: 19/20 corpus `Upd`/`Ext` sites wired — 16 Dec clauses
  (`free_block free_func with_locals with_local with_global with_table
  with_tableinst with_meminst with_elem with_data with_struct with_array`
  upd; `add_structinst add_arrayinst add_exninst evalglobals` ext) + 2
  rule conditions (`Step_pure/vreplace_lane`, `Step_read/vload_lane-val` —
  whose upd-spine equality Sides were previously value-dead) — the 20th is
  a grammar production (out of scope); `$with_mem`'s **slice-path** write
  refuses exactly (`dec.coarse-spine`, needs an `ev.slice` splice family).
  `dec.coarse-spine` 58 → 49 (the 9 idx-path `Upd` conclusions), Dec clean
  659 → 668, opaque 330 → 321. Demos
  (`total::tests::store_writes_fire_end_to_end`): `fn.with_table` computes
  an actual updated-store encoding through the 4-segment
  `ev.upd.root.dot.TABLES.idx.dot.REFS.idx` chain and REFUSES an
  out-of-bounds write; **`Step/local.set` — a real writing step — derives
  end-to-end, hypothesis-free** (state-changing steps are unblocked;
  `Step/global.set`/`table.set`-style rules follow the same chain).
  Regressions: `evalrel::tests::write_families_evaluate_and_refuse`.
- **Wave-D Fix 1 — the sortless-metavariable over-approximation is closed**
  (`lower/sortguard.rs`; argument in `lower/mod.rs` § *Sorts, junk points…*).
  A metavariable whose every occurrence was `Sub`-wrapped (no bare
  occurrence at a position surviving into the encoded conclusion) lost its
  sort to `encode::canon`'s strip and derived false facts at well-sorted
  points (`fn.default_(F32, CONST F32 0)`; `Step_pure/local.tee` on a
  non-`val`). Fix, per site: **per-case expansion** on the `Dec` leg where
  the sort's catalogue cases are all nullary and the clause is residue-free
  (276 copies), else an **`ev.sort.<ty>` guard premise** (on-demand clause
  families like `ev.neq`; exact for nullary cases, head-level for payload
  cases; `ev.sort.list/opt.<ty>` elementwise variants for
  identity-collapsed iteration domains). Measured: 197/558 rules guarded
  (265 premises), Dec 163 guard premises. Regression:
  `decs::tests::default_expansion_refuses_wrong_sort` (F32 point refused,
  I32 point fires premise-free).
- **Wave-D Fix 2 — `Dec` RHSs are result-flattened**
  (`CondFlattener::expr_result`, cond-mode `enc` in result position):
  accessor bodies (`$table(z, x) = $sof(z).TABLES[…]`) now conclude with
  the accessed *value* constrained by `fn.sof`/`ev.dot`/`ev.idx`/`ev.len`
  premises instead of a coarse operator spine — the store-accessor family
  fires. Note the `dec.coarse-spine` bucket (58) did **not** shrink: it was
  always `iter`/`upd`/`ext` conclusions (zip/map RHSs + store *updates*),
  never `dot`/`idx`/`len` — those were sound-but-unfireable, invisible to
  the opaque census. Store *writes* landed in Wave F (below); the bucket is
  now the zip/map RHSs + `$with_mem`'s slice write.
- **Wave-D Fix 3 — encoding injectivity (R1-F1/F2) + the value-dead-side
  census (R3-F1) + iter-currency (R3-F3) + star hardening (R3-F2/F5).**
  `encode::shape` used to drop iteration binders+domains, `ListN` bounds,
  and `upd`/`ext` path index/slice exprs — so
  `encode(C(x)*{x<-xs}) = encode(C(x)*{x<-ys})`, `encode(v^n) =
  encode(v^m)`, `encode(s[0:=9]) = encode(s[1:=9])`; since `cond_eq` lowers
  `Eq` to `Side` equations between encodings, colliding sides were vacuous
  (refl at load) and rules fired at points where the SpecTec condition is
  FALSE (two kernel-checked counterexamples), while 15 corpus rules
  (`Step_read/block` …) silently lost metavariable constraints (`n`
  unconstrained). Fix: binders in the iteration tag
  (`iter.list[x]` / `iter.listn(i)[]`), domain/bound exprs and path
  index/slice exprs as encoded children; `collect_metavars` routes through
  the same shape, so the severed quantifiers return
  (`flatten::tests::step_read_block_constraints_restored`); the condition
  flattener reuses `encode::shape` itself (one shape source, no mirror) and
  wraps numeric metavars *inside* wholesale-encoded iter spines by
  substitution (one currency everywhere — `Step_read/vload-pack-val`'s
  `M`). Identity-iteration collapse still fires first. What's *still*
  coarse is censused, never silent: equation sides carrying value-dead
  `Slice`/`Cvt` spines become `cond.slice`/`cond.coarse-eq` opaque premises
  (12 rules that were "fully flattened" with undischargeable Sides — the
  fully-flattened drop 510 → 502 and opaque rise 240 → 264 are the honest
  correction); star inner-`Rule` element-access spines are counted
  (`star_coarse_inner` = 14, the `Extend_store` family); star tags are
  assert-unique wherever aux clauses are appended (R3-F5); `mixop_key`
  debug-asserts `%` never occurs in a fragment (R1-F5). Regressions:
  `encode::tests::{iteration_binders_and_domains_are_encoded,
  listn_bound_is_encoded, upd_path_indices_are_encoded}`,
  `flatten::tests::{map_equality_over_distinct_domains_is_not_vacuous,
  upd_equality_over_distinct_indices_is_not_vacuous,
  slice_equation_is_censused_opaque}`.
- Cross-leg end-to-end derivations, all hypothesis-free on the full set:
  (a) `Nondefaultable(REF ANY)` through `fn.default_`; (b) Else rule
  `Step_pure/ref.is_null-false` through an `ev.neq` tag pair **plus its
  `ev.sort.ref` guard**; (c) `Resulttype_ok([I32, I32])` through its star
  relation + `Valtype_ok/num ∘ Numtype_ok` (+ `ev.sort.numtype`); and the
  previously-blocked **(d) `Step_read/table.fill-zero`**
  (`total::tests::table_fill_zero_fires_through_store_accessors`): a real
  Else rule reading the store through `$table(z, x).REFS` on a concrete
  two-struct state — 9 premises spanning `fn.*` graphs, five `ev.*`
  relations, two arithmetic sides and two sort guards. Wall-times (debug):
  build+kernel-check ~290 ms; derivations ~0.1–0.5 s each (memoized layout).
- Conventions unified during integration: `Sub`-strip + identity-iteration
  collapse moved into the shared encoder (`encode::canon`); `fn.<f>` tags
  key on `Def` args only (`Typ`/`Gram` dropped — decs' convention);
  `ev.cat` has one definition (`evalrel::cat_clauses`); `Pow` joined the
  nat-arithmetic fragment.
- **Spec slices + transport (Wave F)** — `lower/slice.rs`, re-exported (with
  the whole total-load surface) through `covalence-hol-api`. `SpecSlice::carve`
  cuts a named sub-spec out of the total clause list by seed tags (whole
  relations / single rules / `fn.*`) plus the premise-tag **dependency
  closure** (star aux + `ev.*` families follow their consumers; `opaque.*`
  terminal; `carve_filtered` lets presets stop the tag-level closure from
  re-adopting filtered instruction rules); order = the total order restricted,
  with the slice→total index map. `SliceEnv` gives `RelationEnv` ergonomics
  over the slice's *own* small rule set (a 168-clause slice derives on a
  **default-size** test thread — no `with_total_stack`; cold derive ~1.7 ms vs
  ~300 ms on the full set) and implements `Fragment`. **`transport`** is the
  `1.0 ⊆ 2.0 ⊆ 3.0` seed: `⊢ Derivable_slice ⌜J⌝ → ⊢ Derivable_full ⌜J⌝`
  purely by assume-`Closed_full d` → nth-conjunct projection through the index
  map → re-conjoin `Closed_slice d` → `imp_elim` the opened slice theorem →
  `imp_intro`/`all_intro` (zero new rules; the kernel refuses any slice whose
  clauses aren't literally the full set's). Presets (2026-07-17, all
  **approximations by rule-name classification** — exactness awaits feature
  annotations): `lime` = the maximally-fireable core (premise-free `Step_pure`
  + `Steps/refl` + the `Numtype_ok`/`Valtype_ok/num`/`Instr_ok`
  nop/const/binop typing chain + the `ref.is_null-false` Else demo) — **168
  clauses, ZERO opaque premises** (asserted); `wasm1` ≈ 1.0 MVP (hardcoded
  instruction-key list, handler rules excluded) — **651 clauses, 52 opaque in
  42 clauses**; `wasm2` ≈ 2.0 (+reference types, bulk/table ops;
  **v128 excluded** by choice, exceptions excluded) — **724 clauses, 58
  opaque**. Tests: index-map integrity vs `ClauseMeta`, closure-closedness
  (every non-opaque premise tag has slice clauses or is a zero-clause
  builtin), lime fires on a default stack, transport end-to-end (conclusion
  literally the full-set `Derivable` statement, = the native full-set
  derivation).
- **Remaining caveats** (see `wasm/SKELETONS.md`): the legacy v1 leg
  (`wasm/relation.rs`) is still sortless (frozen comparison path);
  payload-position guard clauses are head-level; the float-metavariable
  junk-witness argument is meta-level, not machine-checked; whole-spec
  kernel ops need ~16 MiB stacks (`with_total_stack`); the one remaining
  coarse encoding position is non-expression `call` arguments (`Typ` args
  all measured type variables, `Gram` never occurs).

## Landed (Wave G — execution traces: multi-step runs through `Steps`)

`lower/trace.rs` (2026-07-17): single-step theorems chain into genuine
**multi-step execution traces** `⊢ Derivable ⌜Steps (z; prog) ↪* (z'; prog')⌝`
through the spec's own RTC rules — zero new machinery trusted, the driver only
proposes instantiations (`k::relation`'s construct-don't-trust shape).
Combined set now **2374 clauses** (+2 `ev.lift`, +2 `ev.nonempty2`), fully
flattened 502 → 505, opaque 321 → 318.

- **What a straight-line trace needs (measured)**: `Steps/refl` (premise-free)
  + `Steps/trans` (`Step` + `Steps` premises) lower clean; the lifts
  `Step/pure` / `Step/read` lower clean (identity iterations collapse — one
  judgement premise each); `Step/ctxt-label`/`ctxt-frame`/`ctxt-handler`
  lower clean. The one blocker was **`Step/ctxt-instrs`** (the `val*`-prefix /
  `instr_1*`-suffix frame rule every multi-instruction program needs), on two
  counts, both fixed:
  - its conclusion carried coarse `cat` spines (no real configuration ever
    matches them) — rule conclusions now encode in `Mode::Concl`, which
    flattens `Cat` through `ev.cat` premises (the Dec-RHS result-flattening
    move restricted to `Cat`; all 55 cat-conclusion rules — `Instrs_ok/seq`,
    `Step_read/block`, the `br`/`return` families … — now conclude genuine
    flat-list encodings);
  - its guard `val* =/= [] \/ instr_1* =/= []` was `cond.or-structural`
    opaque — the `Ne`-vs-empty disjunction shape now lowers to one
    `ev.nonempty2` premise (2 premise-free clauses, derivable iff either side
    is a snoc node — exact at genuine list points). 3 sites unlock
    (`ctxt-instrs`, `Step_pure/trap-instrs`, `Step_read/throw_ref-instrs`);
    the 10 remaining `or-structural` sites mix Eq/Ne-vs-case shapes
    (honest residue).
- **The driver** (`TraceEnv`): explicit chain API over any rule set containing
  the closure (full set or slice) — `lift_pure`/`lift_read`, **`frame`**
  (discharges all 7 `ctxt-instrs` obligations on ground configurations: four
  `ev.cat` evaluations by recursion, the `ev.nonempty2` witness, the `val*`
  elementwise sort guard), `chain` (folds `Step`s through `Steps/trans` onto
  `Steps/refl`, adjacency-checked; the kernel re-checks every application).
  Automatic per-step rule search is the recorded follow-on (SKELETONS).
- **THE DEMO** (`trace::tests` + printed by `coverage_report`; preset
  `slice::exec_slice` = lime seeds + `Steps` + `Step/pure` + `ctxt-instrs` +
  `binop-val`/`binop-trap`/`drop`, filter-carved to **155 clauses**):
  `z; [CONST I32 2, CONST I32 3, BINOP I32 ADD, DROP] ↪* z; []` derives
  hypothesis-free **on a default-size test thread** — const-fold via
  `Step_pure/binop-val`, framed over the `[DROP]` suffix via `ctxt-instrs`
  (endpoints are the genuine flat 4- and 2-instruction lists), then
  `Step_pure/drop` whole-sequence; 2 real steps + refl, ~120–250 ms debug
  (total build ~230 ms, carve ~2 ms) — and **transports into the full
  2374-clause set** via `slice::transport` (~170 ms), the conclusion literally
  the full-set `Steps` statement. Refusals: a falsified final configuration
  fails to chain (kernel premise mismatch in `Steps/trans`), and framing with
  both context parts empty fails (`ev.nonempty2` underivable — the spec's own
  guard).
- **Wave-F2 follow-up: `ev.lift` result flattening.** `Lift` (option→list)
  evaluates in condition/result positions (2 clauses), so `fn.binop_`'s
  DIV/REM conclusions (`lift($idiv_ …)`) now conclude the actual list:
  `[CONST I32 6, CONST I32 3, BINOP I32 (DIV U)] ~> [CONST I32 2]` fires
  through the builtin `fn.idiv_` (+`ev.lift` some-clause), ~19 ms; **the
  by-zero TRAP fires too**: `[CONST I32 6, CONST I32 0, BINOP I32 (DIV U)]
  ~> [TRAP]` through the spec's own premise-free ground by-zero clause
  (`opt.none`) + `ev.lift` none-clause + `Step_pure/binop-trap`'s `r = []`
  refl side, ~14 ms; a wrong quotient's defining side is kernel-refuted
  (`trace::tests::div_const_fold_and_by_zero_trap`).
- Tidy: the ~90 s (debug) whole-spec grammar variant T5b is `#[ignore]`d
  (T5 — the 27-byte module proof — stays); `coverage_report` prints the
  trace-demo numbers with derivability as the only floor.

## Landed (Wave F2 — integer-builtin defining clauses)

`lower/builtins.rs` (2026-07-17): the integer family gets **154 per-width
defining clauses** (order contract: a new leg between the Dec graphs and the
`ev.*` pool; `TotalReport.n_builtin_clauses`/`.builtins`), lifting the
combined set to **2316 clauses** (opaque census unchanged at 330 — the leg
emits no opaques, no judgement premises, `Side`-only arithmetic).

- **What was actually blocked** (measured, corrects the "91 zero-clause
  builtins" framing): `iadd_`/`imul_` spec equations already fired (pure nat
  `add`/`mul`/`mod`/`pow` + `ev.uncase`/`ev.proj`). But `isub_`/`signed_`/
  `inv_signed_`/`sat_*` conclude value-dead `Cvt` spines; `ieq_`-family/
  `ieqz_` conclude `fn.bool(cmp-spine)` (a premise that matches no
  `bool.true/false` point — sound, invisibly dead); `idiv_`/`irem_` route
  through rat division + zero-clause `truncz`; shifts/rotates/`iclz_`/
  `ictz_`/`ipopcnt_`/bitwise are genuinely zero-clause.
- **The leg**: 16 ops × widths 8/16/32/64 (scalar `sizenn` gives 32/64,
  SIMD `lsizenn` reaches 8/16; `idiv_`/`irem_` scalar-only 32/64): `isub_`
  (`(a+2^N−b) mod 2^N`), `ieq_/ine_/ieqz_` + `ilt_/igt_/ile_/ige_`×`U/S`
  (two outcome clauses each; **signed via the sign-bias embedding**
  `biased(x) = (x+2^(N−1)) mod 2^N` — the `signed_` Dec graphs were audited
  and provide only `Cvt`-spine conclusions, nothing to build on), `ishl_/
  ishr_(U/S)/irotl_/irotr_` (`k mod N`, div/mod/pow formulas; S-shr sign
  fill `2^N−2^(N−k')`), `iclz_/ictz_` (ground `0↦N` + bound-pinned nonzero
  clauses), partial `idiv_/irem_` (option results mirroring the Dec eps
  convention; `0 < b` guards so the spec's own ground by-zero → `eps`
  clauses stay the only by-zero derivations; explicit `INT_MIN div −1 ↦
  none` overflow clause). Every clause carries carrier guards (`a < 2^N`…) —
  antecedents strictly at least as strong as the spec's (which assumes
  well-typedness); order-complement machinery is unnecessary (clauses are
  guard-disjoint and each independently faithful to the total function).
- **Faithfulness is oracle-tested, not asserted**: `builtins::tests` check
  every op at w = 8 (+ div/rem) against Rust's independent two's-complement
  arithmetic (`wrapping_sub`, `i8` casts, `rotate_left`, `leading_zeros`,
  `checked_div`, …) over a grid covering both sign classes and the special
  points — each op **fires exactly at the oracle result and refuses r ± 1**;
  out-of-carrier operands refuse everything.
- **The payoff demo** (`total::tests::binop_const_fold_fires_and_refuses`):
  real const-fold steps fire hypothesis-free on the full combined set —
  `[CONST I32 2, CONST I32 3, BINOP I32 ADD] ~> [CONST I32 5]`
  (`fn.size ∘ fn.sizenn ∘ fn.iadd_ ∘ fn.binop_ ∘ ev.mem` →
  `Step_pure/binop-val`) and `[CONST I32 5, CONST I32 3, BINOP I32 SUB] ~>
  [CONST I32 2]` **through the builtin `fn.isub_` clause** (underivable
  before this leg); the wrong results (6, 3 resp.) are kernel-refuted.
  ~0.9 s / ~0.5 s (debug, warm layout).
- **Census note**: the opaque buckets do *not* shrink (they never counted
  the `fn.bool`/`Cvt`-spine dead ends — those were sound-but-unfireable and
  invisible to the census, like the Wave-D store-accessor case); what grows
  is *dischargeability*. Remaining builtin frontier: 85 zero-clause tags
  (floats, lanes/serialisation, bitwise + `ipopcnt_`, `truncz`); the
  `lift(r)` result spines that blocked `binop-val` DIV/REM consumption are
  resolved by Wave G's `ev.lift` flattening (above).

## Goal and soundness frame

**Goal:** every definition of the spec *loads* — becomes clauses of inductive
definitions the generic `metalogic` engine drives, zero axioms, kernel-checked —
so the whole spec is a concrete API and a big corpus to keep green.

**Frame:** a lowered clause's antecedents must be **at least as strong** as the
SpecTec premises. `Derivable_R` may *under*-approximate the true relation
(underivable antecedents = incompleteness, reported), never over-approximate.
"Loading" (clause exists, faithful) is separated from "discharging" (a ground
instance's antecedents can be proven), and dischargeability grows monotonically
afterwards. This keeps the fragment-api note's constraint — conditions are
never dropped — while making full-coverage loading achievable now.

## Corpus facts that shape the design

- Premise totals over 558 rules: `Rule` 300, `If` 296, `Iter` 92, `Else` 35,
  **`Let` 0**. No nested `Iter`, no `List1`, every `Else` at premise position 0,
  every `Iter` domain a plain `Var`.
- `If` conditions: 17 pure value-fragment; 149 contain `Call` (73 distinct
  functions); 129 contain `Uncase`/`Proj`; 77 contain an `Iter` expression
  (structured equalities `x* = y*` etc.).
- `Dec` clauses are relation-rule-shaped (patterns = `SpecTecExp`s, RHS, the
  same premise zoo; 217 `If`, 42 fns with `Else`, 0 `Let`). 91 zero-clause
  builtins (float/int-bit/serialization) are the unavoidable non-equational
  frontier. Mutual recursion only in `subst_*`, `free_*`, `free_instr/block`.
- 16 higher-order combinators (`iv*/fv*`) take `Def` params, but every call
  site passes a *constant* function name — finite monomorphisation.

## The five legs

### 1. Engine: unary mixed premises (Wave A1)

`RuleSet` clauses were always free-form; only the unary *application* path
lacked a `Side` premise kind. Port `metalogic::binary::derive_mixed` (the
grammar engine's `Matches` precedent): `Side(Thm)` discharged by plain
`imp_elim`, `Derivation(Thm)` by the `all_elim(d).imp_elim(assumed)` move.
Plus memoization (cached clause layout / `Closed` term / assumed Thm) for the
~2000-clause scale.

### 2. Encoding: real-nat literals (Wave A2)

`Num{Nat(n)}` encodes as `app(st$c$num.nat, ⌜n⌝)` with a **real numeral**
child (Φ = nat, so real nats live in the carrier natively); ints as
sign/magnitude. One ∀-bound metavar then serves both the opaque judgement
spine and a *computable* arithmetic antecedent — the fragment-api note's
"instantiate condition-metavars with real nats" made structural. Numerals are
kernel-decidable (`⊢ ¬(2=3)` by computation), which is what makes `Else`
negation dischargeable at ground instances. Faithfulness obligations:
distinctness from `app`-spines, injectivity, substitution = `all_elim`
round-trip — tested.

### 3. Condition flattening + evaluator relations (Wave B)

`lower_rule` compiles an `If` condition into **premises + a residual
antecedent** (logic-programming flattening):

- `Call f(args)` → fresh metavar `r`, premise `d ⌜fn.<f> (args…, r)⌝` against
  f's **graph relation** (leg 4).
- `Uncase`/`Proj`/`Dot`/`Idx`/`Len`/`Cat`/`Cvt`… → structural **evaluator
  relations** with finitely many schematic clauses over encoded terms (e.g.
  `uncase.<ty>.<case>` one clause per catalogue case; `len` by snoc-spine
  recursion with real-nat successor), emitted on demand (only tags used).
- Pure constructor/metavar equalities (`x* = y*`, tuple/case equations — the
  "If:other" class) → **syntactic equations over encodings** as `Side`
  antecedents: encoding is injective on the corpus, so encoded-term equality ⟺
  SpecTec equality; ground discharge by `refl`.
- Value-fragment arithmetic residue → real HOL props over the shared metavars
  (`Side`), discharged by `side_cond`/`reduce`.

### 4. Functions as graph relations (Wave B)

Every `Dec` clause `f(pats) = rhs -- prs` lowers to a clause of relation
`fn.<f>`: conclusion `d ⌜fn.<f> (pats…, rhs′)⌝` where `rhs′` has its `Call`s
flattened into premises (same flattener), plus the clause's own premises.
Zero axioms — a graph relation, not a defining equation; determinism is not
asserted (relational reading is sound regardless). `Else` clauses get negated
earlier-guard antecedents (leg 5). `Def`-param combinators are monomorphised
per constant call-site op. The 91 zero-clause builtins load as **declared
relations with no clauses** (sound: judgements mentioning them are simply
underivable) and are reported as the executor/axiom frontier — the natural
seam for the future WASM-executor observer.

### 5. `Else` as negation preprocessing (Wave B)

`-- otherwise` = "no textually-preceding sibling rule (same conclusion
pattern group) applies". Preprocess at the SpecTec level, before flattening:
match sibling conclusions, take each earlier sibling's condition, **negate
syntactically** (De Morgan; comparison flipping Eq↔Ne, Lt↔Ge, …; ¬ of a
bool-valued call stays `Un Not` and flattens through the graph relation),
and emit the negations as ordinary `If` premises. Negated *structural*
equalities that don't bottom out in nat comparisons need on-demand `Neq`
clauses (one per genuinely-distinct tag pair actually required) — emitted
only where needed, checked distinct at emission, sound as antecedents
(under-approximate disequality).

### Iterated premises (Wave B)

Per `Iter` site, synthesize an auxiliary star relation in the same carrier
over left-nested snoc spines (`⌜[e₀…eₙ]⌝ = app(⌜[e₀…eₙ₋₁]⌝, ⌜eₙ⌝)`, base
`st$c$list`):

- `List`, k iteration vars → k-ary **zip-star**: `star(nil…)` and
  `P(x…) ⟹ star(xs…) ⟹ star(app(xs,x)…)`.
- `Opt` → two clauses (none / some).
- `ListN` (16 sites, bounds only `|l|` or a var) → **indexed star** with a
  real-nat index: `istar(l,0)` and `istar(l,n) ⟹ Body(n) ⟹ istar(l,n+1)` —
  real successor, real numerals (leg 2).
- Inner `If` (18 sites) → the star's element premise is the flattened
  condition.

## Grammars and types (Wave A3/A4)

- **Types:** a *total* reified case catalogue (case tags + payload shapes,
  keyed `(type, case)`, no HOL rendering) feeds the evaluator clauses and
  ground gating; multi-instance dispatch in `resolve_parametric` (+19 HOL
  renders); single-inst parametric counted honestly (+17 metric). The 9-type
  mutual SCC (blocks 53 HOL renders incl. `instr`/`module`) stays open — the
  mutual→single tagged-carrier reduction over the carved/impredicative
  backends is the plan, off the critical path.
- **Grammars:** whole-corpus `GrammarEnv` (all 231, both modes) + left-recursion
  guard (T* has a `Thexnum` cycle) + honest per-NT coverage class. Residuals:
  grammar-valued param monomorphisation, non-`If` premises, 2 bridge
  terminals, faithful `ListN`.

## Unlock ladder (measured, cumulative over the 284 skipped rules)

If:call +102 → uncase/proj +62 → structural-eq +44 → Else +24 → Iter(Rule)
+19 → frag +15 → Iter(If)/ListN +18 = **284/284**. The big four relations
(`Step_read`/`Step_pure`/`Instr_ok`/`Step`) hold 73% of skips.

## Risks / watch items

- **Scale:** `Derivable` statements embed all clauses textually; Arc-sharing
  keeps equality cheap but construction walks fresh structure. Memoization
  (leg 1) + keep the coverage test under a minute. If it degrades, the
  term-arena / verified-WASM-construction direction is the known long-term
  answer.
- **Faithfulness reviews:** encode change (leg 2), negation pushing (leg 5),
  `Neq` emission, and the injectivity claim behind syntactic-equation
  conditions each get an adversarial review pass (Wave D).
- **Int representation:** sign/magnitude in-carrier; only a few conditions
  need real int arithmetic — evaluator clauses cover them; report gaps.
- Rules whose conditions still can't flatten (if any) must keep loading via
  an explicitly-underivable reified antecedent (never dropped), and be
  reported — 558/558 loaded is the invariant; dischargeability is the
  growing number.
