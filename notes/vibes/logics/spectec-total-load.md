+++
id = "N002K"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-19T00:00:00+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

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

- **3771 combined clauses** (2026-07-19, post Wave-D fixes + Wave-E review
  fixes: encoding injectivity R1-F1/F2, value-dead-side census R3-F1, Dec
  clause-order R4-F1, mono-env-in-conditions R4-F2 + the Wave-F write
  families below), kernel-checked as one
  `RuleSet` = 558 rule clauses (**558/558 loaded**, 553 fully flattened;
  30/35 Else rewritten) + 184 star aux (**92/92 Iter sites**, 0 whole-site
  opaque) + 1258 `fn.*` Dec clauses (**804/804 source clauses loaded**,
  802 clean; 53 mono instances; 405 per-case sort-expansion copies; 6
  expanded Dec-star sites / 12 defining clauses) + 309 integer-builtin
  clauses over 35 operations + 1462
  `ev.*` evaluator clauses (375 `ev.neq` pairs plus the encoded-natural
  disequality clause; incl. the `ev.sort.*`
  families and 61 `ev.upd.*`/`ev.ext.*` write clauses over 31 path
  families), deduplicated across legs via one flattener pool.
- **7 opaque premises** total, censused by tag (`dec.order` 1,
  rule-`else` 5, and one
  `dec.else-nonif-guard`). Exact per-tag counts are pinned in
  `coverage_report`. `TotalReport::opaque_sites` also pins their exact
  combined-set addresses: `Step_read/{br_on_cast-fail,
  br_on_cast_fail-fail,ref.test-false,ref.cast-fail,array.init_data-zero}`,
  `fn.vcvtop__`, and `fn.NotImmutReachable`. The first five require open
  composite applicability decisions, `vcvtop__` requires the complement of
  existential partial computations, and `NotImmutReachable` is the source
  specification's explicit emulation of relation negation. None is silently
  approximated.
- **Wave G — encoded integer ordering.** `ev.int.lt`/`ev.int.le` compare the
  canonical sign/magnitude integer encoding and reduce same-sign magnitudes to
  real HOL-natural side conditions; exact Nat→Int conversion in condition
  position supplies the common `$cvt` bounds. This removes 23 opaque premises,
  raises fully-flattened rules 502 → 505 and clean Dec clauses 668 → 684
  (including monomorphised copies), and proves the bundled-spec graph fact
  `$sat_u_(32, -1) = 0` through the full combined set.
- **Wave H — mapped-call evaluator relations.** Call-bearing `List`
  iterations lower to per-site `ev.map.*` relations: a nil clause and an exact
  zipped-snoc step whose element body uses the same `fn.*`/`ev.*` graph
  flattener. They work recursively inside call arguments, not only as a
  top-level equality. `Opt` and `ListN` maps share the same evaluator shape;
  `ListN` carries a real-nat index/bound and supports zipped domains. This
  eliminates `cond.iter-map` entirely (79 → 0), shrinks total opaque premises
  295 → 229, raises clean Dec clauses 684 → 698, and makes both the real
  `$free_block` empty map and `Step_pure/vsplat`'s zero-length SIMD map
  kernel-derivable.
- **Wave I — structural boolean guards.** `Or`/`Impl`/`Equiv` conditions lower
  to per-site `ev.guard.*` relations, one clause per true branch (`Equiv` uses
  the both/neither decomposition). This preserves genuine disjunction in the
  Horn engine, eliminates `cond.or-structural` and `cond.bin`, lowers total
  opaque premises 229 → 219, and makes an `Instr_ok/select-impl` numeric/vector
  branch kernel-derivable.
- **Wave J — exact constructor/option complements.** Ordered Dec patterns of
  the form `[CASE payload] ++ tail` followed by `[head] ++ tail` now acquire
  an ordinary structural `head =/= CASE payload` premise. The on-demand
  `ev.neq` family witnesses every other constructor of the owner type, so the
  complement is exact without inspecting the wildcard payload. Option
  presence similarly has the two exact `none`/`some(_)` clauses. This raises
  fully flattened rules 519 → 522 and clean Dec clauses 698 → 720, reduces
  `dec.else-pattern` 28 → 12, and shrinks combined opaque premises 219 → 183.
- **Wave K — Dec iterated premises share the star API.** The remaining
  optional guards (`growtable`/`growmem`) and zipped judgement lists
  (`instantiate`/`invoke`) now lower through the same `StarSite` and
  `LoweredIter` abstractions as relation rules. Five expanded sites contribute
  ten collision-checked defining clauses; empty optional and zipped-list
  instances are kernel-derived in real-spec tests. This eliminates
  `dec.iter-premise`, raises clean Dec clauses 720 → 722, and reduces combined
  opaque premises 183 → 180 (one newly exposed ordered overlap remains
  honestly censused).
- **Wave L — preserve mapped iteration across the Dec seam.** `ClauseCx`
  previously lifted calls inside an iterator before handing the result to the
  shared flattener, erasing the map dependency and forcing a raw `iter.*`
  conclusion. Iterators now cross that boundary intact (with Def callees
  monomorphised), so the existing per-site map evaluator owns their calls and
  zipped domains. Clean Dec clauses rise 722 → 739, fully clean functions
  302 → 318, canonical `dec.coarse-spine` halves 33 → 16, and combined opaque
  premises fall 180 → 147. A real `$subst_moduletype` theorem derives both
  empty mapped substitutions end-to-end.
- **Wave M — exact ListN identities/tabulation and slice writes.** An identity
  `x^n` now denotes its domain plus an exact `ev.len(domain,n)` premise;
  index-only `ListN` generators use the recursive map/tabulation evaluator in
  every judgement position. Store paths now include `Slice`: the evaluator
  witnesses `subject = prefix ++ old ++ suffix`, checks the start/count by
  literal-natural lengths, evaluates the selected segment, and rebuilds the
  result. Its focused theorem replaces a middle slice and refuses a mismatched
  count. Literal-successor `ev.len` results compose with encoded bounds.
  Canonical `dec.coarse-spine` reaches **zero**, clean Dec clauses rise
  739 → 755, fully clean functions 318 → 331, and combined opacity falls
  147 → 131.
- **Wave N — ordinary slice expressions.** `ev.slice` reuses the exact
  prefix/segment/suffix decomposition for reads in conditions, call
  arguments, and results. The dedicated `cond.slice` bucket reaches zero;
  nested unsupported conversions remain separately visible as
  `cond.coarse-eq`. Fully flattened rules rise 522 → 523, clean Dec clauses
  755 → 756, and combined opacity falls 131 → 123.
- **Wave O — encoded-natural ordering.** Iteration element variables arrive
  as full `num.nat` encodings rather than bare HOL naturals. `ev.nat.lt/le`
  now projects those payloads and discharges the real HOL order side, instead
  of misclassifying their typed comparisons as nonnumeric. Fully flattened
  rules rise 523 → 525 and combined opacity falls 123 → 120.
- **Wave P — ordered numeric-literal complements.** The reusable ordered
  pattern API now recognizes a rigid numeric literal followed by a wildcard
  and emits the exact typed disequality (for example `n ≠ 8`) instead of an
  opaque order premise. Constructor/literal complements are restricted to
  premise-pure predecessors: a non-`If` premise cannot be silently treated
  as unconditional. Clean Dec clauses rise 756 → 757, fully clean functions
  332 → 333, and combined opacity falls 120 → 118 (the literal clause's
  expanded copies remove two `dec.order` premises). The remaining wildcard
  overlaps are kept visible because most depend on erased SpecTec sorts or
  existential guard negation, not mere structural disequality.
- **Wave Q — sort-aware ordered applicability.** Earlier Dec clauses now
  retain the exact `ev.sort.*` guards attached by the sort-fix plan.
  Ordered-overlap analysis uses the shared case catalogue to prove that a
  guarded wildcard cannot overlap either a constructor outside its source
  sort or a wildcard guarded by a disjoint constructor set. Plain values only
  are eligible: list and option memberships overlap at `[]` and `none`.
  Clean Dec clauses rise 757 → 773, fully clean functions 333 → 346,
  canonical `dec.order` falls 27 → 11, and combined opacity falls 118 → 94.
- **Wave R — equality-witness projection and open numeric disequality.**
  Ordered guards now eliminate fresh equality-defined witnesses using the
  exact `∃x. x = t ∧ G(x) ⇔ G(t)` rewrite before negating the predecessor.
  The newly exposed open disequalities lower through a compact shared basis:
  option presence plus one encoded-natural clause whose payload inequality is
  a kernel-computable HOL side condition. Constructor pairs remain
  demand-driven; an eager all-variant cross-product was measured at over
  14,000 clauses and rejected. Fully flattened rules rise 525 → 526, clean
  Dec clauses 773 → 777, fully clean functions 346 → 349, canonical
  `dec.order` falls 11 → 10, and combined opacity falls 94 → 76.
- **Wave S — nonnegative-rational order and exact numeric conversions.**
  Rational comparisons built from `Nat → Rat` casts and division now use a
  shared numerator/denominator view, cross-multiplying into real HOL-natural
  order while emitting denominator-positivity premises. `Rat → Nat`
  truncation of such positive quotients becomes HOL `nat.div`; `Int → Nat`
  subtraction becomes `nat.sub` guarded by source nonnegativity. This
  eliminates `cond.cmp-nonnat` (18 → 0), raises fully flattened rules
  526 → 541 and clean Dec clauses 777 → 779, and lowers combined opacity
  76 → 58.
- **Wave T — conversion-bearing structural equality.** Supported
  `Rat → Nat`/`Int → Nat` conversions now evaluate in arbitrary condition
  operands, including exact `ev.slice` reads. A small `ev.unnat` identity
  projector bridges Dec-lifted full-encoding call results back into the
  numeric evaluator without changing their already-emitted graph currency.
  Equality evaluation is gated on the actual per-clause numeric discipline;
  iterated element variables remain conservatively opaque rather than causing
  lowering errors. Fully flattened rules rise 541 → 547,
  `cond.coarse-eq` falls 17 → 4, and combined opacity falls 58 → 46. One
  newly fireable Dec expands, exposing its sixth star site (12 clauses) and
  one additional ordered overlap.
- **Wave U — exact common-premise factoring for ordered rules.** `Else`
  preprocessing now factors relation judgements shared by the earlier and
  current sibling, extending their variable correspondence through the
  judgement's result. It also factors shared `And` conjuncts before negation:
  under current premise `P`, `P ∧ ¬(P ∧ G)` becomes exactly `P ∧ ¬G`.
  This makes `array.init_data-num` and `array.copy-gt` fully fireable; the
  latter retains its shared `Expand` and storage-shape equality and receives
  only the exact `i_1 > i_2` complement. Fully flattened rules rise
  547 → 549, rewritten Else sites 27 → 29, and combined opacity falls
  46 → 44. The remaining four `Ref_ok` complements cannot be encoded as
  negative `d J` antecedents in the impredicative positive-closure RuleSet:
  they require a positive, adequacy-certified decision relation. The
  `array.init_data-zero` Rule-and-If complement and the catch-handler
  constructor complement remain explicit branch-splitting work.
- **Wave V — numeric conversions below structural reads.** Supported
  `Rat → Nat` conversion shapes now participate in the numeric pre-scan even
  when nested below an exact structural evaluator such as `Slice`. Iterated
  premises scan rule-level arithmetic ride-throughs before conclusion
  encoding, then remove domain-local variables so iteration elements retain
  their full encoded currency; named `ListN` indices are marked only at their
  star site. This makes the real `Step_read/load-pack-val`,
  `vload-pack-val`, and `vload-zero-val` byte-slice equations fully fireable.
  Fully flattened rules rise 549 → 552, relation-level `cond.coarse-eq`
  reaches zero, and combined opacity falls 44 → 41 (one separate Dec-side
  coarse equality remains).
- **Wave W — finite source-sort complements for ordered Dec clauses.**
  Ordered wildcard analysis now aligns source variables structurally, uses
  the total case catalogue to enumerate and exclude the earlier source sort's
  constructor heads, and transports guards through directional pattern
  correspondence before negation. This eliminates `dec.else-pattern`
  completely (13 combined premises), discharges two further order conflicts
  including `$ordered`, raises clean source Dec clauses 779 → 793 and fully
  clean functions 350 → 364. The exact `ev.neq` coverage grows to 375 pairs;
  combined opacity falls 41 → 26.
- **Wave X — exhaustive handler-catch complement.** Exact-list/Cat language
  intersection first proves the unrelated `return_call_ref-handler` pattern
  disjoint from the throw fallback. The catalogue-aware preprocessor then
  checks that `catch` has exactly `CATCH`, `CATCH_REF`, `CATCH_ALL`, and
  `CATCH_ALL_REF`, compiling the fallback to one DNF guard: the first two
  constructors survive only when their exception tags mismatch, while the
  unconditional catch-all predecessors contribute no branch. The existing
  `ev.guard` relation gives the constructor payloads existential-witness
  semantics without splitting the source rule. Fully flattened rules rise
  552 → 553, Else rewrites 29 → 30, and combined opacity falls 26 → 25.
- **Final coarse-equality closure.** The signed rational `idiv_` quotient
  guard now lowers through an exact sign/magnitude evaluator instead of
  `cond.coarse-eq`. Clean source Dec clauses rise 793 → 794 and combined
  opacity falls 25 → 24; no `cond.coarse-eq` premises remain in the combined
  set.
- **UTF-8 ordered-clause closure.** Bounded DNF guard analysis, exact
  separated-Nat-interval contradictions, and recognition of the recursive
  map/concatenate singleton self-implication make all five `utf8` clauses
  clean. Clean source Dec clauses rise 794 → 798; source `dec.order` falls
  9 → 5, combined `dec.order` falls 18 → 11, and total opacity falls 24 → 17.
- **Ordered alias-expansion closure.** Equality guards now detect incompatible
  rigid record values (the I32/I64 `growtable` and `growmem` expansions);
  `jsizenn` is treated as the injective size projection on rigid integer-lane
  constructors; and call-result guards compare modulo variable equalities
  forced by nonlinear overlapping patterns. This cleans `vextternop__` and
  two of three `vcvtop__` clauses. Clean source Dec clauses rise 798 → 802,
  source `dec.order` falls 5 → 1, combined `dec.order` falls 11 → 1, and total
  opacity falls 17 → 7. The remaining `vcvtop__` predecessor has an honestly
  existential complement over a half selector and downstream partial calls,
  so it remains fail-closed.
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
  nop/const/binop typing chain + the `ref.is_null-false` Else demo) — **407
  clauses, ZERO opaque premises** (asserted); `wasm1` ≈ 1.0 MVP (hardcoded
  instruction-key list, handler rules excluded) — **1174 clauses, zero
  opaque**; `wasm2` ≈ 2.0 (+reference types, bulk/table ops;
  **v128 excluded** by choice, exceptions excluded) — **1272 clauses, zero
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

## Landed (Wave Y — exact integer bit structure)

`lower/builtins.rs` (2026-07-19) now gives first defining clauses to eight
more zero-clause integer builtins: `inot_`, `irev_`, `iand_`, `iandnot_`,
`ior_`, `ixor_`, `ipopcnt_`, and `ibitselect_`. The builtin leg is now
**186 clauses over 24 ops**, filling **14 of 91** zero-clause tags and leaving
a frontier of **77**; the combined set is **3646 clauses** at this wave.

- Definitions are exact at every reachable width (8/16/32/64), use only
  kernel-supported natural arithmetic, and carry explicit input and result
  carrier bounds. A bit is `(x div 2^i) mod 2`; values are reassembled as
  fixed finite sums. Boolean bit identities define AND/ANDNOT/OR/XOR,
  popcount sums bits, reverse changes their weights, and bitselect is
  `(a & mask) | (b & ~mask)`.
- No trusted bitwise oracle or evaluator family was added: all emitted clauses
  are `Side`-only and the kernel normalizes their `div`/`mod`/`pow`/
  `add`/`sub`/`mul` obligations. This adds no evaluator clauses and no opaque
  premises.
- Tests exhaust the independent 8-bit arithmetic truth tables, replay exact
  graph derivations and wrong-result refusals at 8/16/32/64, and retain an
  explicit ignored all-points HOL replay for deep audits. The combined-set
  payoff derives
  `[CONST I32 0x0ff0, CONST I32 0x00ff, BINOP I32 AND] ~>
  [CONST I32 0x00f0]` through `fn.iand_ ∘ fn.binop_ ∘ Step_pure/binop-val`;
  its wrong defining result is kernel-refuted.

## Landed (Wave Z — integer bit/byte serialization)

`lower/builtins.rs` (2026-07-19) now defines the integer-only serialization
quartet `ibits_`/`inv_ibits_` and `ibytes_`/`inv_ibytes_`. The builtin leg is
now **206 clauses over 28 ops**, filling **18 of 91** zero-clause tags and
leaving a frontier of **73**; this batch adds 20 clauses. With the concurrent
evaluator exactness batch, the measured combined set is **3668 clauses**.

- At each reachable integer width (8/16/32/64), plus the 128-bit width used
  by the real `v128.const` binary/text paths, forward clauses expose the exact
  fixed-length little-endian list of bits or bytes. Inverse clauses require
  that exact length, guard every element (`< 2` or `< 256`), and reconstruct
  the unsigned integer as a finite radix-weighted sum.
- All obligations use existing kernel natural arithmetic and the ordinary
  encoded list spine. There is no float interpretation, trusted byte oracle,
  evaluator extension, or opaque premise.
- Kernel replay tests establish both directions at every width and reject a
  changed element, changed reconstructed integer, malformed length, and
  out-of-range bit/byte. Thus the inverse helpers are partial exactly where
  their typed SpecTec domains are malformed rather than accepting a
  convenient modulo interpretation.

## Landed (Wave AA — exact integer SIMD lanes)

`lower/builtins.rs` now defines `lanes_` and `inv_lanes_` for the four valid
integer 128-bit shapes: I8×16, I16×8, I32×4, and I64×2. The builtin leg is
**214 clauses over 30 ops**, filling **20 of 91** zero-clause tags and leaving
a frontier of **71**.

- Lane zero is the least-significant lane. Forward clauses expose each lane by
  fixed-radix division/modulo; inverse clauses reconstruct the vector carrier
  by the matching finite sum.
- Shape, exact list length, the 128-bit vector bound, and every per-lane bound
  are structural or kernel-computed guards. Malformed lists, overflowing lanes,
  and wrong vectors derive nothing.
- Float shapes intentionally remain clause-less until HOL has an exact float
  carrier. Tests cover both directions for every integer shape, negative
  cases, float refusal, and a live `2^120` vector bit.

## Landed (Wave AB — exact integer conversion matrix)

`lower/builtins.rs` now defines the integer-only conversion primitives
`wrap__`, `extend__`, and `narrow__`, and supplements the value-dead source
equations for `iextend_`. Across every reachable 8/16/32/64-bit width pair,
the builtin leg is **302 clauses over 34 ops**, filling **23 of 91**
zero-clause tags and leaving a frontier of **68**.

- `wrap__` is exact reduction modulo the destination width, with the source
  carrier checked explicitly.
- `extend__` and `iextend_` use a shared low-bit interpretation and split
  signed extension at the source sign bit. `narrow__` saturates unsigned and
  signed values at the exact destination bounds.
- An independent bit-mask/two's-complement oracle checks every width pair and
  both sign classes, while perturbed results, ill-typed carriers, unsupported
  width directions, and float-shaped payloads are rejected. Float
  conversions and reinterpretation remain clause-less rather than inheriting
  an integer approximation.

## Landed (Wave AC — exact unsigned SIMD rounded average)

`lower/builtins.rs` now defines `iavgr_` at exactly the two instruction-reachable
integer lane widths, I8 and I16. The builtin leg is **304 clauses over 35 ops**,
filling **24 of 91** zero-clause tags and leaving a frontier of **67**.

## Landed (Wave AB — exact signed Q15 multiplication and frontier audit)

`lower/builtins.rs` now defines the instruction-reachable
`iq15mulr_sat_(16,S,...)` graph by five disjoint natural-arithmetic clauses.
They cover all four input sign classes and the unique saturating
`INT16_MIN × INT16_MIN` point. Oracle tests cross the rounding half-way
boundaries, sign classes, extrema, saturation, perturbed results, invented
widths/signs, and erased-carrier junk. The builtin leg is therefore **309
clauses over 36 ops**, filling **25 of 91** zero-clause declarations and
leaving **66 declarations**.

The remaining frontier is not honestly “all floats”. Its 61 distinct names
(five names have multiple source declarations) split as follows:

- **42 float-dependent names**: scalar float arithmetic/comparison,
  float bits/bytes and inverses, float/int conversions, reinterpretation, and
  the float-related relaxed choice relations;
- **7 explicitly relaxed/nondeterministic names**: `ND`, `R_idot`,
  `R_iq15mulr`, `R_laneselect`, `R_swizzle`,
  `irelaxed_q15mulr_`, and `irelaxed_laneselect_`;
- **10 representation/generic sequence names**: the composite
  `nbytes_`/`vbytes_`/`zbytes_`/`cbytes_` families and inverses plus
  `inv_concat_`/`inv_concatn_`;
- **2 exact-rational host primitives**, `truncz` and `ceilz`.

The relaxed declarations deliberately remain clause-less: replacing their
specified result sets by one deterministic answer would be a coverage score
improvement but a semantic regression. The generic representation and rational
families are separately actionable; they are no longer mislabeled as floats.

- The result is the WebAssembly unsigned rounded average
  `(a + b + 1) div 2`, computed in the unbounded HOL-natural carrier before
  returning to the lane carrier, so the intermediate sum does not wrap.
- Explicit operand/result bounds make erased or overflowing encodings
  underivable. Signed selectors and invented 32/64-bit AVGR calls receive no
  clause.
- Tests cover even and odd sums, maximum lanes, wrong-result refusal, signed
  refusal, unsupported-width refusal, and out-of-carrier refusal.

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

## Layered source and semantic APIs

The high-level surface now separates claims that used to be easy to conflate:

- `SpecTecSpec` owns and recursively indexes the complete elaborated AST;
  `HolSpec` owns the common-clause lowering and honest census; `lime()` carves
  the current zero-opaque dependency closure.
- `TypeFamilies` / `TypeFamilySource` losslessly reify all **207** type
  families, retain every instance/case/field parameter and all **56**
  refinement premises across **29** owners, and expose deterministic
  dependency/SCC analysis. The real mutual SCC is pinned to its nine exact
  members.
- `HolSort`, `ResolvedType`, and `SemanticTypeResolver` distinguish a carrier
  from its semantic invariant. The compatibility `CarrierTypeResolver`
  deliberately reports `SortInvariant::Unresolved`; carrier renderability is
  not mislabeled as faithful type semantics. The
  `RefinementAwareTypeResolver` now certifies the exact refinement-free
  dependency closure as `Unconstrained`, while every closure reaching one of
  the 56 retained refinements stays unresolved pending predicate lowering.
- `VariantTheory` / `VariantTheoryBackend` expose theorem-bearing constructors
  for currently nonrecursive coproduct variants: carrier, source-name lookup,
  constructor terms, injectivity, and pairwise distinctness derived through
  existing kernel laws. Recursive self placeholders still refuse.
- `DecisionLowerer` represents negative rule applicability only through a
  positive decision graph with an adequacy/totality certification contract.
  `CertifiedDecisionFamily` checks exact closed ground totality and adequacy
  theorems before exposing a request; all other requests use
  `OpaqueDecisions`. A direct negative `d J` premise is forbidden because it
  would make the impredicative positive-closure `RuleSet` operator
  non-monotone.
- Grammar roots are explicit: `GrammarRoot::Instance` and
  `RootedGrammarEnv` preserve canonical ground parameter identity and reject
  generic/symbolic roots rather than erasing their context.
- `ParameterizedGrammarIr` retains symbolic instance arguments, every
  production/premise, and stable source indices. It now follows the exact
  nullary-reference dependency closure. `IndexedGrammarEnv` assigns
  structurally distinct instances distinct `Derives_E` tags, lowers
  premise-free byte-regex productions and direct nullary references to real
  CFG/HOL clauses, and keeps parameter substitution and semantic premises as
  indexed refusal records rather than erasing them.

Grammar coverage remains separately honest. Of 1431 WASM 3.0 productions,
under mode lowers 1129 (97 full / 22 partial / 112 empty grammars) and
recognition mode lowers 1221 (153 full / 10 partial / 68 empty). Recognition
residue is 204 parameter references, four premise forms, and two Unicode
bridge terminals; 199 parameter references are text-format identifier-context
threading and require a parameter-indexed grammar relation, not wildcard
erasure.

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
