# Skeletons — index

## Top priority — biggest holes

Ranked, most blocking first. Each links to the registry where it's detailed.

1. **`covalence-pure` closed-world kernel — only Stage 0 built** — `Op`/`Expr`/
   `Eqn`/`Language` + base `()` exist; ADTs/`Set`, HOL, the builtins, and the
   `language!` macro are unbuilt. [`covalence-pure`](crates/kernel/base/SKELETONS.md)
2. **Term hash-consing not on-by-default / not adopted by consumers** — the rule
   surface has cons-threaded `_with` variants, but `Ctx` owns no interner and the
   script/init consumers don't thread a cons, so proofs still don't share one
   interner end-to-end; ~29% alloc churn and the source of the
   `list.cov`/`utf8.cov`/regex blow-ups. [`covalence-core`](crates/kernel/hol/core/SKELETONS.md), [`script` perf](crates/kernel/hol/init/src/script/SKELETONS.md)
3. **`.cov` script async core + source spans missing** — holes/channels deleted,
   errors are flat strings (no spans/traces), no typed pipeline; blocks
   LLM-assisted proofs and the project loader's concurrent compile. [`script`](crates/kernel/hol/init/src/script/SKELETONS.md)
4. **PA derivation constructors (quantifier/induction/Leibniz)** — the
   `Derivable_PA` motive-handler-capture wall; the deep-PA headline can't be
   constructed *through* the clauses yet. [`peano`](crates/kernel/hol/init/src/peano/SKELETONS.md)
5. **Metalogic structural `σ` transport + set.mm-scale rule sets** — transport
   proven only for `id`/`⟹`-homomorphic σ; the metatheory ladder
   (HOL→ZFC, `Metamath-L ≅ native-L`) waits on a reified inductive encoding. [`metalogic`](crates/kernel/hol/init/src/metalogic/SKELETONS.md)
6. **Declaration-only catalogue ops** — `nat` bit-ops, nat↔bytes,
   `bytesConsNat`/`bytesAt`, `sN.shr` carry `tm = None` (sound on literals only,
   nothing provable by `unfold_term_spec`); the catalogue now lives in
   `covalence-hol-eval::defs` (stage E2). [`covalence-hol-eval`](crates/kernel/hol/eval/SKELETONS.md)
7. **`list_foldl` + `map`/`filter` clauses and the `bytes`/`string` newtype
   surfacing** — discharge the foldl/map/filter recursor clauses and bridge
   `bytes`/`string` length/index/cat onto the list ops. [`init`](crates/kernel/hol/init/src/init/SKELETONS.md)
8. **CFG stratum for grammars** — SpecTec/regex front ends cover only the regular
   base case; `Var` non-terminals rejected, blocking full WASM binary grammar. [`hol/spectec`](crates/kernel/hol/init/src/grammar/spectec/SKELETONS.md), [`covalence-spectec`](crates/lib/wasm/spectec/SKELETONS.md)
9. **`rat`/`real` ordered-field postulates pending proof** — `mul_inv`, `le_def`,
   Dedekind-cut suprema still `axiom`-postulated. [`init`](crates/kernel/hol/init/src/init/SKELETONS.md)
10. **Alethe rule coverage + LIA renderer** — `goal_to_problem` is QF_UF + linear
    `int` only; most propositional/LA rules return `NotImplemented`. [`covalence-alethe`](crates/proof/alethe/SKELETONS.md)

The skeleton registry (every intentional placeholder: empty/stub modules,
removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and commented-out / `#[ignore]`d / deleted tests) is
**split per crate**, co-located with the code. See [`CLAUDE.md`](./CLAUDE.md)
§ Skeletons for the policy.

## Per-crate registries

- **[`covalence-pure`](crates/kernel/base/SKELETONS.md)** — closed-world equality kernel; Stage 0 built, later stages pending.
- **[`covalence-core`](crates/kernel/hol/core/SKELETONS.md)** — the `defs/` D3 residue (dies with the literal leaves), hash-consing default, `subst::close`, property-test coverage gaps.
- **[`covalence-hol-eval`](crates/kernel/hol/eval/SKELETONS.md)** — the eval tier (`CoreEval` + the moved `defs/` catalogue); pure-HOL unit-test gaps (tier-generic init), declaration-only ops, the `core.cov` flip, single-step `prove_true`.
- **[`covalence-init`](crates/kernel/hol/init/SKELETONS.md)** — split per module (project loader, theory catalogue, `.cov` script layer, models, regex/spectec grammars, metalogic, peano, ring). (The thin `covalence-hol` surface has no skeletons.)
- **[`covalence-kernel`](crates/kernel/core/SKELETONS.md)** — empty `facts` observer module; removed legacy prover.
- **[`covalence-shell`](crates/kernel/shell/SKELETONS.md)** — re-export shell; userspace helpers pending the HOL-on-store stack.
- **[`covalence-spectec`](crates/lib/wasm/spectec/SKELETONS.md)** — removed native `.watsup` frontend; single-version WASM grammar; regular-only byte-grammar bridge.
- **[`covalence-wasm`](crates/lib/wasm/core/SKELETONS.md)** — removed `cov:pure` host binding; `wit/pure.wit` + `covalence-core-test-guest` orphaned.
- **[`covalence-haskell`](crates/lang/haskell/SKELETONS.md)** — Haskell surface dialect: no HOL/kernel backend yet; small parser subset (no layout/patterns/types/do-notation).
- **[`covalence-alethe`](crates/proof/alethe/SKELETONS.md)** — Alethe rule coverage.
- **[`covalence-egglog`](crates/proof/egglog/SKELETONS.md)** — `EgglogBridge` Stage 0 (only `fiat` implemented, no kernel-backed impl); egglog `external` bridge disabled (released egglog lacks the proof module).
- **[`covalence-metamath`](crates/proof/metamath/SKELETONS.md)** — substitution engine + `.mm` reader: `set.mm`-scale streaming, canonical serializer, structured-tree encoding, symbol interning.
- **[`covalence-multiformat`](crates/lib/data/multiformat/SKELETONS.md)** — derivation-fact interchange format: unregistered private-use codecs, no signed envelopes, blake3-only multihash, simulated Coln reader.
- **[`covalence-acset`](crates/lib/data/acset/SKELETONS.md)** — generic ACSet library: only Δ migration (no Σ/Π), pullback skips attributes, string-only attribute values, `&'static str` schema names.
- **[`covalence-python`](crates/ffi/python/SKELETONS.md)** — HOL kernel bindings (`pure` module) removed pending rewrite.

A crate with no skeletons has no file. When you add the first skeleton to a
crate (or module) without one, create its `SKELETONS.md` and link it from its
crate index (or here).

## Registry maintenance

**Not yet a complete repo audit.** Entries were recorded as code was written, not
reconciled against a full sweep. Treat a missing entry as "not yet recorded," not
"no skeleton there."
