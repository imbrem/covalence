# Skeletons — index

## Top priority — biggest holes

Ranked, most blocking first. Each links to the registry where it's detailed.

1. **`covalence-pure` base logic unbuilt** — empty scaffold; the `core → pure`
   foundation the whole substrate refactor rests on. [`covalence-pure`](crates/covalence-pure/SKELETONS.md)
2. **Term hash-consing not threaded through the inference rules** — proofs don't
   share one interner end-to-end; ~29% alloc churn and the source of the
   `list.cov`/`utf8.cov`/regex blow-ups. [`covalence-core`](crates/covalence-core/SKELETONS.md), [`script` perf](crates/covalence-init/src/script/SKELETONS.md)
3. **`.cov` script async core + source spans missing** — holes/channels deleted,
   errors are flat strings (no spans/traces), no typed pipeline; blocks
   LLM-assisted proofs and the project loader's concurrent compile. [`script`](crates/covalence-init/src/script/SKELETONS.md)
4. **PA derivation constructors (quantifier/induction/Leibniz)** — the
   `Derivable_PA` motive-handler-capture wall; the deep-PA headline can't be
   constructed *through* the clauses yet. [`peano`](crates/covalence-init/src/peano/SKELETONS.md)
5. **Metalogic structural `σ` transport + set.mm-scale rule sets** — transport
   proven only for `id`/`⟹`-homomorphic σ; the metatheory ladder
   (HOL→ZFC, `Metamath-L ≅ native-L`) waits on a reified inductive encoding. [`metalogic`](crates/covalence-init/src/metalogic/SKELETONS.md)
6. **Declaration-only `covalence-core` catalogue ops** — `nat` bit-ops, nat↔bytes,
   `bytesConsNat`/`bytesAt`, `sN.shr` carry `tm = None` (sound on literals only,
   nothing provable by `unfold_term_spec`). [`covalence-core`](crates/covalence-core/SKELETONS.md)
7. **`list` recursion cons-side + nat Euclidean division** — gate `list_foldl`,
   `map`/`filter`, all `bytes`/`string`/text length/index, and `div_mod`/`mod_lt`. [`init`](crates/covalence-init/src/init/SKELETONS.md)
8. **CFG stratum for grammars** — SpecTec/regex front ends cover only the regular
   base case; `Var` non-terminals rejected, blocking full WASM binary grammar. [`hol/spectec`](crates/covalence-init/src/spectec/SKELETONS.md), [`covalence-spectec`](crates/covalence-spectec/SKELETONS.md)
9. **`rat`/`real` ordered-field postulates pending proof** — `mul_inv`, `le_def`,
   Dedekind-cut suprema still `axiom`-postulated. [`init`](crates/covalence-init/src/init/SKELETONS.md)
10. **Alethe rule coverage + LIA renderer** — `goal_to_problem` is QF_UF + linear
    `int` only; most propositional/LA rules return `NotImplemented`. [`covalence-alethe`](crates/covalence-alethe/SKELETONS.md)

The skeleton registry (every intentional placeholder: empty/stub modules,
removed-pending-rewrite subsystems, `NotImplemented` / `todo!()` /
`unimplemented!()` stubs, and commented-out / `#[ignore]`d / deleted tests) is
**split per crate**, co-located with the code. See [`CLAUDE.md`](./CLAUDE.md)
§ Skeletons for the policy.

## Per-crate registries

- **[`covalence-pure`](crates/covalence-pure/SKELETONS.md)** — empty base-logic scaffold.
- **[`covalence-core`](crates/covalence-core/SKELETONS.md)** — declaration-only catalogue ops.
- **[`covalence-init`](crates/covalence-init/SKELETONS.md)** — split per module (project loader, theory catalogue, `.cov` script layer, models, regex/spectec grammars, metalogic, peano, ring). (The thin `covalence-hol` surface has no skeletons.)
- **[`covalence-kernel`](crates/covalence-kernel/SKELETONS.md)** — empty `facts` observer module; removed legacy prover.
- **[`covalence-spectec`](crates/covalence-spectec/SKELETONS.md)** — removed native `.watsup` frontend; single-version WASM grammar; regular-only byte-grammar bridge.
- **[`covalence-alethe`](crates/covalence-alethe/SKELETONS.md)** — Alethe rule coverage.
- **[`covalence-egglog`](crates/covalence-egglog/SKELETONS.md)** — egglog `external` bridge disabled (released egglog lacks the proof module).
- **[`covalence-metamath`](crates/covalence-metamath/SKELETONS.md)** — substitution engine + `.mm` reader: `set.mm`-scale streaming, canonical serializer, structured-tree encoding, symbol interning.
- **[`covalence-multiformat`](crates/covalence-multiformat/SKELETONS.md)** — derivation-fact interchange format: unregistered private-use codecs, no signed envelopes, blake3-only multihash, simulated Coln reader.

A crate with no skeletons has no file. When you add the first skeleton to a
crate (or module) without one, create its `SKELETONS.md` and link it from its
crate index (or here).

## Registry maintenance

**Not yet a complete repo audit.** Entries were recorded as code was written, not
reconciled against a full sweep. Treat a missing entry as "not yet recorded," not
"no skeleton there."
