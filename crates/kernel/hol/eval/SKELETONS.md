# Skeletons — covalence-hol-eval

See [`CLAUDE.md`](../../../../CLAUDE.md) § Skeletons and the [root index](../../../../SKELETONS.md).

## Pure-HOL unit tests: coverage gaps (stage E3, D5)

`tests/pure_hol_units.rs` checks definition-vs-native per cert family; open
gaps (full scoping in that file's module docs):

- **nat/int definitional derivations are `EvalThm`-typed** — the chains use
  HOL rules only, but `covalence-init` pins `EvalThm`; tier-generic init
  derivations (`Thm<L: HolTier>`) would land them at `Thm<CoreLang>` verbatim.
  Until then the pure tier holds only the δ/β spines (it cannot state literal
  equations at all — the D3 denotation axioms are eval-tier by design).
- **bytes definitional evaluation missing** — blocked on the `Blob` ↔ `list u8`
  bridge + list recursion (covalence-init `init/SKELETONS.md`); the test pins
  only the spine + the cert value.
- **fixed-width definitional evaluation stops at `toNat`/`fromNat`**
  (intentionally declaration-only); the body-forced differential is
  `tests/audit_reduce.rs::audit_reduce_matches_body`.

## Declaration-only catalogue ops (no definitional body yet)

These `defs/` term-specs carry `tm = None`: sound/complete on literals (via
the family certificate rules) but no open-form body, so nothing is provable by
`unfold_term_spec`. Each should become a `let_term!` def; on adding a body,
delete here and — if reducible — add to
`tests/audit_reduce.rs::audit_reduce_matches_body`. (Moved here from
`covalence-core` with the catalogue, stage E2.)

- **`sN.shr` (arithmetic right shift), `defs/int_ops.rs`** — needs floor-division
  (round toward −∞), not yet exposed (`int.div` truncates toward zero).
- **`nat` ops, `defs/nat.rs`** — `natBitAnd/Or/Xor`, `natToBytesLe/Be`,
  `natFromBytesLe/Be` are declaration-only (`term_decl!`).
- **`bytes` ops, `defs/blob.rs`** — `bytesConsNat`, `bytesAt` declaration-only
  (need a `nat ↔ u8` conversion).

(Fixed-width conversions `toNat`/`toInt`/`fromNat`/`fromInt`/`zext`/`sext` in
`int_ops.rs` and the F2b bit-level float ops in `defs/floats.rs` are
*intentionally* declaration-only — the primitive reducible interface, not a
stub.)

## EG3b transitional literal-T/F bridge (dies with EG5)

`boolean.rs` (`tru_eq_lit`/`fal_eq_lit`/`fal_from_lit`/…), the eval-tier
literal-premise tolerances in `derived.rs` (`false_elim`/`not_intro` accept
`⌜F⌝`-shaped premises at `CoreEval` only), the `fal-to-lit`/`fal-from-lit`
script rules, and init's bridge crossings (`init/logic.rs` simp locals,
`eqf_intro` twins, `inductive/carved.rs::eq_f`) all exist ONLY because the
`Bool` literals remain the certificate/normal-form currency. Delete the lot
when EG5 removes the literal leaves (the defined `tru`/`fal` become the sole
`T`/`F`).

## defs/core.cov source-of-truth flip (deferred, blocked on re-entrancy)

`core.cov` + the `defs::cov` parser mirror part of the catalogue as data, proven
byte-identical to the hand-written `defs::*` (`cov::tests`), but the accessors
still source from Rust. Flipping `defs::*` to source from `core_env()` is
DEFERRED: a prior attempt deadlocked (a `LazyLock` re-entered the same accessor
during its own init; reverted in `fed9819`). To redo: `parse_core` must resolve
references from the partial env under construction (or a build-local Rust
resolver), never the `core_env`-backed accessors — and must be **test-gated**.
Porting the numeric tower to data is the remaining follow-up.

## Symbolic float landers: only the binaries add/mul (stage EG2 `float-unwall`)

`tohol.rs` lands `f32.addBits`/`f32.mulBits`/`f64.addBits`/`f64.mulBits`
symbolically (`f{32,64}_add/mul_thm_symbolic`, shapes `F{32,64}BinEqE`) via the
newly-admitted `ToHolF32Val`/`ToHolF64Val` reify rules + `f{32,64}_bin_reify`.
Not yet landed (all reuse `FloatCert` + the same reify rules — no new admitted
rule needed):

- **Other binaries** (`sub`/`div`/`min`/`max`/`copysign`): reuse
  `f{32,64}_bin_reify` verbatim (same `F{32,64}BinEqE` shape); add a lander
  passing the matching `FloatOp` + `pe::F{32,64}{Sub,Div,…}` rule.
- **Unaries** (`sqrt`/`abs`/`neg`/`ceil`/`floor`/`trunc`/`nearest`): need a new
  symbolic shape `F{32,64}UnEqE` (mirror `IntUnEqE`) + a unary reify chain.
- **Comparisons** (`eq`/`ne`/`lt`/`gt`/`le`/`ge`): eq sort is `bool`, the result
  leaf is a `bool` literal not a `ToHolF*` leaf — needs a `bool`-result shape.
- **Conversions** (`promote`/`demote`/`truncSat`/`convert`): mixed operand/result
  widths/tags — one shape per family (cf. the mixed-sort `BytesLenEqE`).

## EG3a `zero` bridge is transitional; freeness rules still literal-stated

`rules::ZeroLitCert` (`⊢ zero = ⌜0⌝`) bridges the EG3a primitive
`TermKind::Zero` to the coexisting `Nat(0)` literal; it dies with the literal
at the maintainer-gated EG5 flip (compile-enforced — its body builds the
literal). Until that flip, core's `ZeroNeSucc`/`NatInduct` keep their
literal-stated conclusions (`⊢ ¬(⌜0⌝ = succ n)`, base `p[⌜0⌝/x]`) — switching
them breaks every literal-based induction in `covalence-init`. `zero`-form
facts derive through the bridge (`zero::zero_ne_succ_zero`); still open: a
derived `zero`-base `nat_induct` transport (λ-abstract the motive, `mk_comb`
the bridge, `beta_conv` both sides, `eq_mp` the base premise) if a consumer
needs induction stated at `zero` before EG5.

## P2 facade sweep — remaining literal-ctor sites (EG5-prep)

The `lit::mk_*`/`as_*` facade is the eventual single build/recognize chokepoint
(so EG5's swap reduces to the `Lit::to_term` flip). The high-traffic init sweep
is DONE (init `term-literal-ctors` ratchet 72→6). Remaining direct-ctor sites,
deliberately left as subtle/serialization/shape-test surfaces:

- **init `script/infer.rs`** — 4 code sites (`:283`/`:427` blob, `:298` nat
  builders on the `.cov` literal-inference path; `:863` a test asserting the
  exact `Term::blob(vec![1,2,3])` shape it produces + its `:858` doc comment).
  Sweep the three builders and the `want` shape together in a follow-up.
- **init `sexp.rs`** — 2 sites (`:290` blob / `:301` small_int deserialization
  builders), paired with this file's `TermKind::Blob/SmallInt` recognizer arms
  (tracked by the `purge-ratchet.json` ctor exception); flip together at EG5.
- **downstream (out of this stage's scope)** — `kernel/hol/traits`
  `hol_light_ctx.rs` (2× `bool_lit`), `proof/alethe` `hol.rs` (3× `bool_lit`).

## Minor

- **`prove_true` is single-step only.** It reduces one redex and bridges `= T`;
  the recursive normalise-then-decide workhorse remains `TermExt::prove_true` in
  `covalence-init` (whose ι steps route here since the S6 re-route).

## Minor

- **Connective-rule perf (logic-out).** and/or/imp/not/all/lem are now multi-step
  `CoreLang` derivations (`derived.rs`), not kernel rules — ~1.5–1.7x on the
  hot proving suites (real/int/utf16). Acceptable for now; if it bites, re-admit
  the hottest as `CoreEval` accelerator rules with the derivation as the standing
  soundness witness (same pattern as the arithmetic certs). See
  `notes/vibes/handoff/tohol-purge.md`.
