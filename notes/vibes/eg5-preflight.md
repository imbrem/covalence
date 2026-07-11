# EG5 preflight — literal-leaf deletion readiness analysis

*AI-authored preflight (2026-07; UNBLOCKED update 2026-07-11 recording the two
maintainer decisions in §0.5 + the P1 guard extension landed this stage — the
EG5 deletion itself is still NOT executed). Scope: the
irreversible EG5 stage of the literal endgame
([`literal-endgame-design.md`](./literal-endgame-design.md) §6,
[`tcb-holomega-roadmap.md`](./tcb-holomega-roadmap.md) Front A) — deleting
`TermKind::{Nat, Int, SmallInt, Blob, Bool}` from `crates/kernel/hol/core`.
Grounded against this worktree's post-EG3a/EG3b/A3 HEAD (`d8f4202e`; goldens
verified green: `manifest_matches_golden` +
`tohol_unfolding_rules_are_exclusive` pass).*

**VERDICT: UNBLOCKED-WITH-DECISIONS** (was BLOCKED). Two maintainer design
decisions (2026-07-11, §0.5) resolve the two named preflight blockers:

1. **Nat's structural target is a *binary* encoding (log-sized), NOT a unary
   `zero`/`succ` tower.** This dissolves the O(value) perf wall — a moderate
   literal like `0xD800` lowers to a ~16-deep binary term, not a 55k-node
   succ-tower. `crates/kernel/hol/init/src/init/nat_binary.rs` already carries
   the `double n = 2n` / `succ` binary normal form with surjectivity proved;
   that is the intended encoding for the eventual `ToHolNat` structural
   unfolding.
2. **`SmallInt` becomes another `toHOL` *leaf*** — a `ToHolSmallInt` op over
   `Val<SmallIntLiteral>` (exactly like `ToHolNat`/`ToHolInt`), with **NO
   structural unfolding rule**. Because it has no structural partner it needs
   no exclusivity-guard pairing and is deletable as a plain `toHOL` denotation.
   f32/f64 are stored as SmallInt bit-patterns (tags `U32`/`U64`), so they ride
   along on the same treatment — their `ToHolF32`/`F64` leaf ops already exist.
   `SmallInt` is barely used, so churn is low. This means the float-lander gap
   (old blocker 1) no longer gates deletion: unlanded float facts keep their
   `ToHolSmallInt`/`ToHolF32/F64` *leaf* denotation, they are not stranded.

Consequently the guard-pairing and structural-unfolding story applies to
**nat, int, bytes only** (the three families that carry both a `*Val` reify
rule and a future structural `*Mk`/`Zero`/`Succ`/`Nil`/`Cons` rule);
smallint/float stay leaf-only.

---

## 0.5 Maintainer decisions (2026-07-11) — the unblock

The two decisions above are recorded here as the authoritative resolution of
the old §5 blockers. Their downstream consequences are folded into the S3/S4
plan sections (§2) and the blocker table (§5), which now read
`RESOLVED`/`UNBLOCKED`. The one remaining maintainer input — unary vs binary
concrete numerals (old blocker 3, the perf wall) — is **resolved by decision 1
in favor of the binary form**.

---

## 0. Current state (verified against HEAD)

- `termKindVariants: 19` (`tcb-audit.json`): the 5 literal leaves + `Zero`
  (EG3a) + `Succ` + the 12 structural/spec variants. EG5 target: **14**.
- `coreManifest: 25` (post-EG3b `FalseElim` removal), `evalManifest: 17`
  (16 raw + `HolApp` canon).
- EG3a DONE (`TermKind::Zero`, `ZeroLitCert` bridge). EG3b DONE (`tru`/`fal`
  defined specs, `defs/logic.rs:88,198`; connective calculus at `CoreLang`;
  transitional `Bool`-literal bridge enumerated in `eval/SKELETONS.md`).
  A3/DEFS-OUT DONE (sequent-reshaped freeness/choice rules; `defsCoupling` 29;
  `ZeroNeSucc` already accepts **both** zero shapes, `core/src/thm/rules.rs:570`).
- Float-lander gap **OPEN** (`eval/SKELETONS.md` "Symbolic float landers: only
  the binaries add/mul") — a roadmap hard precedent of EG5.

## 1. Inventory of remaining literal-leaf uses, by EG5 replacement

Grep basis: `TermKind::{Nat,Int,SmallInt,Blob,Bool}` matches + literal
constructor/recognizer call sites, whole workspace.

### 1a. Kernel-internal — dies by deletion (compile-enforced, mechanical)

| Site | What | Replacement |
|---|---|---|
| `core/src/term/term.rs` enum (~:625–:635) | the 5 variants | deleted; 19→14 |
| `term.rs:948–:964` | `Term::{blob, nat_lit, int_lit, small_int}` + `u8..s64` wrappers | deleted; downstream routes through the eval facade (`mk_*`) |
| `term.rs:1001–:1003` | `truth()`/`falsity()` `LazyLock<Bool>` | **repoint in place** to the `tru`/`fal` specs (EG3b) — API-preserving, callers don't move |
| `term.rs:822` `as_bool` | `Bool(b)` recognizer | recognize `tru`/`fal` spec terms |
| `term.rs:338–:342` (hash), `:1162–:1166` (Debug), `:1284–:1288` (wf), `:1412–:1416` (type_of) | leaf arms | deleted arms |
| `subst.rs` ~10 no-op leaf match blocks (:53, :113, :382, :467, :600, :660, :717, :774, :806, :881) | walker arms | deleted arms |
| `SmallIntLiteral`/`IntTag` (`term.rs:378–:548`) | the fixed-width literal payload; `IntTag::ty()` keys the `defs` bits chain | **survives as `Lit::Small` currency** (native value, no term leaf) — must move out of the `TermKind` orbit; ITS TERM FORM IS THE §5.2 GAP |
| `core/src/term/cons.rs:463,:532`; `core/tests/audit_typedef.rs:549` | `Bool` in hash-cons/audit tests | rewrite onto `tru`/`fal` |

### 1b. The `Lit` facade chain — flips, consumers never move (by design)

- `core/src/thm/lit.rs` — `Lit::{to_term, from_term, hol_type}`: THE single
  build/recognize chokepoint. Flip targets: `Nat`→`zero`/`succ` tower,
  `Int`→canonical `mkInt` pair form (`eval/defs/int.rs:86`),
  `Bytes`→`bytesNil`/`bytesConsNat` chain (`eval/defs/blob.rs:94`;
  declaration-only is fine — the admitted rules pin the denotation),
  `Bool`→`tru`/`fal`, `Small`→a `ToHolSmallInt` **leaf** over
  `Val<SmallIntLiteral>` (decision 2, §0.5 — a `toHOL` denotation, NOT a
  structural form; f32/f64 bit patterns route through it).
- `eval/src/lit.rs` — facade `mk_*`/`as_*` unchanged; `kind_name` literal arms
  die.

### 1c. Eval tier — the atomic-swap surface

- **OUT of `eval_rules!`** (same-family commit as the structural rules —
  guard-enforced; **nat/int/bytes only** per decision 2): `ToHolNatVal`,
  `ToHolIntVal`, `ToHolBytesVal` (`rules.rs:157,:219,:234`).
  `ToHolF32Val`/`ToHolF64Val` (`rules.rs:257,:273`) **STAY** — they reify to a
  `ToHolSmallInt` leaf (decision 2), not to a deleted structural form, so they
  are unguarded and unswapped (only their reify *target* flips from the
  `SmallInt` literal to the `ToHolSmallInt` leaf, in S3).
  `ZeroLitCert` (`rules.rs:476`) dies with the `Nat` literal (body is
  compile-enforced) — it is object-level (`⊢ zero = ⌜0⌝` inside `IsThm`), NOT
  part of the base-tier contradiction pair, so it may die in the deletion
  commit rather than the swap commit.
- **IN**: `ToHolNatZero`/`ToHolNatSucc` (over the **binary** `nat_binary`
  `double`/`succ` form, decision 1), `ToHolBytesNil`/`ToHolBytesCons`,
  `ToHolIntMk`, and a `ToHolSmallInt` **leaf** (decision 2 — a plain `toHOL`
  denotation, no structural partner, so NOT guarded). Names must keep the
  `ToHolNatZero`/`ToHolNatSucc` prefixes the guard string-matches.
- **STAY, conclusions flip implicitly via `Lit::to_term`**: `NatAddCert`
  (already symbolic), `PairVal`, `NatArithCert`, `SuccCert`, `IntArithCert`,
  `BytesCert`, `FixedWidthCert`, `LitEqCert`, `CoercionCert`, `FloatCert`,
  `HolApp`.
- **`tohol.rs` landers**: `nat_add_thm_symbolic` survives verbatim. The
  int/bytes symbolic landers (`int_add/mul/neg`, `bytes_cat/len`) transport
  through the dying `*Val` reify rules (`int_bin_reify` + `transport_symbolic`)
  and must be rewritten onto the int/bytes structural rules; the concrete
  self-floor witnesses (`int_arith_thm`/`bytes_thm`) inherit structural-form
  conclusions. `nat_add_thm` (the reifying exemplar) flips its reify target to
  the binary nat form. The **float landers** (`f32/f64_add/mul`) keep routing
  through the surviving `f{32,64}_bin_reify` + `ToHolF32/F64Val` → the
  `ToHolSmallInt` leaf, so they need no structural rewrite (decision 2).
- **EG3b bridge — delete wholesale** (already enumerated in
  `eval/SKELETONS.md`): `boolean.rs` (`tru_eq_lit`/`fal_eq_lit`/…),
  `derived.rs` literal-premise tolerances (:955, :985), the
  `fal-to-lit`/`fal-from-lit` script rules, `zero.rs` bridge derivations.

### 1d. Core rules — conclusion flips, manifest names unchanged

- `NatInduct` base check `Term::nat_lit(0)` → `Term::zero()`
  (`core/src/thm/rules.rs:614`).
- `ZeroNeSucc`: drop the `hol::zero()` literal arm (:575 — already
  dual-accepting since A3, so this is arm-deletion, not reshape).
- `docs/deps/core-manifest.txt` unchanged (names only, still 25).

### 1e. Downstream (untrusted; mechanical + semantic)

- **`covalence-init`** (~60 files): 104 `nat_lit` + 96 `int`-family + 16
  `blob` + 3 `small_int` direct constructor sites (+24 already on the facade);
  23 files / ~115 refs consuming `nat_induct`/`zero_eq_succ` whose base-premise
  shape flips `⌜0⌝`→`zero`; `hash.rs` literal tag arms (:238–:299 — content
  addresses change; tags documented unstable, no persisted-compat);
  `sexp.rs` literal serialization arms (:203–:217; no `.cov` fixtures carry
  literal atoms — verified); the EG3b bridge crossings (`init/logic.rs` simp
  locals, `eqf_intro` twins, `inductive/carved.rs::eq_f`); `wasm/denote.rs`.
- **`kernel/hol/traits`**: `hol_light_ctx.rs` `is_true`/`is_false`
  (:193, :198) → `tru`/`fal`.
- **`proof/alethe`**: `goal.rs:93` `Bool` arm + `hol.rs`.
- **`lang/haskell`**: 5 files (lower/backends/hol + 2 test files).
- **Script layer**: no literal `TermKind` matches (verified — only
  App/Abs/Free/Eq); exposure is the `fal-to-lit` rules (1c) + constructor
  calls in `tactic.rs`/`handle.rs:150`/`inductive.rs:225`.

## 2. Atomic-swap execution plan (ordered commits)

Pre-commits (additive, reversible, land now):

- **P1 — guard extension (DONE, this stage).**
  `tohol_unfolding_rules_are_exclusive` (`eval/src/rules.rs`) originally covered
  ONLY the nat pair (`ToHolNatVal` vs `ToHolNatZero/Succ` prefixes). The
  identical base-tier `⊢False` class exists per family (`ToHolIntVal` +
  `ToHolIntMk` ⇒ `Val(int_lit)` = `Val(mkInt-term)` via sym+trans — false
  definitional Eq). Extended to the **three families that carry both a `*Val`
  reify rule and a future structural rule — nat, int, bytes** — via a per-family
  exclusivity table keyed on the family name and its structural-rule prefixes.
  **Not** smallint/float (leaf-only per decision 2, no structural partner) and
  **not** the object-level `ZeroLitCert`. Adding a structural `*Mk` rule for a
  family REQUIRES dropping that family's `*Val` rule in the same commit — the
  guard fires at `cargo test` otherwise.
- **P2 — C0 facade sweep.** Migrate every downstream direct constructor /
  recognizer (1e; ~220 init sites + traits/alethe/haskell/tests) onto the eval
  facade so post-sweep `grep Term::nat_lit` outside core + `thm/lit.rs` is
  zero. Mechanical, testable, reversible; shrinks the swap commits to the
  facade flip.
- **P3 — wasm32 job** (§3) established BEFORE any swap so the swap commits are
  wasm32-gated.

The swap itself — **per-family staging is legal** (each family's transitional
and structural rules are exclusive *within* the family; families don't
interact), so stage lowest-blast-radius first:

- **S1 — bytes swap** (one commit): admit `ToHolBytesNil`/`ToHolBytesCons`,
  drop `ToHolBytesVal`, flip `Lit::Bytes` in `to_term`/`from_term`, rewrite
  `bytes_cat/len_thm_symbolic` transports, regen
  `docs/deps/eval-manifest.txt` (`COV_REGEN_GOLDEN=1`). Full test + wasm32
  gate in the same commit.
- **S2 — int swap** (one commit): `ToHolIntMk` in, `ToHolIntVal` out,
  `Lit::Int` flips to the **canonical** pair form, int landers rewritten.
  Carries the §6.2 int-disequality audit note in `LitEqCert`'s docstring.
- **S3 — smallint/float swap** (one commit): UNBLOCKED via decision 2.
  `SmallInt`/f32/f64 become plain `toHOL` **leaves** — no structural rule, no
  guard pairing. `Lit::Small` flips its reify target to a `ToHolSmallInt` op
  over `Val<SmallIntLiteral>` (the same leaf shape as `ToHolNatVal` before nat
  goes structural); `ToHolF32Val`/`ToHolF64Val` keep reifying to the
  bit-pattern leaf (now `ToHolSmallInt`, not the deleted `SmallInt` literal).
  Because there is no structural `SmallInt` partner rule, this commit does NOT
  touch the exclusivity guard and can be written today. Unlanded float facts
  are not stranded — they retain their leaf denotation.
- **S4 — nat + bool swap** (one commit, the big one):
  `ToHolNatZero`/`ToHolNatSucc` in — over the **binary** `nat_binary`
  `double`/`succ` normal form (decision 1), NOT a unary succ-tower;
  `ToHolNatVal` out (guard forces same commit); `Lit::{Nat, Bool}` flip
  (`Nat` → the binary structural form via `nat_binary.rs`);
  `truth()`/`falsity()`/`as_bool` repoint to `tru`/`fal`;
  `NatInduct`/`ZeroNeSucc` flip to `zero`-form (1d); EG3b bridge deleted (1c);
  init induction/normal-form consumers repaired (1e). The binary encoding keeps
  moderate-magnitude numeral proofs log-sized (no 55k-node towers), so this is
  where the init semantic churn concentrates but NOT a perf regression.
- **S5 — the deletion commit** (irreversible): delete the 5 `TermKind`
  variants + constructors + all 1a arms + `ZeroLitCert` + `kind_name` arms +
  `hash.rs`/`sexp.rs` literal arms; relocate `SmallIntLiteral` to the `Lit`
  orbit; regen `tcb-audit.json` (`termKindVariants` 14) + `bun run deps`.
  rustc enumerates every residual site — nothing survives by accident.
- **S6 — Cluster A** (separate follow-on, per roadmap sequencing): empty
  `core/src/defs/` of the D3 residue type chain (`bits`/`int`/`bytes`/`unit` +
  carrier closure) into eval; the `exists`/`and` connective residue stays
  (L4-gated, `forall_spec`/`and_spec` pointer identity).

**Golden/manifest choreography:** `eval-manifest.txt` regenerates at S1, S2,
S3, S4 (net 17 → ~16: −6 transitional, +5-or-more structural);
`core-manifest.txt` untouched throughout; `tcb-audit.json` at S5. The
exclusivity guard is the atomicity tripwire: any split admitting a structural
rule while its family's `*Val` survives fails `cargo test` at the commit
boundary — after P1, per family, not just nat.

## 3. wasm32 32/64-bit divergence audit plan

Precedent (the class): `nat.shr` keyed off `usize` — a **wasm32-only
`⊢False`** invisible to green 64-bit CI
(`handoff/tohol-purge.md:24,61`). EG5 is the only Front-A stage the roadmap
marks wasm32-adversarial-audit-gated.

1. **Static sweep** (before S1): audit every `usize` / narrowing cast on the
   swap-touched trust surface — `base/trusted` CanonRule gates,
   `covalence-pure-eval` rules (`shl`/`shr`/`pow` refusal guards, `bytes`
   `at`/`slice` indices, length paths), `eval/certs.rs` dispatch
   (the `LazyLock<HashMap<usize, _>>` ptr-id keys at :95 are identity-only —
   verify), and **especially the new structural builders**: the
   `Nat`→succ-tower and `Bytes`→cons-chain loops MUST iterate on the bignum /
   the buffer, never a `usize`-truncated count (a truncated tower count = a
   wrong term = a false minted equation — exactly the `nat.shr` class).
2. **Dynamic differential job**: run the `covalence-pure-eval` semantics
   suite + `covalence-hol-eval` cert/structural tests on
   `wasm32-wasip1-threads` under wasmtime; pin boundary KATs straddling
   2^31/2^32 (nat shift amounts, pow exponents, `bytes.len`, slice bounds,
   u64-magnitude values) bit-for-bit against native x86-64 outputs.
3. **Adversarial pass** (the audit gate proper): per family, attempt to mint
   `⊢False` on wasm32 through inputs whose `usize`-narrowed images collide,
   against both the surviving cert families and the new structural rules.
   Multi-agent adversarial format (per `kernel-soundness-trait-gating-lessons`:
   green tests don't catch this class).
4. **Gate**: S1–S4 do not merge until (a) the job is green on both targets and
   (b) the static-sweep findings are recorded in the worklog.

## 4. Init-churn estimate

- **Mechanical (P2 sweep)**: ~220 direct constructor sites in init (60 files)
  + ~10 more files across traits/alethe/haskell/test-guest + 83 test-file
  hits. Sed-adjacent; 1–2 sessions.
- **Semantic (S4)**: 23 init files / ~115 `nat_induct`+`zero_eq_succ` refs
  flip base-premise shape; the EG3b bool-bridge crossings; every
  `prove_true`/`reduce` consumer whose normal form was a literal. Days of
  proof repair, concentrated in nat/bool; bytes/int (S1/S2) are small.
- **The perf wall — RESOLVED (decision 1, §0.5): post-S4 a concrete numeral is
  a *binary* term, not a unary succ tower.** Moderate-magnitude literal proofs
  — `char.rs` surrogate bounds (`0xD800`), utf8/utf16 code points,
  `nat_parse`/`nat_div` radix arithmetic — lower to log-sized binary terms
  (~16 deep for `0xD800`, not 55k nodes), so they stay O(log value) per
  numeral, not O(value). The binary normal form is `init/nat_binary.rs`'s
  `double n = 2n` / `succ` with surjectivity proved; `ToHolNatZero/Succ` unfold
  onto it. No longer a wall.
- **Content addresses**: every literal-containing term re-addresses
  (`init/hash.rs` tags are documented in-flux, no persisted-hash compat — the
  roadmap's "changes content-addresses" is acknowledged, low-risk today).

## 5. Blockers — all RESOLVED (see §0.5)

1. **Float symbolic-lander gap — RESOLVED (decision 2).** It no longer gates
   deletion: with `SmallInt`/f32/f64 as plain `toHOL` **leaves**
   (`ToHolSmallInt`, `ToHolF32/F64Val` surviving), an unlanded float fact keeps
   its leaf denotation rather than being stranded on a missing structural path.
   Landing the remaining symbolic float binaries/unaries/comparisons/conversions
   stays desirable (proving-power) but is decoupled from the one-way EG5 door.
   The four binary add/mul landers still exist (`eval/SKELETONS.md`).
2. **`SmallInt` (and float bit-pattern) structural replacement — RESOLVED
   (decision 2): there is no structural replacement, by design.** `SmallInt`
   becomes a `ToHolSmallInt` leaf over `Val<SmallIntLiteral>`; `ToHolF32/F64Val`
   reify into that leaf; `FixedWidthCert`/`FloatCert`/`CoercionCert`/
   `LitEqCert`-on-`Small` conclusions read the leaf. No `uN` structural rule, no
   guard pairing, no unary-tower infeasibility. `SmallInt` is barely used, so
   churn is low.
3. **Concrete-numeral feasibility — RESOLVED (decision 1): binary, not unary.**
   The `nat_binary.rs` `double`/`succ` form keeps hot utf8/utf16/parse suites
   log-sized; the one-way door no longer risks a perf-driven revert.

Named risks that remain AFTER unblocking (want maintainer eyes, not blockers):

- **Int disequality under the quotient** (§6.2 of nobody): `LitEqCert`'s `F`
  direction rests on "distinct literals denote distinct values"; `mkInt` pair
  forms are NOT injective (`mkInt(1,0) = mkInt(2,1)`). Sound only if
  `Lit::Int(i).to_term()` emits the **canonical** representative and the cert
  refuses non-canonical operand shapes — needs an explicit audit paragraph in
  the S2 commit.
- The guard-extension gap (P1) — CLOSED this stage: the per-family
  exclusivity table now forbids co-admitting `ToHolIntVal`/`ToHolBytesVal` with
  their structural partners as well as the nat pair.
- The wasm32 class (§3) on the new structural builders.
- One-way-ness itself: deleted public ctors + re-addressed content hashes +
  a manifest swap with no reverse migration.

## 6. Bottom line

The mechanical deletion surface is completely enumerated, compile-enforced,
and smaller than it looks (the facade + EG3b + A3 prep did their job: core's
own literal coupling is ~10 walker arms, 5 constructors, and 2 rule checks).
The swap choreography is well-defined and per-family stageable with the
extended guard as tripwire. **EG5 is UNBLOCKED (§0.5):** the two former design
inputs are decided — `SmallInt`/f32/f64 stay `toHOL` leaves (no structural
story needed, so the float-lander gap is decoupled from the one-way door), and
concrete nat numerals are binary (`nat_binary.rs`), dissolving the perf wall.
The remaining prep is additive: P1 (guard extension — DONE this stage), P2
(facade sweep — in progress), P3 (wasm32 job) — all shrink the eventual swap to
its essential, audited core.
