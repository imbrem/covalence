+++
id = "N0017"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-13T20:42:09+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# SHA-256 round — the universality keystone

**SKETCH (design probe).** The smallest demo that, if it lands, exercises *every*
mechanism of the verified-WASM + import-fuel thesis end-to-end, on the cheap import
(set.mm — no Dedukti, no model beyond a definitional one). Instantiates
[`../../vision/roadmap.md`](../../vision/roadmap.md) Phase C/D and realizes the assumption-ledger of
[`../tcb/soundness-audit.md`](../tcb/soundness-audit.md) §4. Companion to
[`../../vision/VISION.md`](../../vision/VISION.md) §3 (oracles as theorems) and
[`../substrate-rewrite.md`](../substrate-rewrite.md) (the replacement substrate
this should eventually exercise).

## The keystone, and what it falsifies

**Prove a WASM implementation of one SHA-256 compression round equal to the FIPS
180-4 spec, with the hard algebra step discharged by a fact imported from set.mm.**

One round — not all 64, not the message schedule. Full SHA-256 = compose the round
64× then fold the schedule (scale, not new mechanism). The round is the slice where
every load-bearing claim is either demonstrated or breaks. If it lands, these are
validated together:

1. **Verified WASM (the engine).** We can state `exec_wasm(B, in) = spec(in)` and
   discharge it — WASM enters as a *theorem*, not a trusted oracle.
2. **Import delivers fuel (the universality bet).** A theorem we did *not* prove — a
   modular-arithmetic ring fact in set.mm — closes a step we could not otherwise.
3. **Transport works.** A set.mm statement (over `ℤ mod 2^32`) re-stated and used in
   the WASM-domain theory (over `u32`) soundly.
4. **The ledger is honest.** The final `Thm` carries `Axiom(Con(GT))` (set.mm's base)
   + `Obs(T_wasm)` (WASM semantics) + the instruction-level denotation facts.

If it doesn't land, the keystone tells us *which* broke and why (§6).

## The spec — one round (FIPS 180-4)

Given 8-word state `(a,b,c,d,e,f,g,h)`, schedule word `Wₜ`, round constant `Kₜ` (all
`u32`, arithmetic mod `2^32`):

```
Ch (x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)
Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)
Σ0(x)      = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)
Σ1(x)      = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)
T1 = h + Σ1(e) + Ch(e,f,g) + Kₜ + Wₜ        (mod 2^32)
T2 = Σ0(a) + Maj(a,b,c)                      (mod 2^32)
a' = T1 + T2   e' = d + T1   b'=a c'=b d'=c f'=e g'=f h'=g
```

The keystone proof obligation is the **`T1` add-chain** (the densest part, the
natural home of the set.mm fact); `T2`, `Maj`, and the register shuffle are strictly
easier and follow the same pattern. Prove `T1`; the rest is composition.

## The WASM implementation

Representative bytecode for `T1` (`i32.add` wraps at `2^32` by spec, so it *is*
mod-`2^32` addition; `i32.rotr`/`xor`/`and`/`const` are spec'd bitwise ops):

```wat
;; Σ1(e) = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25)
local.get e i32.const 6 i32.rotr
local.get e i32.const 11 i32.rotr i32.xor
local.get e i32.const 25 i32.rotr i32.xor          ;; ⟶ Σ1(e)
;; Ch(e,f,g) = (e & f) ^ (~e & g)
local.get e local.get f i32.and
local.get e i32.const -1 i32.xor local.get g i32.and i32.xor ;; ⟶ Ch
i32.add  local.get h i32.add  local.get K i32.add  local.get W i32.add
;; ⟶ T1  (left-nested: ((((Σ1+Ch)+h)+K)+W))
```

### The prerequisite — `T_wasm` (HONEST: unbuilt, likely the real long pole)

To state any of this we need a WASM operational semantics `T_wasm` giving each `i32`
word instruction a denotation: `⊢ ⟦i32.add⟧ = λa b. (a + b) mod 2^32`, etc. **This
does not exist today.** `covalence-spectec` is an AST + *grammar* wrapper only (binary
parsing, regular-grammar fragments); no operational-semantics theory (its SKELETONS
flags the CFG stratum as the headline gap). The refactor-plan's `covalence-eval` (WASM
acceleration) is Phase E — *after* the product.

So the keystone's *enabling* work is not the import — it is **standing up a minimal
`T_wasm` for the `i32` word-op fragment** (add/sub/mul, and/xor/or, shl/shr/shr-s,
rotl/rotr, const, local get/set). A real, bounded formalization, and where the effort
and time actually sit. Treat the import as the *cheap* thing being validated once
there is an engine to burn fuel in.

The carrier it lands into *does* exist: `u32` is already a `defs` type
(`crates/covalence-core/src/defs/bits.rs` — a subtype of `bits := list bool` carved
by a length-32 predicate). So `T_wasm`'s target type is in place.

## The proof, factored

**Obligation:** `⊢ ∀ (a..h,K,W : u32). exec_wasm(B, (a..h,K,W)) = T1_spec(a..h,K,W)`.

Symbolic-execute `B` under `T_wasm` to a concrete bitvector expression `E_bytecode`;
the obligation reduces to `⊢ E_bytecode = E_spec`, closed by equational rewriting in
three kinds of step:

| Sub-lemma | Discharged by | Mechanism |
|---|---|---|
| each `i32.*` = its bitvector op | `T_wasm` denotation rules | WASM semantics |
| `((((Σ1+Ch)+h)+K)+W) = h+Σ1+Ch+K+W` (any paren/order) | **set.mm modular-`2^32` ring facts** (assoc+comm of `+ mod 2^32`) | **IMPORT + transport** |
| `Σ1`, `Ch` unfold to `⊕/∧/¬/ROTR` form | bit-list lemmas over `u32`, or set.mm `bits` | native / second import |
| register shuffle / `T2` | trivial rewrites | kernel tactics |

The **bold row is the keystone of the keystone**: the one step that genuinely needs
an *imported* fact — assoc/commutativity of mod-`2^32` addition is exactly what you do
not want to re-prove by hand, and exactly what set.mm has sitting proven.

## The import + transport (the fuel)

**The imported fact.** The WASM chain adds left-to-right; the spec writes `T1` as a
flat 5-term sum. Closing the gap needs **`+ mod 2^32` is associative and
commutative** — the modular-arithmetic ring/group structure on `ℤ/2^32ℤ`. set.mm
proves modular arithmetic is a commutative ring (`modaddmod`-style reassociation).
Locate the exact `*.mod` ring lemma at execution time (don't assume the label); the
load-bearing claim is only that *such* facts exist there, which they do.

**Transport (definitional-tier — why set.mm is the right validator).** set.mm states
the fact over integers mod `2^32`; the WASM-domain theory over `u32 = bits` of length
32. Not syntactically the same carrier, so transport is real — but the model is
*definitional*: the bits ↔ integer-value correspondence (`val(bs) = Σ 2ⁱ·bsᵢ mod
2^32`) is a bijection, and set.mm also has bit machinery (`df-bits`). So Tier-3
faithful transport is *cheap here*: prove `val : u32 ↔ ℤ/2^32ℤ` a ring isomorphism
(bounded, over the 32-bit list), then every set.mm ring fact transports through it —
one bridge theorem, many facts ride. Contrast the future CIC/HOL import (`CIC ↪ GT`,
a real relative-consistency proof, *not* definitional): set.mm is the cheap validator
precisely because its carrier aligns with `u32` by a bijection.

**The three tiers on this fact:**

1. **Assume.** Take "mod-`2^32` `+` is assoc/comm" as a scoped `Postulate`, justified
   by `Con(GT)`. Cheapest; no proof object. Enough to *close the round* on day one.
2. **Re-check.** set.mm *has* the proof term (`metamath::verify_all` checks all of
   set.mm in ~1 min). `mm_import`/`mm_replay` construct `⊢ Derivable ⌜S⌝`; lift to the
   ring fact (the schema-database replay, roadmap Phase B follow-on).
3. **Faithful transport.** Prove `val` a ring iso; the set.mm lemma becomes a
   first-class `u32` theorem.

**The ledger.** The final `Thm` carries `Axiom(Con(GT))` + `Obs(T_wasm)` + the
`T_wasm` instruction denotations. A consumer who distrusts `T_wasm` sees it and gets
nothing; one who accepts it gets a proven round. `soundness-audit.md` §4 made
operational — and it makes the *import* honest: the set.mm dependency is a named,
dischargeable assumption, not silent trust.

## The demo a stranger sees

```sh
$ cov check sha256_round.cov
proven: round_t1  ⊢ ∀ a..h K W. exec_wasm(0x<B_hash>, …) = T1_spec(…)
  provenance: Axiom(Con(GT))   ← set.mm lemma "mod-2^32 add is a comm ring"
              Obs(T_wasm)       ← i32 word-op fragment
```

Pitch: *"this WASM is proven to implement the SHA-256 round, and the algebra that made
the proof close was not written here — it was imported from set.mm."*

## The honest risks this is designed to surface

Each should change the plan if it fires:

1. **`T_wasm` is the long pole, not the import.** If standing up even the minimal
   `i32` fragment is large, WASM semantics is the bottleneck and "import is cheap" is
   correct but *not schedule-determining*. Size this first.
2. **The fuel may split across sources.** set.mm's strength is the *additive* ring
   facts; the *bitwise* facts (rotation, XOR/AND tautologies) may be more naturally
   native to `u32`-as-`bits` (structural induction on the list). If so, SHA-256's real
   imported fuel is narrow (add-reassociation only), and a more arithmetic-heavy WASM
   target (modular exponentiation, a small bignum) would exercise import harder.
3. **The best free word-arithmetic library may be HOL's, not set.mm's.** HOL
   Light/HOL4 have the canonical bitvector/`words` theory. If set.mm's modular fuel is
   thin at the right grain, the keystone naturally pulls in `hol.mm` as a second
   (still-cheap) import.
4. **Native-vs-imported fraction.** If the round is 90% hand-authored `.cov` tactics
   and 10% imported fact, the universality thesis was not really tested. The goal is a
   step that *cannot* close without the import.
5. **`.cov` authoring perf.** The round is authored in `.cov`, the kernel-tactic path
   that blows up without hash-consing. set.mm's ~1-min number is the wrong regime to
   cite. If authoring is painfully slow, revisit the hash-consing thread — but only if
   the proof is hand-heavy (see #4).

## Sub-steps (cheapest-falsifying-first)

0. **Size `T_wasm`.** Confirm nothing exists; scope the minimal `i32` word-op
   fragment. *The schedule-determining unknown.*
1. **Spec as a `.cov` `#thy`** — `T1_spec` (+ `Ch`/`Σ1`/`Maj`) over the existing
   `defs/bits.rs` `u32`. State the obligation.
2. **`T_wasm` denotation lemmas** for the round's instructions (`add`, `rotr`, `xor`,
   `and`, `const`, `local.get`).
3. **The keystone-of-the-keystone:** import *one* modular-add ring fact from set.mm,
   transport it to `u32` via the `val` iso, use it to close the add-chain
   reassociation. If this works, the thesis is demonstrated.
4. **Complete the round** (`Σ1`/`Ch` unfold, `T2`, shuffle). Composition only.
5. **(Later, out of scope)** 64-round fold + message schedule; `Kₜ` as a verified
   lookup; the full `compress` oracle as a license-to-run.

## Open questions

- Does the `covalence-pure` executor base want to *own* `T_wasm`, or does it live in
  `covalence-eval` / a `wasm/` domain group? Keep placement consistent with the
  observer→pure rewrite.
- Ship the round at tier 1 (assume the ring fact, `Con(GT)` in the ledger) to land
  fast, then upgrade to tier 2/3? Recommend yes — the ledger makes tier-1 honest.
- Is `val : u32 ↔ ℤ/2^32ℤ` already partially proven in `defs/bits.rs`, or greenfield?
  Check before sizing step 3.
- For the additive step, a QF_BV SMT discharge (`(#by (smt))`) would also close it —
  but *bypasses* the import thesis. Keep SMT as the fallback sledgehammer, not the
  primary path.
