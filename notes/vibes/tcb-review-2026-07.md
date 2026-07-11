# TCB change review — 2026-07 leaf-elim + base-abstraction + Haskell-SExpr push

For joint maintainer review. Everything below is merged to **local `main`
`8e2e9f13`** (not pushed — the main-only hook + classifier still block me). Three
tracks ran in parallel worktrees, each stage adversarially audited (with a
fix+re-audit loop) before merge; **all stages returned SOUND**, and **EG5 was
correctly NOT executed** (its preflight returned BLOCKED). This doc is the
"go over it together" artifact: what touched the TCB, why each is sound, and
what's still open.

Companion: the running decision log `tcb-holomega-worklog.md`; the EG5 plan
`eg5-preflight.md`; the base-abstraction design `base-abstraction.md` +
`base-api-surface.md`.

---

## TL;DR — the manifest / TCB-shape deltas

| Item | Before | After | Kind |
|---|---|---|---|
| CoreLang admitted rules (`core-manifest.txt`) | 26 | **25** | **FalseElim DELETED** (re-derived) |
| CoreEval admitted rules (`eval-manifest.txt`) | 16 | **17** | **+ZeroLitCert** (transitional, dies at EG5) |
| `TermKind` variants | 18 | **19** | **+Zero** (primitive nat zero) |
| 5 CoreLang rules' INPUT shape | `(Term,…)` | **`(Prem<L>,…)`** | sequent-reshape (A3) |
| core→defs coupling refs | 37 | **29** | connective builders left core |
| base mint sites (tcb-audit.json) | 18 → **24** | — | **NOT new** — see "stale-artifact" note |

**Net trust direction:** CoreLang got **smaller** (a primitive rule removed; T/F
became definitions). One transitional CoreEval rule was added that is **compile-
enforced to die** with the Nat literal at EG5. No `unsafe` anywhere; no new base
(`crates/kernel/base/trusted`) trust.

---

## Track A — leaf elimination + defs-out (kernel; the TCB-bearing track)

### EG3a — `TermKind::Zero` + `ZeroLitCert` bridge  (SOUND)
Commits `b018e0d1`, `9b4cdd99`.
- **Added** `TermKind::Zero`: a primitive nat-zero constructor (type `nat`, printed
  `zero`, `Term::zero()`), rule-free in core (typing arms only; closed leaf in every
  subst walk; `CORE_MANIFEST` and `crates/kernel/base` untouched).
- **One new eval-tier admitted rule `ZeroLitCert`** minting `⊢ IsThm(∅, ⌜zero = ⌜0⌝⌝)`
  — the transitional bridge between the new `Zero` constructor and the old `Nat(0)`
  literal. **Why sound:** `Zero` is a *fresh* constructor with no defining equations,
  so `zero ↦ 0` is a consistent standard-model interpretation and the bridge is a
  *conservative definitional axiom*. It is deliberately the object-level `IsThm`
  shape, **never a base `Eqn`** (the two Terms are structurally distinct, so a base
  definitional equation would be false). `Lit::from_term` returns `None` for `Zero`
  so cert decoders can't mint a contradicting disequality. CoreLang **refuses** the
  mint (TypeId gate + pinned negative test). **It is compile-enforced to be deleted
  with the Nat literal at EG5.**
- Zero-form freeness (`⊢ ¬(zero = succ n)`) is **derived** through the bridge
  (zero new axioms); `ZeroNeSucc`/`NatInduct` keep literal conclusions for now.

### EG3b — T/F as defined constants; FalseElim deleted  (SOUND, 1 fix round)
Commits `995ea8c2`, `ac3890a1`, `867edc73`, `a15dd40e`, fix `440968db`.
- **`T`/`F` are now DEFINED constants** — `tru ≡ (λp.p)=(λp.p)`, `fal ≡ ∀p:bool.p`
  as let-style TermSpec catalogue definitions (semi-trusted defs tier; defining
  equations come from the already-admitted `UnfoldTermSpec`). **`⊢ T` now derives at
  pure `Thm<CoreLang>`**, and the whole derived connective calculus dropped from
  CoreEval to CoreLang tier.
- **`FalseElim` DELETED from the kernel** (`core_rules!`), coreManifest 26→25, golden
  regenerated. Ex-falso is now the derivation *unfold-`fal` + ∀-elim*, re-exposed as
  `DerivedRules::false_elim` (drop-in for consumers). **Zero new axioms.**
- Coexistence with the literal machinery is fully derived: `⊢ T=⌜T⌝` and `⊢ F=⌜F⌝`
  proved in `eval/boolean.rs`; the hard half (literal ex-falso `{⌜F⌝}⊢p`) routes
  through **nat freeness** (`LitEqCert` `⌜0⌝≠⌜1⌝`, `zero_ne_succ`, derived `not_elim`).
  This is *why* FalseElim deletion + the not-body flip had to land in one stage.

### A3 — defs/ out of core; 5 rules reshaped  (SOUND) — **most scrutiny-worthy**
Commits `ab2792ee`, `1a293490`, `d8f4202e`.
- **Five CoreLang rules changed INPUT shape** (`crates/kernel/hol/core/src/thm/rules.rs`):
  `SelectAx`/`SpecAx`/`SuccInj`/`ZeroNeSucc`/`SpecRepAbsFwd` now take a `Prem<L>`
  (proven-premise) instead of raw `Term`s. Manifests **byte-identical** (25/17 — same
  rules, same names, same count; only the Rust input types changed). Public API
  renames (`select_ax→select_intro`, `zero_ne_succ→zero_eq_succ_elim`, …).
- **`ZeroNeSucc` became a genuine ex-falso sequent rule**: `Γ⊢0=succ n ⇒ Γ⊢q` for any
  bool `q`. **Why sound (audit):** every reshaped rule bottoms out in the shared
  `seq`/`check_sequent` floor that bool-typechecks conclusion **and** hypotheses — so
  the arbitrary `q` is type-gated, and the ex-falso conclusion *always carries the
  inconsistent `0=succ n` hypothesis*, closing the empty-context forgery path. Each
  new sequent form is **inter-derivable with its old axiom form** (no proof-strength
  change); `Prem<L>` is tier-parameterized (no CoreEval→CoreLang laundering).
- Connective builders (`imp/and/or/not/exists/forall`) **left `core::hol`** (now
  defs-free) → public `covalence-hol-eval::hol`. Coupling **37→29** (target 25→17 in
  the minimal config). `SpecRepAbsBack`/`NewTypeDefRule` stay connective-built with
  in-code justifications (honest floor until L4/EG5).

### EG5 preflight — **BLOCKED** (EG5 not executed)
Doc `notes/vibes/eg5-preflight.md` (`6983bffb`). Two named missing prerequisites:
1. **Float symbolic-lander gap** — only `add`/`mul` landers exist; unaries/comparisons/
   conversions have none (the roadmap's own hard go/no-go gate, still open).
2. **SmallInt + f32/f64 structural replacement is unspecified** — `TermKind::SmallInt`
   is on the delete list and the `ToHolF32/F64Val`/`FixedWidthCert`/`FloatCert` certs
   are made of it, but **there is no structural target**: `uN.fromNat` unary towers
   are infeasible at 2³²/2⁶⁴ magnitudes. **This is a genuine maintainer design fork**
   (new structural `uN` rules over symbolic nat leaves vs. per-family symbolic
   conclusions colliding with the EG4 `Dyn` wall vs. binary numerals).
- Plus a **perf wall**: unary numerals make char/utf8/utf16/nat_parse proofs O(value)
  per literal (0xD800 ≈ 55k-node towers) on suites EG3b already slowed 1.5–1.7×.

**Latent-hardening finding (act before EG5, not currently exploitable):** the
`tohol_unfolding_rules_are_exclusive` guard (`eval/src/rules.rs`) is **nat-only** —
co-admitting `ToHolIntVal + ToHolIntMk` would be the same base-tier `sym+trans ⊢False`
class, currently *unguarded*. Not exploitable today (`ToHolIntMk` doesn't exist), but
P1 = extend the guard to all five families is recommended now.

**Recommended unblock prep (all additive, all shrink the eventual swap):** extend the
exclusivity guard to 5 families; the ~220-site downstream facade sweep onto `mk_*/as_*`;
stand up a **wasm32 differential CI job** (the `nat.shr` usize-narrowing divergence
class — a wasm32-only `⊢False` invisible to 64-bit CI — is the specific hazard for the
new structural `Nat→succ-tower`/`Bytes→cons` builders).

---

## Track B — Haskell ⇒ S-expressions ⇒ backend  (SOUND, zero-TCB)
Commits `a525828c`…`a5e9cdc7`.
- First-class **`SExpr` IR** (`src/sexpr.rs`): Sym/Nat/Str/List + canonical text
  printer & parser (the third-party interchange), round-trip tested incl. 2¹²⁸.
- **Nat literals are covalence `Nat`** (per your correction) via a new
  kernel-independent `covalence-types` dep — the `u128` cap is gone; the parser
  accepts arbitrarily large literals.
- The pluggable seam moved to a **`Realize` trait over `SExpr`** (succeeds the
  AST-shaped `Lower`); Text/Peano/NoLit backends reimplemented; the HOL backend
  re-routed **Haskell → SExpr → carved sexpr kernel Term**.
- **Third-party tests**: hand-written S-expr *text* (never touching Haskell syntax)
  reaches the same backends as the Haskell route; print→parse round-trips equal
  direct lowering. Flagship `init_dialect.rs` lowers an init-flavored module
  (compose/const + Church option) to exact interchange text **and** kernel Terms.
- **Also fixed a pre-existing RED deps gate on main**: the earlier `77f66005` haskell
  commit had tripped the purge-ratchet (`term-literal-ctors 0→5`); atom payloads now
  route through the `mk_blob` facade (count → 0, no golden bump). **main's `bun run
  deps` was red before this session's merges; it is green now.**

## Track C — base abstraction seam + SQLite TCB dump  (SOUND, zero-TCB)
Commits `1a92775e`…`76c4e553`. `crates/kernel/base/trusted/**` **byte-identical to main**.
- `base-api-surface.md`: inventory — only `covalence-core`/`covalence-hol-eval`
  import `covalence_pure`, consuming a **small stable kernel** (Thm + calculus,
  apply/canon, Language/Manifest/Rule, the Expr/Op/App/Val/Eqn vocabulary). The
  `of_eq` family, `Ref`/`Dyn`, MatchApp, the rel calculus, and the HOL-ω reflection
  have **zero external consumers** → the refactor-freedom set.
- `covalence_pure::api` — curated re-export facade with a stability CONTRACT
  docstring (type-identity pinned by test). Zero behavior change.
- `covalence_pure::algebra::CertificateAlgebra` — a GAT certificate-algebra trait
  (mint-by-admitted-rule / equality transport / positive relation facts), implemented
  for the current kernel by delegation; module docs give the **`RelKernel` recipe**
  for the future relations base (`execute` stays primitive; `apply` becomes
  schematic-axiom instantiation; `canon` derives via a `Computation(i,o) ⟹ f(i)=o`
  functionality axiom) — the seam for "all computation = untrusted relations".
- **`covalence-tcb-db`** (`crates/app/tcb-db`): zero-TCB SQLite dump of the TCB *shape*
  (languages/rules from the golden manifests; configs + mint sites from
  tcb-audit.json) via the `covalence-sqlite` wrapper; round-trip + semantic SQL
  assertions ("all mint sites inside `trusted/src`"). The SQLite-dump-a-TCB goal.

---

## Two "not-new-trust" clarifications (important for the audit)
1. **`tcb-audit.json` base numbers jumped** (files 9→14, mintSites 18→24, LoC 934→1496)
   **during this session but measure ALREADY-LANDED work** — the `rel.rs` positive
   calculus (`execute`/`transpose`/`compose`/`meet`/`join`) and B-K1..3. Earlier
   tracks had **skipped `bun run deps`**, so the checked-in artifact was stale; the
   regen is catch-up, **not new trust added by these tracks**. Worth confirming those
   24 mint sites are the ones we expect.
2. A pre-existing **`lang → kernel` cross-group edge** (covalence-haskell's optional
   `covalence-init` dep under the `hol` feature) was surfaced by the graph regen —
   flagged for your call, as a new cross-group edge is a deliberate-decision artifact.

## EG5 status update (2026-07-11) — unblocked in design, prep landed, execution is bigger than sketched

**Maintainer decisions received & recorded** (resolve the two preflight blockers):
nat's structural target is a **binary** (log-sized) encoding via `nat_binary.rs`'s
`double`/`succ` (no unary perf wall); **SmallInt becomes a `toHOL` leaf**
(`ToHolSmallInt`, no structural rule, so leaf-only + deletable), and f32/f64 ride
along as SmallInt bit-patterns. `eg5-preflight.md` is now UNBLOCKED-WITH-DECISIONS.

**Prep landed (additive, merged, gate-green, manifests byte-identical):**
- P1 — the `tohol_unfolding_rules_are_exclusive` guard extended to a per-family table
  (nat/int/bytes; smallint/float deliberately excluded as leaf-only). Test-internal,
  no rule/manifest change.
- P2 — facade sweep: init literal-ctor sites routed through the eval `mk_*/as_*`
  facade (`term-literal-ctors` 72→6; 6 subtle sites recorded).

**S1 (bytes swap) attempted → honest-stop, no TCB change.** The finding (worth your
eyes): the preflight's per-family swap sketch **underestimated the work**. Each swap
is genuinely all-or-nothing (the guard forbids an additive intermediate that keeps
`*Val`), and the *honest* structural target requires machinery that **doesn't exist
yet** — `bytesConsNat`/`bytesAt` are declaration-only, and the `Blob ↔ list u8`
bridge + list-recursion lemmas are a real init-level proof development. A sound swap
therefore means, per family: (1) complete the structural HOL theory, (2) flip the
**whole cert family** (`BytesCert`/`LitEqCert`/`CoercionCert` + `Lit::to_term/from_term`
+ ~17–23 downstream sites) to a structural RHS, (3) discharge a **new
structural-injectivity audit obligation** (`⟨struct a⟩=⟨struct b⟩ ⇔ a=b`). Int (S2)
has the identical structure; nat/smallint differ (binary / leaf). This is a
multi-stage, per-family effort — not the quick swaps the sketch implied.

## Open items for us to decide together
- **EG5 design fork**: the SmallInt/f32/f64 structural target + the unary-vs-binary
  numeral decision (the perf wall) — EG5 is gated on this.
- The **A3 rule reshape** (Prem-carrying `ZeroNeSucc` ex-falso, the 5 sequent forms) —
  audited SOUND, but it's a real CoreLang shape change worth your eyes.
- Whether to do the **P1/P2/P3 EG5 prep** now (guard-to-5-families, facade sweep,
  wasm32 CI) — all additive.
- Consuming the Track C **facade/algebra** in core/eval (deferred; migration order in
  `base-abstraction.md`).
