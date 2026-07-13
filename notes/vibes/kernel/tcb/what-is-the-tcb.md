# What exactly is the TCB?

Human-readable orientation derived from the machine artifacts — the golden
manifests (`docs/deps/{core,eval,builtins}-manifest.txt`) and the audit
(`docs/deps/tcb-audit.json`, from `scripts/tcb-audit.mjs`). Numbers are a
**snapshot (2026-07-11)**; live truth is those files (regenerate: `bun run
deps`; print: `bun run tcb`). If a number here disagrees with the JSON, the JSON
wins.

Companions: [`../kernel-design.md`](../kernel-design.md) (read first before
touching the TCB), [`../closed-world-kernel.md`](../closed-world-kernel.md) (base
design), [`../base-abstraction.md`](../base-abstraction.md) (facade + future
data-shaped TCB), [`soundness-audit.md`](./soundness-audit.md) (deeper audit).

## The TCB in one paragraph

The Trusted Computing Base is the code whose correctness you must believe for a
Covalence theorem to mean what it says. Everything else — front ends, drivers,
tactics, importers, server, CLI — is untrusted: it can only produce a `Thm` by
going through the TCB's audited mint sites, so a bug there yields a *failure to
prove*, never a *false theorem*. The TCB is small, `unsafe`-free, and enumerable:
the base equality kernel plus the HOL rules on it, growing *only* by the
computation tier (`eval`) when you opt into arithmetic/literals.

## Trusted crates (concentric configs)

Measured as nested configurations — you pay only for the tier you use (tests
excluded; lower = more auditable):

| config | crates | files | src-lines | `unsafe` | mint sites | admitted rules |
|---|---|---|---|---|---|---|
| **base** | `covalence-pure-trusted` (`crates/kernel/base/trusted`) | 14 | 1496 | 0 | 24 | — (equality calculus) |
| **base+HOL** | + `covalence-core` (`crates/kernel/hol/core`) | 56 | 6951 | 0 | 24 | 25 (`core`) |
| **base+HOL+eval** | + `covalence-hol-eval` + `covalence-pure-eval` | 90 | 13281 | 0 | 24 | 25 + 17 + 387 |

- **Mint sites stay at 24 across every config.** Adding HOL or eval does *not*
  grow the places a `Thm` is born (`Thm::new`) — HOL/eval rules are *admitted
  rules routed through the base's `apply`/`canon`*, not new mint sites. One mint
  chokepoint, audited once. The base's goal is *fewer* mint sites over time
  (ideally `execute` + instantiation + transport; `base-abstraction.md` §7).
- **Zero `unsafe`** in every trusted config — a CI-tracked invariant.
- The audit also tracks a **`base+HOL (target)`** config (36 files / 5142 lines /
  17 `defs::` coupling vs 29) — the shrink goal as the literal-leaf `defs/`
  residue dies (root `SKELETONS.md` #6).

## The 24 mint sites (where trust enters)

Every `Thm::new` in the base, by file (`tcb-audit.json → mintSiteLocations`):

- **`trusted/src/eqn.rs` (12)** — equality calculus: `refl`, `sym`, `trans`,
  `eq_mp` (Leibniz), `cong_app`, `cong_pair`, `of_ptr_eq`, `lift`, `of_eq`,
  `apply` (the general admitted-rule gate), `canon` (op evaluation).
- **`trusted/src/prop.rs` (5)** — pure bool theory: `and_intro`, `or_inl`/
  `or_inr`, and/or elim, `mp`.
- **`trusted/src/rel.rs` (6)** — positive relation calculus: `execute` (run
  untrusted `f`, mint `⊢ (a,b) ∈ Rel(f)`), `transpose`, `compose`, `meet`,
  `join` (×2). **Positive-only** — no path mints `¬(a R b)`.
- **`trusted/src/matching.rs` (1)** — `apply_rewrite`.

The transport calculus (refl/sym/trans/eq_mp/cong) is **ungated** — sound in
every language. Gated: `apply`/`canon` (checked against `Language::admits` of the
rule's own `TypeId`) and `execute` (checked against `Rel<F>`'s `TypeId`). That
gate — *"a rule fires only in a language that admits it"* — makes the per-language
TCB exactly its admitted set.

## Admitted rules, per language

An admitted rule is a trusted inference the base's `apply`/`canon` will fire for a
given `Language`, pinned in golden manifests (CI fails on drift). Snapshot: core
25, eval 17, builtins 387.

- **`core` (25) — the HOL kernel:** HOL Light's equality core + audited derived
  constructors: `Refl Sym Trans MkComb Abs BetaConv EtaConv Assume EqMp
  DeductAntisym Inst InstTFree Weaken`, the subtype/spec + definitional rules
  `SpecAbsRep SpecRepAbsFwd SpecRepAbsBack SpecAx UnfoldTermSpec Define
  NewTypeDefRule`, the non-computational `UnitEq NatInduct`, nat constructors
  `SuccInj ZeroNeSucc`, and `SelectAx` (ε). `lem`/`false_elim` are **not** here —
  they left the kernel as zero-TCB derived rules in `covalence-hol-eval`.
- **`eval` (17) — computation tier:** per-family computation certificate + toHOL
  rules: `ToHolNatVal PairVal NatAddCert ToHolIntVal ToHolBytesVal ToHolF32Val
  ToHolF64Val NatArithCert SuccCert IntArithCert BytesCert FixedWidthCert
  LitEqCert CoercionCert FloatCert ZeroLitCert HolApp`. Each states an equation
  whose RHS is computed natively then certified; drivers around them
  (`reduce`/`prove_true`/`delta`) are untrusted.
- **`builtins` (387) — native op catalogue** (`covalence-pure-eval`): every
  native computation the kernel trusts, as per-op `Op`+`CanonRule` ZSTs (nat/int/
  bytes + `u8`…`s64` + float conversions). Large because it enumerates the whole
  arithmetic surface; each entry is a single differentially-tested op semantics.

## Term/type shape

`tcb-audit.json → globals`: **19 `TermKind` variants, 7 `TypeKind` variants** —
the fixed grammar. Kept small: connectives (even `T`/`F`) are *defined constants*,
not term-kind variants (`defs/logic.rs`).

## The future: a queryable, cross-referenced TCB doc

Direction: a TCB doc that mirrors the *data* and cross-references it rather than
restating it in prose. The pieces exist:

- **`covalence-tcb-db`** (`crates/app/tcb-db`) round-trips the manifests + audit
  into a STRICT-schema SQLite (`languages`, `language_rules`, `configs`,
  `mint_sites`) with semantic queries ("is `Refl` admitted by `CoreLang`?").
- **The web TCB page** (`apps/covalence-web/src/routes/tcb/+page.svelte`) renders
  `tcb-audit.json` (embedded at build, CI-gated by `deps:check`).
- **The relational base rewrite** ([`../../../design/relational-base-rewrite.md`](../../../design/relational-base-rewrite.md))
  turns axioms into serialized propositions, so a rule row becomes `(relation id,
  schematic proposition)` and the doc can link each admitted rule to its statement.

Target: this prose = **narrative index**, `tcb-db` = **queryable body**, the web
page = **live view**, each admitted rule cross-linked from all three. Until then,
this file is the snapshot; the JSON is truth.
