# OpenTheory import — verifying articles on the native HOL kernel

*Status: working. The **entire OpenTheory standard library verifies** — `cov hol
pkg base` re-checks **1340 theorems**, ~46s cached. By default it verifies
relative to OpenTheory's three HOL axioms; with `--native-axioms` all three
(infinity over `nat`, extensionality, choice) are **proved natively in
covalence's kernel**, so `base` verifies relative to **zero** axioms. The
article stack machine, the native kernel backend, the matching framework, the
`cov hol` CLI, and the download+cache+verify-all `bun run opentheory` benchmark
are all live.*

## What this is

`covalence-opentheory` reads [OpenTheory](http://www.gilith.com/opentheory/)
articles — the interchange format HOL Light, HOL4, and ProofPower export proofs
to — and replays them against our HOL kernel, re-checking every inference. The
crate already had the format machinery (article reader, stack machine, `.thy`
package/dependency resolution, an HTTP+disk-cache fetcher); what the kernel
rewrite left missing was a *backend*. This adds it.

## Architecture: the trait is the swap seam

```
article (.art)  ──reader──▶  ArticleInterp<K: HolLightKernel>  ──▶  K
                             (generic stack machine)                 = NativeOt today
```

- **`HolLightKernel`** (`crates/kernel/hol/traits`) is the arena-style, NameId-
  handle interface OpenTheory-shaped backends want: the 10 primitive rules +
  `deduct_antisym`, parallel `inst`/`inst_type`, `define`,
  `new_basic_type_definition`, plus validated constructors.
- **`NativeOt`** (`crates/proof/opentheory/src/native.rs`, feature `native`)
  implements it over `covalence-core`'s value-typed kernel. Every rule delegates
  to an already-audited `covalence-core` / `covalence-hol-eval` operation.
- The generic `ArticleInterp` never mentions the backend, so the *next* north
  star — an internal/object-level HOL (HOL-in-Metamath, or another HOL we prove
  equivalent to it) — is **just another `HolLightKernel` impl**. Benchmarking the
  two against the same article corpus is then an apples-to-apples comparison.

## Trust: zero TCB beyond core HOL

Every theorem `NativeOt` produces is minted by a `covalence-core` rule; the
module declares no `Language` rule and cannot reach `Thm`'s private mint. Two
design points keep it honest:

- **Axioms are hypothesis-tracked, never minted.** `new_axiom(p) = Thm::assume(p)`
  → `{p} ⊢ p`. A theorem that uses an axiom carries the axiom term as a
  hypothesis; the honest reading is "verified *relative to* these assumptions".
  (Contrast OpenTheory's own `axiom`, which asserts a hyp-free `⊢ p` — that would
  be new TCB.) So `bool` verifies with the extensionality + choice axioms
  reported as its two unsatisfied assumptions, exactly as it should.
- **Opaque constants/types are conservative or uninterpreted.** The only
  primitive constants are `=` (`Term::eq_op`) and `select` (`Term::select_op`,
  recognised type-directedly: any *undefined* constant of shape `(α→bool)→α` is
  the unique primitive `select`). Everything else enters via
  `defineConst`/`defineConstList`/`defineTypeOp` → `Thm::define` /
  `Thm::new_type_definition`. An unregistered type constructor (e.g. `ind`, the
  infinity type) is auto-registered as an opaque `Tycon` of the observed arity —
  sound, since names are an efficiency token, not a soundness one.

## The three subtleties that took work

1. **Simultaneous substitution from single-variable primitives.** OpenTheory
   `subst` is simultaneous; core exposes single-variable `inst`/`inst_tfree`.
   `NativeOt` does a two-pass fresh-rename (old→fresh, then fresh→new), avoiding
   article-controlled name collisions. The swap case `{x↦y, y↦x}` is a unit test.

2. **`defineTypeOp` v5 vs v6 shapes.** The backend returns the v5 laws
   `⊢ abs (rep a) = a` and `⊢ (φ r) = (rep (abs r) = r)`. For version-6 articles
   the interpreter reshapes them into the λ-abstracted forms the standard
   specifies — `⊢ (λa. abs (rep a)) = (λa. a)` and
   `⊢ (λr. rep (abs r) = r) = (λr. φ r)` — via `abs_rule` (+ `sym`). Getting this
   wrong silently produces wrong-shaped theorems downstream; it was the primary
   blocker for `unit-def` and everything above it.

3. **Polymorphic-axiom instances as hypotheses.** Because axioms are
   hypothesis-tracked, a polymorphic axiom assumed at `'A` but used at, say,
   `(('A→bool)→bool)` propagates as a *type instance* of itself onto the export.
   The `thm` command tolerates a hypothesis that is a type instance of a tracked
   axiom (new `HolLightKernel::discharges_as_axiom` hook + a term type-instance
   matcher in `NativeOt`) — sound, because it is exactly `INST_TYPE` of the axiom.

## Custom handling: checking articles against a native theory

By default an `axiom` command is hypothesis-tracked, so `base` verifies
*relative to* the three HOL axioms. But a backend whose own logic already has
the relevant structure can discharge them — the `HolLightKernel` trait carries
one **optional** hook (default `None` reproduces stock behaviour):

```rust
fn prove_axiom(&mut self, tm: Self::Term) -> Option<Result<Self::Thm, HolError>>;
```

When an `axiom` fires, the interpreter offers the statement here first; a
returned proof (whose conclusion it re-checks against `tm`) discharges the
axiom, and it is *not* added to the assumption set — so downstream theorems
come out axiom-free. `NativeOt` exposes a richer, injectable configuration via
the `NativeOverrides` trait (with a fluent `OverrideMap` for the common case):

- `prove_axiom(stmt)` — a native proof of an axiom (e.g. OpenTheory's infinity
  for a native infinite type, or a lemma from a different construction);
- `resolve_type(name, args)` — map an OpenTheory type operator to a native type
  (e.g. `ind` → native `nat`), consulted in `opType`;
- `resolve_const(name, ty)` — map an OpenTheory constant to a native term,
  consulted in `constTerm` *before* the article's own definitions (so an
  override wins over a `defineConst` — the hook for "swap out this natural
  numbers / this lemma source").

```rust
let ov = OverrideMap::new()
    .type_("ind", native_nat_ty())          // reinterpret the infinity type
    .axiom(|stmt| prove_infinity_for_nat(stmt));   // discharge infinity
let kernel = NativeOt::new().with_overrides(ov);
```

Everything is built through `covalence-core` / `covalence-hol-api` directly, so
an override cannot forge a theorem — a returned `Thm` is a real kernel theorem,
and the conclusion re-check rejects a mismatched proof.

### Matching tactics (`matching.rs`) — the reusable bridge

The gap the override has to cross is *representation*: an OpenTheory `axiom`
statement is fully **δ-inlined Church-encoded** HOL (0 `Def`s, 0 `Spec`s, ~113
nested `Abs`), whereas a native proof is stated with the kernel's *definitional*
connectives (`∀ ∃ ∧ ¬ ⟹` as `TermSpec` leaves). Bridging them is a reusable
concern, so it lives in a framework generic along two axes — stable as the
internal logic evolves:

- **`MatchLogic`** — the HOL representation being matched (the "thing being
  matched"). `HolMatch` implements it for covalence-HOL; a metamath-HOL backend
  would add its own. It supplies α-equality, `concl`/`eq_rhs`,
  `refl`/`sym`/`trans`/`eq_mp`, and β/δ normalisation as `⊢ t = nf` theorems.
  The δ-normaliser unfolds *every* connective spec via congruence **without**
  β-reducing — reaching exactly the article's inlined shape.
- **`MatchStrategy`** — how two terms are recognised equal and a proof carried
  across: `Structural` (α), `UpToBeta`, `UpToDelta`, `UpToBetaDelta`. A strategy
  defines only `normalize`; the shared `transport` composes the two normal-form
  equations (`⊢ native = nf`, `⊢ target = nf`) and discharges with `eq_mp`, so
  the result is a real kernel theorem of exactly `target`.

### The three axioms, discharged (`axioms.rs`)

Each of OpenTheory's HOL axioms is a theorem of covalence's kernel:

- **infinity** — `prove_infinity` proves `⊢ ∃f:nat→nat. injective f ∧
  ¬surjective f` (witness `succ`; injectivity is `succ_inj`, non-surjectivity
  from `zero_ne_succ`). Mapped in via `ind→nat`.
- **extensionality** — `prove_extensionality` proves `⊢ ∀f. (λx. f x) = f` (the
  η axiom) via `eta_conv`.
- **choice** — `prove_choice` proves `⊢ ∀P x. P x ⟹ P (ε P)` via `select_ax`
  (Hilbert choice is already a kernel rule).

`standard_axioms()` bundles all three into one `OverrideMap` (proofs built once;
each incoming axiom `UpToDelta`-matches against them). `cov hol pkg
--native-axioms base` then verifies all 1340 theorems relative to **zero**
axioms.

The one subtlety worth recording: each proof's predicate must match
OpenTheory's *exactly* so the δ-normal forms are α-equal — same `injective` /
`surjective` definitions, same conjunct order, and the `not` **connective** for
negation (`imp(p, F)` would δ-unfold to a different, wrapper-free shape). The
same trait seam is exactly what a swap-in "different natural numbers / lemma
source" would use.

## Numerals (the "for now")

No kernel numeral literal is ever constructed. The OpenTheory `std` library
*defines* naturals and their binary `bit0`/`bit1`/`zero`/`suc` numerals inside
the articles themselves — already in double/succ form — so `natural-def`
verifies through ordinary `defineConst`/`defineTypeOp` with **zero extra TCB**.
A later backend may instead map `Number.Natural.*` onto `covalence-init`'s nat
theory (or the internal HOL), which is where the trait seam earns its keep.

## Running it

```sh
cov hol check [--stats] file.art …            # standalone articles
cov hol pkg  --dir <vendored-dir> … <pkg…>    # offline packages + deps
cov hol pkg  --repo <url> --cache <dir> <pkg…>  # fetching (default gilith repo)

bun run opentheory            # download + cache + verify `base` (online)
bun run opentheory:offline    # verify the vendored assets (no network)
```

`bun run opentheory` fetches the whole stdlib (once, cached) and verifies
`base` — 1340 theorems. The online resolver turns a bare package name (or bare
`.thy` `requires:`) into its latest version by reading the repo's
`?pkg=<name>` package-info page; `CachingUrlResolver` resolves from the on-disk
cache first, so re-runs need no network. Offline (`--offline`), ~20 packages
verify from the vendored subset.

## Known limitations (see `crates/proof/opentheory/SKELETONS.md`)

- **`.int` interpretation files** are parsed but not applied (deep NameId
  renaming of theorem terms), so `word`↔`byte`-style renaming packages will
  over-report assumptions. `base` verifies whole regardless.
- **Offline vendored corpus** is a subset; the full stdlib needs the online
  (fetching) path.

## Next

- Internal-HOL backend: a second `HolLightKernel` impl targeting HOL-in-Metamath
  (or an internal HOL proved equivalent), so importing an article *proves the
  statement in internal HOL* rather than native HOL. Same corpus, same CLI, a
  new impl — and a genuinely interesting benchmark pair.
