# OpenTheory import — verifying articles on the native HOL kernel

*Status: working. The **entire OpenTheory standard library verifies** — `cov hol
pkg base` re-checks **1340 theorems** relative to exactly the 3 genuine HOL
axioms (extensionality, choice, infinity), ~46s cached. The article stack
machine, the native kernel backend, the `cov hol` CLI, and the
download+cache+verify-all `bun run opentheory` benchmark are all live.*

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
and the conclusion re-check rejects a mismatched proof. The tests demonstrate
the mechanism end-to-end: the same article exports the same theorem with **1**
assumption (stock) or **0** (with an override that proves the axiom by `REFL`).
Writing the *full* infinity proof over native `nat` (unfolding OpenTheory's
`injective`/`surjective`) is a larger exercise the API now makes expressible.

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
