# OpenTheory import — verifying articles on the native HOL kernel

*Status: working. 20 stdlib packages / 428 theorems verify offline with zero
verification failures; the article stack machine, the native kernel backend,
the `cov hol` CLI, and the `bun run opentheory` benchmark are all live.*

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

Offline today: `bool-def`, `bool`, `unit-def`, `function`, `pair-def`,
`axiom-infinity`, `natural-def`, … — 20 packages, 428 theorems, and the only
failures are missing vendored packages, never verification errors.

## Known limitations (see `crates/proof/opentheory/SKELETONS.md`)

- **Online version resolution.** `UrlResolver` can't turn a bare package name
  (or bare `.thy` `requires:`) into a version without a repo index; versioned
  names fetch fine. This is the one thing between the online benchmark and the
  full stdlib (incl. the `defineConstList` packages `list`/`option`/… and
  `base`). Fetch the repo's package/version index, or seed a name→version map.
- **`.int` interpretation files** are parsed but not applied (deep NameId
  renaming of theorem terms), so `word`↔`byte`-style renaming packages will
  over-report assumptions.

## Next

- Internal-HOL backend: a second `HolLightKernel` impl targeting HOL-in-Metamath
  (or an internal HOL proved equivalent), so importing an article *proves the
  statement in internal HOL* rather than native HOL. Same corpus, same CLI, a
  new impl — and a genuinely interesting benchmark pair.
