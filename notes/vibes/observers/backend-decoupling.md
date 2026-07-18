+++
id = "N002P"
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

# Backend decoupling — the `covalence-hol-api` trait surface

*Agent-authored design note (TRACK A). Status: first slice landed.*

## The problem

Almost every consumer of the HOL tower builds terms and theorems by naming
`covalence_core::Term` / `TermKind` constructors directly. The concrete kernel
representation (locally-nameless `TermKind` with `Nat`/`Int`/`Bytes` literal
leaves, `Thm<L>` tiers) is therefore hard-wired into thousands of call sites.
A serious backend change — an arena/id-typed kernel for perf, an
internal/object-level HOL for the "prove induction *inside* HOL" goal, a
different literal representation, or the planned relations base
(`base-relcalc-holomega-design.md`) — would mean editing every consumer, not
one adapter.

The inventory below (regenerate with `bun scripts/backend-coupling.mjs`) sizes
it: `Term::` / `TermKind::` sites per crate, src only. The impl crates
(`kernel/hol/core` is the backend; `kernel/hol/init` + `kernel/hol/eval` host
the trait impl + the theorem catalogue) are *expected* to stay high; the number
to watch is the **consumer total**.

## The shape

Follow the same spirit as `covalence_pure::api` / `covalence_pure::algebra` one
tier up: a curated, trait-backed consumer surface that the backend refactor
"must not move". The new crate is **`covalence-hol-api`**
(`crates/kernel/hol/api`), a pure consumer layer *above* the kernel — zero TCB
delta, no admitted rule, golden manifests byte-identical.

It exposes two traits:

- **`Hol`** — the value-typed HOL Light surface: `bool_ty`/`fun_ty`,
  `var`/`app`/`lam`/`eq`/`imp`/`and`/`forall`/`exists`/`select_op`, the query
  destructors, and the full rule set (the 10 primitives + the derived rules the
  inductive engine needs). This trait already existed *inside* `covalence-init`
  (grown to make the inductive engine backend-generic within HOL); this crate
  **promotes it to a first-class supported API** and re-exports it (plus the
  generic helpers `cong_arg`/`conjuncts`/`rewrite`/`beta_expand`/…). It is also
  the trait that `covalence_inductive::LogicOps` mirrors, so the inductive-types
  API rides along.
- **`Nat`** (new) — the natural-number surface: the `nat` carrier type,
  `zero`/`succ`/`lit`/`add`/`mul` term builders, and **the workhorse Peano
  lemmas by name** (freeness `succ_inj`/`zero_ne_succ`, the recursion equations
  `add_base`/`add_step`/`mul_base`/`mul_step`, and the algebra `add_zero`/
  `add_comm`/`add_assoc`/`add_cancel`/`mul_zero`/`mul_succ_r`/`mul_comm`).

Both are implemented for one concrete backend — **`NativeHol`** — and *only*
that impl (`crates/kernel/hol/api/src/nat.rs`, the `covalence-init` `Hol` impl)
mentions `TermKind` / the concrete `nat_add()` ops. Everything a consumer writes
is generic over `H: Hol + Nat`.

## The swap-the-backend argument

A consumer written against `H: Hol + Nat` cannot observe which backend it is
on: it never names `TermKind`, never names `Term::app`, never names a concrete
theorem accessor — it goes through trait methods whose *signatures* are stable.
To bring up a second backend you implement `Hol` + `Nat` for a new carrier
marker `struct OtherHol` and every trait-generic consumer compiles against it
unchanged. This is the same argument `covalence_pure::algebra`'s
`CertificateAlgebra` makes for the base tower, one level down: name the base
once, be otherwise generic.

The `tests/through_the_api.rs` suite is the end-to-end proof: it specialises
`add_comm` to numerals, builds `S 0` and `1+0=1`, and proves a generic
`x + 0 = x` helper — all written against `H: Hol + Nat`, zero backend types
named. That code is verbatim-portable to any future `Hol + Nat` impl.

## Migration order (recommended)

1. **`Nat` trait + demo** — DONE (this slice). Establishes the pattern with the
   most-used theory.
2. **`covalence-haskell` HOL backend** (`lang/haskell`, 2 `Term::` sites) — a
   small, real consumer; the cleanest first *external* migration.
3. **`proof/alethe`, `proof/egglog`** — proof-format frontends; migrate their
   term construction to `Hol` builders.
4. **`server/core`** (2 `TermKind::` sites) — trivial, high-visibility.
5. Grow the trait family as needed: an `Inductives` trait (declare type +
   recursor + induction) fronting `covalence_inductive::InductiveBackend`, a
   `HolOmega`/kinds surface tying to `kindcheck.rs`/`tyrep.rs`, and further
   theory traits (`Int`, `List`, `Bool`) mirroring `Nat`.

The impl crates (`init`/`eval`/`core`) are deliberately **not** migration
targets — they are where the backend and its adapter live.

## Non-goals / open

- The `Hol` trait fixes the error type to `covalence_core::Result` (matching its
  origin in the inductive engine). A fully backend-agnostic surface would make
  `Error` associated (as `covalence_inductive::Logic` does); deferred until a
  second backend actually needs a different error type.
- `Nat`'s theorem accessors currently return `Result` for uniformity even
  though the native impl's lemmas are infallible (the `cached_thm!` macro
  `.expect()`s internally). A backend whose lemmas are genuinely fallible (an
  object-level HOL proving them on demand) uses the `Result` honestly.
- Term-builder equality gotcha (documented in the demo): `succ(zero())` is
  `App(nat.succ, 0)`, structurally distinct from the numeral `lit(1)`; they are
  provably equal, not definitionally so. A backend with a unary `nat`
  representation would collapse them — which is exactly the kind of
  representation choice the trait hides.
