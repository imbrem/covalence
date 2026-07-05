# Plan: get `defs/` out of `kernel/hol/core` (the TCB)

**End goal (maintainer priority, 2026-07):** move the `defs/` catalogue
(TypeSpec/TermSpec definitions: nat/int/rat/real/bytes/list/unit/prod/coprod/
option/result/floats + the logic connectives + all the arithmetic) OUT of
`crates/kernel/hol/core` (TCB) INTO `crates/kernel/hol/eval` (untrusted).

**Why (in the maintainer's words):**
1. **Dramatically shrink the minimal TCB** — definitions become untrusted *data*
   whose soundness rests on the toHOL/cert contract, not on residence in the
   kernel.
2. **Auditability** — the HOL definitions sit *next to the native
   implementations* (the `covalence-pure-eval` CanonRules), so a reviewer sees
   "what `nat.add` means in HOL" beside "what it computes natively."
3. **"Unit tests" for definitions in pure HOL** — prove a definition's
   properties as `Thm<CoreHol, _>` (the pure tier of the [three-tier tower]),
   machine-checking that the definition matches the native impl.

This is the organizing goal the **literal-path foundations** now serve: literals
as lazy `toHOL` base expressions and the `ε/rep/abs` object vocabulary are *means*
to a small, defs-free core.

---

## The decoupling surface (grounded — `defs::` refs in core, outside `defs/`)

- **`thm/certs.rs` — 39 refs. THE blocker.** The 7 cert families recognize a term
  as operation X by `spec.ptr_id()` against tables built from `defs::*_spec()`
  handles (`(defs::nat_add_spec, NatOp::Add)`, …). In-TCB: a wrong table entry
  mints ⊢False. This *pointer-identity-against-defs-handles* dispatch is why the
  certs (TCB) structurally depend on `defs/`.
- **`hol.rs` — 11 refs.** Convenience builders for the logic connectives
  (`defs::and()`/`or()`/`not()`/`imp()`/`exists()`) — construct defined `Spec`-leaf
  terms. NOT kernel primitives (the primitives are `=` and `ε`).
- **`term/term.rs` — 11 refs.** `SmallIntLiteral::ty()` → `defs::u8_ty()..u64_ty()`
  (a literal's type), plus logic doc refs.
- **`ty/ty.rs` (9), `thm/mod.rs` (9), `ty/spec.rs`, `term/spec.rs`, `tohol.rs`
  (2), `thm/rules.rs` (2):** scattered type/spec construction + the `hol_light_tests`
  (19, test-only).

**Reading:** the kernel *primitives* (`=`, `ε`, the 10 rules, `define`,
`new_type_definition`, the future `ε/rep/abs`) need NOTHING from `defs/`. Every
`defs::` ref in core is either (a) the cert dispatch or (b) a convenience builder
that constructs a *defined* object. Both can leave.

---

## The core tension + resolution

**Tension:** a cert rule (TCB) must *soundly recognize* an operation to compute
it; if the operation's *definition* is untrusted (in eval), the cert cannot
recognize it *by the definition* — and it must not trust an untrusted spec's
self-tag.

**Resolution (the toHOL principle):** certs operate at the **base-op level**,
keyed on base `CanonRule` `TypeId`s (`pe::NatAdd`, `pe::IntAdd`, `pe::F32Add`, …)
which live in `covalence-pure-eval` — a *legitimate core dependency*, NOT part of
the moving `defs/`. The HOL-level operation constants (`int.add : int→int→int`)
are DEFINED in the untrusted eval catalogue; a closed HOL computation is
discharged by the **untrusted driver** composing:

```
int.add <litA> <litB>
  --unfold int.add's definition (untrusted; sound via its twin defining theorem)-->
  <base-op form over the literals>
  --core cert, keyed on the BASE op pe::IntAdd (never on defs::int_add_spec)-->
  <litC>
```

The core cert never references `defs::int_add_spec`; recognizing "this is int.add"
happens untrusted-side, via the definition. Because the cert now keys on base ops,
the 7 cert families **largely collapse into base `canon`** (`⊢ App<F,Val> =
Val(F.eval)`, which already exists) + the toHOL literal bridge — a TCB shrink
*beyond* just relocating files.

---

## Staged path (ordered fastest-to-defs-out; each stage gated + committed)

**L0 — Inventory + design lock (cheap, no code).** The surface above is the
worklist. Decide the two open questions (below) before L1. Produces the exact
target cert architecture.

**L1 — Decouple the cert families from `defs::` (the hard TCB step).** Rework
`thm/certs.rs` so recognition/dispatch keys on base-op `TypeId`s, not
`defs::*_spec` ptr_ids; move HOL-op→base-op unfolding to the untrusted
`covalence-hol-eval` driver. Likely collapses redundant family logic into base
`canon` + the literal bridge. **Gate:** the existing cert tests + the differential
suite + the `.cov` proving suites stay green; core-manifest golden shrinks.

**L2 — Relocate the convenience builders.** Move `hol.rs` connective builders and
`term.rs` literal-typing (`u8_ty`…) out of core (to `hol-eval`/`init`), or make
them not need `defs/`. After L1+L2, core has *no* `defs::` refs outside `defs/`.

**L3 — Move `defs/` to `hol-eval`, one family at a time** (logic → nat → int →
… → floats). Each family becomes untrusted twin-defined definitions *next to*
its CanonRules; after each, core drops that dependency, the ratchet/TCB shrinks
in-diff, and we add the **pure-HOL unit test** (`Thm<CoreHol,_>` proving the
definition's properties against the native impl — the payoff).

**L4 — The `ε/rep/abs` endgame (object vocabulary).** Replace `Spec`/`SpecAbs`/
`SpecRep` + `Def` (named-constant global state) with predicate-parameterized
`ε/rep/abs` (`epsilon P`, `rep P e`, `abs P e`, `P : T→bool`) — needed to fully
delete the `TypeSpec` machinery from core and remove global constant state.
Literals finish as lazy `toHOL` base expressions over this vocabulary. (Some of
this may be pulled earlier if L3 needs it per family.)

**L5 — Done.** `core/src/defs/` gone; `tcb.json` shrinks visibly. The
[three-tier tower] `CoreHol ⊂ CoreEval ⊂ CoreWasm` lands naturally: `CoreHol` =
the minimal kernel, the defs+certs are `CoreEval` (in eval).

---

## Open decisions (need maintainer steer before L1)

1. **Do the cert families collapse into base `canon` + untrusted unfolding, or
   stay as core cert families re-keyed on base ops?** The former shrinks the TCB
   more but is more rework; the latter is a smaller step. (Recommend: aim for
   collapse, but a re-keying intermediate is a valid first commit.)
2. **`ε/rep/abs` migration (L4) — now or deferred?** An *opaque-spec-handle*
   intermediate (Term keeps `Spec` leaves carrying handles built in eval) gets
   `defs/` out FASTER without the full vocabulary change; the `ε/rep/abs` cleanup
   then follows. (Recommend: defer L4; chase defs-out first via opaque handles.)
3. **L3 family ordering** — first family for the fastest visible win (recommend
   **logic**: connectives are the simplest defined constants and exercise the
   whole move end-to-end, or **nat** if we want the cert path proven first).

Everything else (S10 literal deletion, S11 endgame, the float cert families) is
downstream of this and inherits the clean base-op-keyed cert architecture.

[three-tier tower]: ../pure-hol-and-build-plan.md
