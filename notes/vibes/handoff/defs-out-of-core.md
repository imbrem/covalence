+++
id = "N000M"
status = "draft"
review = "unreviewed"

[[contributions]]
role = "author"
actor = "agent:claude"
at = "2026-07-05T16:50:03+01:00"
source = "legacy"
agent = "claude"
harness = "claude"
+++

# Plan: get `defs/` out of `kernel/hol/core` (the TCB)

Move the `defs/` catalogue (nat/int/rat/real/bytes/list/unit/prod/coprod/option/
result/floats + logic connectives + arithmetic) OUT of `crates/kernel/hol/core`
(TCB) INTO `crates/kernel/hol/eval` (untrusted).

## Why

1. Shrink the minimal TCB — definitions become untrusted *data* whose soundness
   rests on the toHOL/cert contract, not on residence in the kernel.
2. Auditability — HOL definitions sit next to the native `covalence-pure-eval`
   CanonRules, so a reviewer sees "what `nat.add` means in HOL" beside "what it
   computes natively."
3. Pure-HOL unit tests — prove a definition's properties as `Thm<CoreHol, _>`,
   machine-checking definition vs native impl.

The literal-path foundations (literals as lazy `toHOL` base expressions;
`ε/rep/abs` object vocabulary) serve this small, defs-free core.

## The core tension + resolution

A cert rule (TCB) must soundly recognize an operation to compute it. If the
definition is untrusted (in eval), the cert cannot recognize it *by the
definition*, and must not trust an untrusted spec's self-tag.

Resolution (the toHOL principle): certs operate at the **base-op level**, keyed
on base `CanonRule` `TypeId`s (`pe::NatAdd`, `pe::IntAdd`, …) in
`covalence-pure-eval` — a legitimate core dependency, NOT the moving `defs/`.
HOL-level op constants (`int.add : int→int→int`) are DEFINED in the untrusted
eval catalogue; a closed HOL computation is discharged by the untrusted driver:

```
int.add <litA> <litB>
  --unfold int.add (untrusted; sound via its twin defining theorem)-->
  <base-op form over the literals>
  --core cert, keyed on the BASE op pe::IntAdd, never defs::int_add_spec-->
  <litC>
```

## Decisions (locked)

- **D1 — make the tower real.** Don't decouple cert tables from `defs::` inside
  core (every re-key variant re-imports the defs or loses init's defining
  equations). Instead create **`CoreEval`, a base `Language` in
  `crates/kernel/hol/eval` that extends `CoreLang`**, and move `certs.rs` +
  `tohol.rs` + the cert/toHOL rules + `defs/` there as `Rule<CoreEval>` impls
  with their own manifest golden. Works because the orphan-rule constraint binds
  rules to the crate owning the language. Trust is tiered by declaration:
  `Thm<CoreLang,_>` = pure HOL (no computation TCB); `Thm<CoreEval,_>` = +eval
  axioms.
- **D2 — typed-Thm tiering.** `core::Thm<L = CoreLang>`; `EvalThm =
  Thm<CoreEval>`; lift low→high only. init consumes the top tier via the driver/
  TermExt seam.
- **D3 — transitional residue.** Literal LEAVES (`TermKind::Nat/Int/SmallInt/
  Blob`) and their TYPES (`u8_ty`…`int_ty`) stay in core until the toHOL literal
  path replaces them; the TERM catalogue moves now. Dies with the literal leaves.
- **D4 — ε/rep/abs deferred.** Predicate-parameterized vocabulary replaces
  `define`/typedef's named machinery in a later arc; defs-out doesn't wait on it.
- **D5 — pure-HOL unit tests land with the move.** Per family, derive the same
  equation each cert mints in the `CoreLang` tier and assert equality.

## Status: L1+L2 done, audited, merged

`Thm<L=CoreLang>` tier param → `CoreEval` in `kernel/hol/eval` with the cert/
tohol/defs term catalogue moved there → pure-HOL unit tests + tiered tcb-audit.

- CoreLang manifest 52 → 26 rules (after logic-out; pure HOL only). CoreEval
  manifest carries the cert/toHOL rules.
- CoreLang extends NOTHING — `Thm<CoreLang,_>` is computation-free by
  declaration; a Builtins fact refuses to lift into it (test-pinned).
- Pure-HOL unit tests: `hol/eval/tests/pure_hol_units.rs`, per cert family.
- **Scoping correction to D5:** a `Thm<CoreLang>` derivation of a literal-leaf
  equation is mathematically impossible — the pure tier has no literal-
  denotation axioms (by design; even `⊢ T` is eval-tier while `T` is a `Bool`
  literal). What lands: pure δ/β spines + definitional derivations that never
  invoke the family under test, asserted concl-equal to the cert facts.
- Five kernel rules sequent-reshaped (`SelectAx`/`SpecAx`/`SuccInj`/
  `ZeroNeSucc`/`SpecRepAbsFwd`) — connective-free, each derivable from its old
  axiom form (no new strength); classic imp/¬ forms are `DerivedRules` drop-ins
  in hol/eval. Connective builders left `core::hol` for `hol-eval::hol`.

**Documented stayers in core:** `SpecRepAbsBack` (the `∨¬∃` disjunction IS the
witness-freeness), `NewTypeDefRule` (single-mint freshness forces `∀/⟹/∧`),
`parse_hol_forall` + `typedef.rs`'s `and_spec` recognition for the typedef
split. Die/reshape at L4/EG5.

## The next wall — needs maintainer design, do NOT improvise

Killing the D3 residue = killing the literal LEAVES = the **symbolic-prop
problem**. A `core::Thm`'s `CoreProp` holds `Val<Term>` (concrete values), so
deleting literal leaves without materializing succ-towers needs theorems whose
props stay *symbolic base exprs* (`App<ToHolNat, Val(n)>` in place of the
literal subterm) — the S5 wall: "varying `E: Expr` conclusions are
un-transportable through `eq_mp` without new base machinery."

Options to design with the maintainer:
(a) a base-level `Dyn`-expr equality/transport story;
(b) `CoreProp` generalized over a sealed family of prop shapes;
(c) keep literal leaves as ground representation, accept the residue as the
permanent (small) cost of the binary-data substrate.

Until decided, the residue stays and is measured (`scripts/tcb-audit.mjs`). L4
(ε/rep/abs endgame) and the residue deletion (with S10/S11) are maintainer-gated.
