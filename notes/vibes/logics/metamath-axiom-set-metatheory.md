# Metamath axiom-set metatheory (2026-07-13)

Design record for the `covalence-metamath` metatheory layer built this session:
axiom sets as first-class objects, checked implication certificates, the
renaming/interpretation metatheorems, and the HOL-side composition facade.
Companion code: `crates/proof/metamath/src/axioms.rs`,
`crates/proof/metamath/src/interpret.rs`,
`crates/kernel/hol/init/src/metalogic/` (composition facade),
`bun run bench:setmm` (`scripts/bench-setmm.mjs`, pinned set.mm).

## Where this sits in the vision

Per `metamath-as-shared-logic-substrate`: a Covalence theorem *relative to a
Metamath-defined logic* means "∃ a Metamath derivation". Everything here is
machinery for reasoning about **which axioms** that existential quantifies
over, and for **transporting existence** between axiom sets and databases
without materialising derivations:

- **`AxiomSet`** (vendored: PROP ⊂ PRED ⊂ ZF_KERNEL ⊂ ZF ⊂ ZFC ⊂ TG; ZFC ⊂
  REALS; iset.mm's iPROP ⊂ iPRED ⊂ IZF; hol.mm's HOL) — names a sub-theory of
  a pinned database by its `$a` labels. Layered (`extends` + `delta`) so the
  ladder is explicit.
- **`axiom_closure` / `derivable_from`** — which `$a`s a proof transitively
  rests on; "theorem T needs only axioms A (+ definitions)".
- **`Implication`** (`check_implication`) — axiom set A ⇒ axiom set B: every
  B-axiom gets a *same-statement* witness theorem proved from A-axioms (+
  explicitly admitted `$a`s, conventionally `df-*`). The transport metatheorem
  (splice witness proofs in place of axiom steps) then moves every B-theorem
  to an A-theorem in O(1), never building the spliced derivation.
- **`Interpretation`** (cross-database, σ on symbols) — the IZF→ZF shape:
  check once that every src `$a` has a σ-image witness in tgt; thereafter
  `transport(label)` certifies existence of a tgt derivation for any src
  theorem without replay. `Implication` is the src=tgt, σ=id special case.

## The headline checked results (env-gated tests, pinned set.mm)

- **Reals conservative over ZFC+definitions**: all 25 `ax-cnex … ax-mulf`
  axioms have `axcnex … axmulf` witnesses with identical statements whose
  closures lie in ZFC ∪ df-*. (True conservativity of the *definitional
  extension* itself is the deferred metatheorem below.)
- **ZF's redundant axioms**: ZF_KERNEL ⇒ ZF (axsep/axnul/axpr/axinf2).
- **Negative controls**: ZF ⇏ ZFC (choice), ZFC ⇏ TG (ax-groth) — the checker
  correctly refuses.

## Soundness notes (what is checked vs argued)

- `same_statement`: conclusion + essentials (in order) + mandatory float
  typing must be identical; witness `$d` ⊆ axiom `$d` (weaker side conditions
  = stronger schema = valid substitute). Float typing is compared, not
  assumed, because `$f` is scoped in general.
- `axiom_closure` uses the compressed-proof label block — an
  *over*-approximation of use, which is the conservative direction for every
  consumer here.
- The splice/transport arguments live in module docstrings and are *argued*,
  not kernel-checked: these are Rust-level checked certificates (untrusted
  tooling), not `⊢ Derivable` kernel theorems. Lifting them into the kernel is
  exactly the `transport_db` structural-σ program
  (`metalogic/SKELETONS.md`).

## HOL-side composition (using Metamath proofs from outside Metamath)

`metalogic::mm_compose::DbSession` composes derivability theorems in the
`Derivable_DB db` world (reified-**prop** carrier `Φ⟨bool⟩`, where the
monotonicity/interpretation theorems live). A session fixes a database value
`db = λf. f = a₀ ∨ … ∨ f = aₙ₋₁`; `axiom(formula)` mints `⊢ Derivable_DB db
⌜formula⌝` (membership + `derive_axiom_from_membership`), and `mp(a, b, der_a,
der_ab)` combines `⌜A⌝` and `⌜A⟹B⌝` into `⌜B⌝` via `derivable_db_mp` — Metamath
rule application performed by the HOL kernel, no `.mm` proof of the composite
`B` written down (and `B` need not be an axiom or stored theorem). All results
genuine + hypothesis-free; no new trusted code. Example (two MP steps derive an
un-stated `p2`): `crates/kernel/hol/init/examples/mm_compose.rs`.

The `.mm` **importer** (`mm_database::replay_db`) produces the *other*
derivability encoding (`Derivable_L` over a `RuleSet`, `Φ = nat`); composing
imported set.mm theorems the same way needs a `RuleSet`-level MP (today
`derivable_db_mp` is database-value-specific), and a general `apply(rule,
floats, premises)` beyond MP — both in `metalogic/SKELETONS.md`.

## Deferred (recorded in SKELETONS)

- **Definitional-extension conservativity** as a metatheorem (today `df-*` is
  *admitted*, honestly reported, not discharged). Includes
  unfolding/renaming of definitions as statement-transformers.
- **Derived-witness bridges**: implication/interpretation witnesses that are
  small tgt *proofs* rather than existing assertions (needed to finish
  IZF→ZF where iset/set statements differ syntactically).
- **α/$d-variant statement matching** (same schema up to bound-variable
  choice).
- **Kernel-level transport**: reify Implication/Interpretation as
  `⊢ Derivable_A ⌜S⌝ ⟹ Derivable_B ⌜σS⌝` via the metalogic engine
  (structural σ blocker).

## North star (user-stated, not this session)

"Assuming Con(ZFC), toHOL(S) is true if Derivable(ZFC, S)" for a fragment
(e.g. arithmetic statements): a *reflection* bridge from the Metamath substrate
into HOL truth. Pieces it needs: the grounding bridge
(`∃P. ValidProof(P,S,db) ⟺ Derivable_DB db S`, metalogic SKELETONS), a toHOL
statement-translation on the arithmetic fragment (cf. the toHOL literal
design), and a soundness-of-ZFC-relative-to-HOL-model argument — the pillar-1
interpretation machinery above is the substrate-side half.
