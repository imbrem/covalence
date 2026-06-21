# Peano Arithmetic — build plan (STATUS: DONE)

> **STATUS: DONE — kept as a pointer.** This was the handoff plan for building
> Peano Arithmetic as a reified object theory inside HOL (rung 2 of the
> prop → PA → SOA ladder). The plan has **landed**: the PA deep embedding +
> the Metamath PA database + the untrusted-proof → kernel replay all exist.
> The original long build plan is recoverable from git history; this file is
> now just a status note + pointers.

## What's built (and where it's tracked)

The proper deep embedding is done — pure `Derivable_PA`, a single internalized
soundness theorem, and one-step projection — plus the Metamath ⇄ HOL side and
the replay bridge. The authoritative, up-to-date status (including what is still
**deferred** and why) lives next to the code:

- **[`crates/covalence-hol/src/peano/SKELETONS.md`](../crates/covalence-hol/src/peano/SKELETONS.md)**
  — module-by-module status: `fol.rs` (reified locally-nameless FOL syntax +
  substitution), `sem.rs` (two-sorted HOAS carrier + single-Church-fold
  denotation), `pa.rs` (`Derivable_PA A := ∀d. Closed_PA d ⟹ d A`, the
  11-clause `Closed_PA`, the once-proved soundness theorem, one-step `project`),
  `mm_pa.rs` (the Metamath PA `Database` — the `ValidProof` side), and
  `mm_replay.rs` (the untrusted Metamath-PA → kernel replay landing the headline
  `⊢ ∀x. x+0=x`). It also records the remaining **deferred** items: the headline
  as a full `.mm` proof script (proper-substitution apparatus), the
  `RuleSet`-from-`Database` stretch, the quantifier/equality derivation
  constructors (the motive-capture redesign), and the `.cov` surface (Phase C).

## Where this fits the vision

- **[`theories-models-and-logics.md`](./theories-models-and-logics.md) §5.5/§5.6**
  — PA is the worked instance of the two metatheory pillars (induction on
  derivations → interpretation; representation equivalence) and of *Metamath as
  the shared logic-definition substrate*: `mm_pa` is a Metamath database, and
  `Metamath-PA ≅ our-PA` is the anchoring correspondence.
- **[`roadmap.md`](./roadmap.md)** — PA is listed under "what is already built";
  the generic `metalogic` engine (`Derivable_L`, the HOL `Database` type, the
  `⊑`/`⟹_σ` relation lattice) that PA is now wired onto is the Phase-A keystone.
