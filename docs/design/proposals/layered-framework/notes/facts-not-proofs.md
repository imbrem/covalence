# Facts, not proofs

> **STATUS: PROPOSED — working-draft note, not committed.**
>
> Companion note to the [layered-framework
> proposal](../README.md). Captures the operating principle for
> the bottom layer's data model. Not a committed architecture; see
> [`where-we-are.md`](../../../../where-we-are.md) for the canonical
> snapshot.

## The principle

The trusted bottom layer stores **facts**, not justifications.

A fact is a value of the opaque kernel type (`Thm` / `EThm` / etc.).
The value is itself the witness that the legal rules were applied —
soundness is *constructional*, as in HOL Light: no other path could
have produced the value. Once a fact is constructed, the trail that
produced it is **dropped**.

Equivalently: the bottom layer never grows when we add a new
algorithm A. A clever new equality saturator, a faster SMT, a learned
tactic — all of these compose existing rule applications. They don't
ship a justification format to the kernel, and the kernel doesn't
record one.

This is plain LCF discipline. We call it out because earlier drafts of
the [proposal](../README.md) and in-conversation notes
drifted toward "store the justification chain," which is **not** what
we want.

## What the bottom layer actually contains

1. **Opaque fact types.** `Thm`, `EThm`, and similar. Constructible
   only via the legal rules. No way to forge.
2. **The (tiny, fixed) constructor set.** The legal rules. New
   algorithms above the line never extend this set — they call it.
3. **Storage and indexing of facts.** A fact store keyed by content
   hash; for equality, a union-find / congruence index over the
   stored facts. The index is part of the trusted bottom because it
   **is the storage**, not because it makes decisions.
4. **The fact-flow mechanism.** Above-the-line algorithms call legal
   rules; the kernel atomically (a) constructs the fact value and (b)
   updates indices.

That is the whole picture. There is no derivation tree, no proof
term, no "this fact was justified by step S of algorithm A" record.

## EProp / EThm under this rule

The current [Phase P](../../../../prop-egraph-design.md) shape is
already close to right:

- `EThm` is a value, like HOL Light's `thm`. Constructible only via
  the rule API (`eq_mp`, congruence rules, axiom introduction, etc.).
- The egraph's union-find is the **storage** for known equalities.
  "Is `s ≡ t`?" is an index query, O(α(n)). It is not a decision
  procedure inside the kernel; the *decision* (to assert the
  equality) happened earlier when some rule application constructed
  an `EThm` and the kernel atomically merged the eclasses.
- Adding a new equality saturator (egglog, an SMT theory, a learned
  rewriter) means writing an above-the-line component that **finds
  sequences of rule applications** and makes them. The kernel
  records the resulting `EThm`s. The saturator does not need to
  produce, transmit, or store a justification format.

What this does *not* change:

- The kernel's rule list. Same rules as Phase P.
- The Prop-egraph invariants (no `concl` field; canonical truth via
  union with `Bool(true)`; userspace allocates the truth ref). See
  [memory: Prop-egraph no-concl](../../../../../README.md) — the
  invariants are about *what counts as a legal rule application*, not
  about justification storage.

What this *clarifies*:

- The egraph machinery (UF rebuilds, congruence closure, eclass merging)
  is part of the trusted bottom **because it is the storage**, not
  because we trust it to "decide" anything. Decisions happen at the
  rule-application boundary.
- Rewrite **scheduling**, rule **selection**, and saturation
  **strategy** are explicitly above the line. A bug in scheduling
  cannot produce a false fact; it can only fail to find a true one.

## Federation: signed facts, not signed proofs

Two engines exchange `Signed<Thm>`, not `Signed<Proof>`.

- If engine B trusts A's signing key (an [authority](../03-authority.md)),
  B accepts the fact. No proof is shipped because none is stored.
- If B does not trust A, two options:
  1. **Re-derive locally.** B runs whatever algorithm finds the rule
     sequence on its own. Cheaper than it sounds for many cases
     because the search space is constrained by the fact's
     statement.
  2. **Recorder mode.** A re-runs the derivation with an *optional*
     recorder that captures the rule-application trail, then ships
     the trail. B replays it through its own kernel — same rules,
     same kernel — and constructs its own fact.

Both options are explicitly outside the trusted bottom. Federation
infrastructure (PKI, signing, transport) lives in
[§09-federation](../README.md#planned-not-yet-written) (planned).

## Optional proof recording

When recording is wanted — for export to a distrustful engine, audit,
debugging, or pedagogical "show me the proof" — the kernel exposes a
**recorder** mode. The recorder is a separable, off-by-default
component that:

- Hooks the rule-application API and writes the rule name + premise
  IDs + result ID to a sidecar log.
- Produces a replayable derivation script, *not* a proof term.
- Has no effect on the fact store or on soundness when off.

The recorder is a debugging / interop convenience, not a soundness
mechanism. Soundness is the LCF discipline; the recorder is *output*.

## The acceptance test for an above-the-line algorithm

A new algorithm A is correctly above the line if:

1. A does not extend the kernel's constructor set.
2. A produces facts only by calling existing legal rules.
3. Swapping A for A′ (a better implementation of the same job)
   requires **zero changes to the trusted bottom layer**.

If any of those fail, A has leaked into the TCB and needs to be
restructured — either reduced to legal-rule applications, or
introduced as an explicit [oracle with a meaning-axiom](../03-authority.md)
(which is the *intended* way to add trusted capabilities).

## What this note is *not* saying

- **Not** "proof storage is bad." It's optional and useful; it just
  isn't where soundness lives.
- **Not** "decision procedures are forbidden." A decision procedure
  is fine — it lives above the line and emits facts via the rule
  API. The kernel's β/η-aware well-formedness checking
  (see [§05-trust](../05-trust.md)) is a type-theoretic
  necessity, not an "equality decision procedure."
- **Not** "the egraph is untrusted." The egraph **storage** is
  trusted (it is part of the kernel's data structures). The egraph
  **engine** — strategy, scheduling, rule firing — is untrusted.
  Same distinction as "the symbol table is trusted, the parser
  isn't."

## Cross-references

- [Layered-Framework proposal README](../README.md)
- [§02 Framework](../02-framework.md) — the bottom layer's primitives.
- [§03 Authority](../03-authority.md) — oracles, meaning-axioms; how
  trusted capabilities enter the system.
- [§05 Trust](../05-trust.md) — meta-trust vs trust set; β/η in
  meta-trust as well-formedness, not as equality decision.
- [`prop-egraph-design.md`](../../../../prop-egraph-design.md) — the
  current Phase P design that this note refines.
- [`where-we-are.md`](../../../../where-we-are.md) — what's actually
  built today.
