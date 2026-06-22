# covalence-core: kernel soundness audit

> **STATUS: AUDIT REPORT + FORWARD-LOOKING DESIGN.** Audits the TCB
> (`crates/covalence-core/src/`) as it stands on branch `proof-thoughts`
> (commit `e1738f1`, 2026-06-20). §1–§2 inventory and critique the current
> trusted base; §3 proposes confidence-improvement steps that do **not**
> block the roadmap; §4 designs **assumption tracking** (the user's key
> ask). §4 is a *design sketch* — no kernel code is changed by this report;
> the illustrative API in §4.4 is clearly marked as proposal.
>
> Grounds in [`kernel-design.md`](./kernel-design.md) (esp. §5, §8, §9,
> §11), [`observers.md`](./observers.md) (esp. §7), and
> [`VISION.md`](./VISION.md) §4. Where this report disagrees with
> `kernel-design.md` §9's "no known soundness holes" framing, it says so
> explicitly and explains why the residual risk is real but bounded.

---

## 0. Executive summary

The kernel is an LCF-style HOL Light core (~3 KLoC) whose only path to a
`Thm` is the rule API in `thm/`. **`Thm::build` is module-private**, so the
`thm/` directory is the whole minting surface — a genuinely small, auditable
boundary. The *logical* core (the HOL Light primitive ten + the standard
derived rules) is on very solid ground: these are textbook rules with
decades of model-theoretic pedigree, and the implementations are tight
single-shot term builds.

The **risk is concentrated in the non-logical extensions** the kernel adds
for efficiency and for its binary-data mission:

- **Accelerated reduction** (`reduce_prim` / `unfold_term_spec`) — sound
  "by literal denotation," but that claim rests on Rust arithmetic code
  agreeing with the catalogue bodies it is coupled to. This is guarded by
  *example-based* tests, not exhaustive proof, and one real hole
  (`nat.mod n 0`) was found here historically.
- **The `defs/` catalogue** — "semi-trusted," but several rules
  (`unfold_term_spec`, `spec_ax`, the `spec_*` subtype laws) commit the
  kernel to facts about catalogue bodies. The catalogue's *internal*
  consistency (e.g. that `int.add`'s body really is the Grothendieck
  addition) is asserted by construction and never machine-checked.
- **The four+ non-computational axioms** (`nat_induct`, `false_elim`,
  `unit_eq`, `lem`, plus `select_ax`/`spec_ax`/`succ_inj`/`zero_ne_succ`) —
  standard and sound under the stated model, but `lem` and the Peano
  freeness rules are *postulated* rather than *derived*, even though they
  are derivable; each is a place where a coding bug could not be caught by
  "it's just the standard derivation."
- **No provenance for any of the above.** `has_no_obs` tracks only `Obs`
  leaves. A `Thm` produced via `reduce_prim`, `lem`, or `nat_induct`
  carries **zero trace** of that fact. So today the kernel *cannot answer*
  "does this proof use nat acceleration?" — the precise question §4 is
  designed to make answerable.

Top recommendations (detail in §3): (1) make `audit_reduce_matches_body`
property-based / exhaustive-over-small-inputs rather than example-based;
(2) **restore the connective soundness witnesses** — `kernel-design.md` §5.2
claims they cross-check the fast connective rules, but they were *deleted*
on this branch (§1.3 finding), so those rules currently have no live
executable check — and then extend the same pattern to discharge `lem`;
(3) build the §4 assumption-tracking field so acceleration and oracle use
become *visible*; (4) treat the upcoming `core.cov` data-driven catalogue
as an opportunity to make the catalogue *checkable data* rather than
trusted Rust.

The §4 design in one paragraph: give `Thm` an **assumption set** — a small
lattice of named base assumptions (`NatAccel`, `BytesAccel`, `IntAccel`,
`Lem`, `Choice`, `Peano`, plus per-observer-type and per-postulate tags) —
that each rule unions into its result. The **default interface treats the
base set as NULL** (assumed valid, so everyday proving is unburdened), but
the set is queryable, so one can ask "which assumptions does this `Thm`
rest on?" and single out proofs that *don't* use, say, `NatAccel`. An
assumption is **discharged by proving it**: develop Peano arithmetic
without the `NatAccel` assumption, show categoricity, and then *identify*
the accelerated `nat` with the defined naturals — at which point `NatAccel`
is dropped from any `Thm` that re-derives it, exactly the
`observers.md` §7 "trust the WASM spec → prove it instead" move turned on
the kernel's own literals.

---

## 1. The trusted base — an inventory

For each entry: **what is assumed**, **why it's believed sound**, and a
**confidence** rating (HIGH / MEDIUM / GUARDED — where GUARDED means "sound
under a side condition the kernel does not itself enforce, checked only by
tests").

### 1.1 The minting boundary

| Assumption | Why sound | Confidence |
|---|---|---|
| `Thm::build` is the *only* constructor and is module-private to `thm/`; every rule bottoms out there; `build` re-types concl + all hyps at `bool`. Free variables are identified by `(name, type)` (`Var`), so there is no cross-term name/type consistency to enforce — a same-named variable at two types is two distinct variables (HOL Light's model). | Standard LCF discipline. The boundary is small and the privacy is enforced by Rust's module system. | **HIGH** |
| `Obs` leaves compared by `Arc` pointer identity, never user `Eq`/`Ord`/`Hash` (`observer.rs`). | A misbehaving observer cannot corrupt the hyp `BTreeSet`. Verified by inspection; the `PartialEq`/`Ord`/`Hash` impls all go through `Arc::as_ptr`. | **HIGH** |

The supporting machinery `build` *relies on* — `subst.rs` (de Bruijn
shift/open/close/subst), `type_of_in`, `Ctx` set ops — is in the TCB and
its correctness is assumed. `subst.rs` is 22 KLoC of fiddly index
arithmetic; it is the single largest "trust by inspection" surface and the
most likely home for a subtle capture/shifting bug. Confidence **MEDIUM**
(no property-based commutativity tests yet — see §3).

### 1.2 The HOL Light primitive ten + standard derived rules

`refl`, `trans`, `mk_comb`, `abs`, `beta_conv`, `assume`, `eq_mp`,
`deduct_antisym`, `inst`, `inst_tfree`; plus `sym`, `cong_app`/`cong_abs`
(aliases), `imp_intro`/`imp_elim`, `all_intro`/`all_elim`, `eta_conv`.

- **Assumed:** HOL `=` is interpreted as model equality; each rule is sound
  under that interpretation.
- **Why sound:** these *are* HOL Light's rules (and its well-known derived
  rules), with the standard model-theoretic justification recorded in each
  `Soundness:` docstring. The derived rules are exposed as direct
  constructors for performance, but each docstring points at the canonical
  HOL Light derivation.
- **Confidence: HIGH** for the logical content. The residual risk is purely
  *implementation* — e.g. a side-condition slip in `abs`/`all_intro` (the
  "free var not in hyps" check) or in `eta_conv`'s `uses_bound_outer`
  guard. These checks are present and read correctly, but they are
  hand-written, not derived. Confidence **HIGH but not absolute**.

### 1.3 The propositional connective fast-rules

`and_intro`, `and_elim_l/r`, `or_intro_l/r`, `or_elim`, `not_intro`,
`not_elim`.

- **Assumed:** these match the derivations from the `defs/logic.rs`
  definitions of `∧`/`∨`/`¬` over `=`/`ε`/`T`/`F`.
- **Why sound:** `kernel-design.md` §5.2 claims an executable witness
  derivation in `covalence-hol::proofs::bool` cross-checks each fast
  method. **AUDIT FINDING: on this branch that witness module no longer
  exists.** `covalence-hol::proofs::mod.rs` documents that the old `bool`
  module "(HOL connective intro/elim *postulates*) … were removed: the
  connectives are now kernel primitives," recoverable only from
  `backup/pre-hol-cleanup`. So the connective fast-rules are **today
  justified only by their `Soundness:` docstrings, with no live executable
  cross-check** — the doc's strongest claim is stale.
- **Confidence: MEDIUM (downgraded from the doc's implied HIGH).** The
  derivations are standard HOL Light `bool.ml` and the constructors read
  correctly, but the cross-check that would catch an implementation
  divergence is gone. **Recommendation (§3.2): restore an executable
  witness test** — this is also the model to extend to `lem`. (This is the
  same doc-staleness class kernel-design §9 lists under "Doc-comment
  audit," now reaching into a load-bearing soundness claim.)

### 1.4 The non-computational axioms

| Rule | Assumed | Why sound | Confidence |
|---|---|---|---|
| `nat_induct(base, step)` | `Type::nat()` denotes the standard naturals freely generated by `0`/`succ`. | The defining property of the naturals. The read-back of motive/var from the conclusion shapes + the GEN side conditions (`n` free in neither `p` nor `Γ₂`) are implemented and checked. | **HIGH** (logic) / **MEDIUM** (the shape read-back is bespoke parsing; a parser bug would reject, not over-accept, so fail-safe). |
| `false_elim` | `F = Bool(false)` denotes falsity; `Γ ⊢ F` means `Γ` is contradictory. | Ex falso. Trivial. | **HIGH** |
| `unit_eq(a, b)` | `unit := { b : bool | b = T }` is a one-element type. | Singleton ⇒ any two inhabitants are equal. Sound *if* the `unit` spec really carves a singleton — which is a `defs/` fact (§1.6). | **HIGH** (given the spec) |
| `lem(p)` | Classicality (two-valued model). | Derivable in HOL Light from `ε` + extensionality + `deduct_antisym` — the kernel has every ingredient — but **exposed as a direct axiom**, not derived. | **MEDIUM**: logically impeccable, but it is a *postulate* where a derivation is possible; a standing target. |
| `select_ax(p, x)` | Hilbert choice: `(p x) ⟹ p(ε p)`. | The characterising axiom of `ε`/`Select`. Standard. | **HIGH** |
| `spec_ax(t, w)` | Each named def-spec is its own choice: `(p w) ⟹ p(t)`. | Unconditionally sound *in isolation* (vacuous if `p` empty). **But couples with `reduce_prim`** — see §1.5 / §2.3. | **GUARDED** |
| `succ_inj`, `zero_ne_succ` | `0`/`succ` are distinct, injective constructors of the free `nat`. | The other half of the `nat_induct` commitment. Standard, but again *postulated* rather than derived from a recursion/no-confusion theorem. | **MEDIUM** |

**Critical-auditor note:** `kernel-design.md` §5.7 calls `nat_induct` +
`false_elim` + `unit_eq` + `lem` "the entire non-computational axiom
surface," but the freeness rules (`succ_inj`, `zero_ne_succ`) and the two
choice rules (`select_ax`, `spec_ax`) are *also* non-computational
primitives. The honest count is **eight** non-computational axiom-shaped
rules, not four. Each is standard; the point is that the doc's framing
undercounts the trusted surface.

### 1.5 Accelerated reduction — `reduce_prim` / `unfold_term_spec`

- **Assumed:** each emitted `⊢ t = canonical` is true "by the literal's
  fixed denotation." Concretely: distinct literals denote distinct values
  (`Nat(5) ≠ Nat(6)`, etc.), and the Rust arithmetic in `builtins.rs`
  computes the *real* function the operand denotes.
- **Why believed sound:** for `reduce_prim`, literal distinctness is the
  kernel's denotational commitment (`literal_eq`), and each arithmetic arm
  is small, reviewable Rust. For `unfold_term_spec`, the unfolding equation
  `Spec = body` is a definitional let-binding, sound for *any* body.
- **The real risk** (the kernel-design §9 "coupling"): when a spec is
  reachable by **both** rules — let-style body **and** in `PRIM_TABLE` —
  the kernel commits to *two* facts (`spec = body` and `spec lit… =
  reduce_prim(…)`). These are consistent **only if the body denotes the
  same function `reduce_prim` computes, on every input.** A divergence is
  *derivable inconsistency*: it yields `litₐ = lit_b` for distinct
  literals, hence `⊢ F`. This already bit once: `nat.mod n 0` reduced to
  `0` while the body `n − (n/m)·m` evaluated to `n` at `m=0`, reproducing
  `⊢ 0 = 5` unconditionally (fixed; reduction now returns `n`).
- **Confidence: GUARDED.** The coupling is real, the guard
  (`audit_reduce::audit_reduce_matches_body`) is **example-based** — it
  probes a hand-picked tuple list (the div/mod sign quadrants, a handful of
  fixed-width edges), not all inputs or even all reducible ops. The
  Grothendieck/`iter` ops (`nat.add`, `int.add`, …) are *immune* because
  their bodies are stuck at `ε` and can't reduce to a literal
  (`iter_based_bodies_are_stuck` confirms this) — so they are sound by the
  model alone. The danger zone is exactly the let-style-AND-reducible ops,
  and the test's coverage of *that* zone is finite-sample, not exhaustive.

### 1.6 The `defs/` catalogue — semi-trusted

- **Assumed status (per kernel-design §6/§8):** user-constructed specs go
  through the *same* rules as catalogue entries, so the catalogue "needs no
  special trust." This is *true for `unfold_term_spec` in isolation* (a
  let-binding for an opaque atom is sound for any body).
- **Where it is NOT trust-free:** three places where catalogue *content*
  matters:
  1. **`reduce_prim` coupling** (§1.5) — only the kernel-shipped specs in
     `PRIM_TABLE` are coupled, and the coupling demands the *catalogue
     body* match the *Rust reduction*. That is a property of the shipped
     catalogue, not a user concern.
  2. **`spec_ax` × `reduce_prim`** — for a def-style spec *also* in
     `PRIM_TABLE` (today only `nat.le`, `nat.lt`), the kernel commits to
     both the choice axiom and the reduction; they are jointly satisfiable
     only because the predicates (the four recursion equations) have a
     *unique* solution that `reduce_prim` computes. Guarded by
     `audit_reduced_def_specs_satisfy_their_predicate` — again
     example-based.
  3. **`unit_eq` / `Type::unit()`** — `unit_eq`'s soundness *is* the claim
     that the `unit` spec carves a singleton. That is a `defs/unit.rs`
     fact the kernel rule *depends on* but never checks.
- **Confidence: MEDIUM, and the "semi-trusted, no special trust needed"
  framing is too generous.** A bug in a *kernel-shipped* coupled body, or
  in `unit`'s carving predicate, is a genuine soundness bug — it just
  happens to be confined to the shipped catalogue (users can't *enlarge*
  the coupled set without going through `PRIM_TABLE`, which is kernel
  code). So: the catalogue is semi-trusted *for user-constructed specs* but
  **fully trusted for the kernel-shipped coupled subset**, and that subset
  is verified only by example tests.

### 1.7 Spec coercions and subtype laws

`Term::spec_abs`/`spec_rep` (bare typed leaves, theorem-free) and the three
witness-free bijection rules `spec_abs_rep`, `spec_rep_abs_fwd`,
`spec_rep_abs_back`; plus `new_type_definition`'s three bijection theorems.

- **Assumed:** the "total interpretation" in `thm/mod.rs` (lines 825–836):
  `S = { x | ⟦P⟧ x }`; if `S ≠ ∅`, `τ = S` with `abs` a retraction and
  `rep` the inclusion; if `S = ∅`, `τ = carrier` with `abs = rep = id`.
- **Why sound:** every *other* rule treats `abs`/`rep` as uninterpreted, so
  committing to this interpretation is consistent. The witness-free "back"
  direction is correctly *weakened* (the `P a ∨ ¬∃x. P x` escape hatch)
  precisely because no non-emptiness witness is supplied. This is careful,
  correct reasoning.
- **Confidence: HIGH** for the laws as stated. The one thing to watch:
  `subtype_pred` rejects quotient specs (whose `tm` is a relation), so the
  laws only fire for subtype/newtype specs — that gate is load-bearing and
  is checked (`pred.type_of()? == carrier → bool`).

### 1.8 Literal builtins

`TermKind::Nat/Int/SmallInt/Blob/Bool` are kernel-builtin term leaves
(`Succ` too, as a monomorphic `nat → nat` constructor).

- **Assumed:** these denote their obvious values, and distinct same-kind
  literals are distinct (the basis of `literal_eq`).
- **Why sound:** they are the binary-data substrate the kernel exists to
  serve; treating `Blob(b"hi") ≠ Blob(b"bye")` as a denotational commitment
  is exactly the "kernel as binary-data substrate" vision. `Succ` is
  handled as a closed, tvar-free no-op leaf in every substitution/predicate
  walk (`has_no_obs` returns `true` for it, etc.).
- **Confidence: HIGH** for the denotation; the only risk is a missing arm
  in some substitution/typing walk for one of these kinds (a past pass
  fixed a `match_types` arm that panicked on `Bool`/`Spec`). A panic is
  fail-stop, not unsoundness — but a *wrong* arm could be.

---

## 2. Gaps & risks (the critical-auditor section)

### 2.1 Provenance is syntactic-only — the headline gap

`has_no_obs` walks for `Obs` leaves and nothing else. **Acceleration and
axiom use leave no trace.** A `Thm` built with `reduce_prim`, `lem`,
`nat_induct`, or `Thm::assume(postulate)` is indistinguishable, by any
kernel query, from one built purely from `refl`/`trans`/`mk_comb`. Three
consequences:

- You cannot ask "does this proof depend on nat acceleration?" — the exact
  capability `observers.md` §7.2 promises and §4 here designs.
- `Thm::assume`-style postulates *are* visible (they sit in `hyps`), which
  is good — but a postulate routed through an *observer* (`obs_true`) is
  visible only as an `Obs` leaf with no indication of *which* policy
  admitted it or *what* it assumed.
- The "this theorem holds in the bare logic" property (`has_no_obs`) is
  *too coarse*: a theorem can have no `Obs` leaves yet still depend on
  `lem` (classicality) or `NatAccel`. `has_no_obs == true` does **not**
  mean "constructive" or "acceleration-free."

### 2.2 The acceleration coupling guards are example-based

`audit_reduce_matches_body` and
`audit_reduced_def_specs_satisfy_their_predicate` probe finite tuple lists.
They caught the `nat.mod n 0` hole *after* it shipped, on a pass that
specifically went looking. There is no exhaustive-over-small-inputs or
property-based sweep, and no guard that *new* `PRIM_TABLE` entries are
automatically included (adding a coupled spec without extending the probe
list silently leaves it unguarded). This is the highest-leverage place to
raise confidence (§3.1).

### 2.3 The `spec_ax` × `reduce_prim` coupling is subtle and under-guarded

The soundness argument ("the predicate has a unique solution =
`reduce_prim`'s output, so they can't disagree") is correct for `nat.le` /
`nat.lt` but rests on a *uniqueness-by-construction* claim that is **not
machine-checked** — only the weaker "reduce satisfies the equations" is
tested. A future def-style spec added to `PRIM_TABLE` with a predicate that
*under*-determines its solution would be a soundness hole that the existing
guard would not catch. The doc flags this as a manual obligation; manual
obligations are exactly what audits exist to distrust.

### 2.4 Catalogue content is asserted, never checked

Nothing verifies that `int.add`'s body really is Grothendieck addition, that
`unit`'s predicate really carves a singleton, or that the `coprod`/`prod`
constructors are mutually consistent. The "semi-trusted" label papers over
the fact that the *kernel-shipped coupled subset* (§1.6) is fully trusted
and verified only by example. The `core.cov` migration (§3.4) is the right
moment to address this.

### 2.5 Postulated-but-derivable axioms

`lem`, `succ_inj`, `zero_ne_succ` are all derivable (the first from `ε`, the
latter two from a no-confusion/recursion development) yet shipped as direct
constructors. Each is a constructor whose *body* could have a bug that "it's
the standard derivation" reasoning would not catch — because there is no
derivation in the loop. The connective fast-rules were *supposed* to show
the better pattern — keep the fast constructor, maintain an executable
witness a test cross-checks — but that witness was deleted (§1.3), so they
have currently *regressed into the same bare-postulate posture*. Restoring
the witness (§3.2) is the fix for both.

### 2.6 `subst.rs` has no property tests

The largest fiddly-index surface in the TCB (open/close/shift/subst,
simultaneous tvar substitution, capture avoidance) is tested only through
end-to-end rule tests. A capture or off-by-one bug here would be a
soundness bug of the worst kind (silent, far from its cause). Property-based
tests for substitution commutativity / α-equivalence are listed in
kernel-design §9 as "hardening opportunities" and remain undone.

### 2.7 No independent re-check path exists yet

kernel-design §11.5's "paranoid mode" (a simple dynamic core that
re-checks the fast paths) is design, not code. Today every fast path is
trusted on its own; there is no second, independent implementation to make
the "confidence from agreeing paths" mirror principle
([`VISION.md`](./VISION.md) §4) operational at the kernel level.

---

## 3. Confidence-improvement roadmap (non-blocking)

Each item is incremental and compatible with the current roadmap.

### 3.1 Make the acceleration guards exhaustive-ish and self-extending

- Convert `audit_reduce_matches_body` to **property-based** (e.g. quickcheck
  over `Nat`/`Int`/`SmallInt` ranges incl. the zero/sign/overflow edges)
  rather than a fixed tuple list.
- Add a **table-completeness test**: iterate `PRIM_TABLE`, and for every
  let-style entry assert it appears in the body-match probe set (fail if a
  new coupled spec was added without a guard). This closes §2.2's "silent
  unguarded addition" gap mechanically.
- Same treatment for `audit_reduced_def_specs_satisfy_their_predicate`, and
  add a uniqueness check (or at least a documented uniqueness obligation
  *with a test that would catch a counter-model*) for §2.3.

### 3.2 Discharge the postulated-but-derivable axioms

First, **restore the connective witness cross-check** (§1.3 finding: the
`covalence-hol::proofs::bool` witnesses were deleted; the fast connective
rules currently have no live executable cross-check). Then extend the same
pattern to:

- **`lem`** — port HOL Light's `EXCLUDED_MIDDLE` derivation from `ε` +
  extensionality + `deduct_antisym` into `covalence-hol::proofs`, and
  cross-check the fast `Thm::lem` against it. Then `lem` becomes a
  *witnessed* fast-rule rather than a bare axiom.
- **`succ_inj` / `zero_ne_succ`** — derive from the nat recursion theorem
  (already done in the shell per memory note `recursion-theorem-done`) and
  cross-check.

This shrinks the *effective* axiom surface from eight to ~three
(`nat_induct`, `false_elim`, `unit_eq` — the irreducible model
commitments + choice) while keeping the fast constructors.

### 3.3 Property tests for `subst.rs`

Close §2.6: substitution/shift commutativity, `open ∘ close = id` on
closed terms, α-equivalence under renaming, simultaneous-subst vs.
sequential-subst divergence (the swap case `inst_spec_tvars` guards
against). This is pure-`covalence-core` work, no roadmap dependency.

### 3.4 Use the `core.cov` migration to make the catalogue *checkable*

A concurrent agent is migrating `defs/*.rs` into a data-driven
`defs/core.cov` catalogue. **This does not appear on `proof-thoughts` yet**
(no `*.cov` under `crates/covalence-core`; `core.cov` is not present), so
this audit covers the *Rust* catalogue. When it lands, the TCB surface
shifts:

- The **trusted parser** for `core.cov` becomes part of the base (a new,
  small, auditable trusted component — analogous to the simple core of
  §11.5).
- The **`core.cov` data itself becomes checkable**: catalogue bodies are
  now *data*, so the body-vs-reduce coupling (§1.5), the spec-predicate
  obligations (§2.3), and even "`unit` carves a singleton" can be expressed
  as *checks over the data* run at load time, rather than trusted Rust. The
  data is content-addressable, so a frozen, audited catalogue blob can be
  pinned.
- Net: the migration *reduces* the trusted Rust surface (the catalogue
  arithmetic moves from "trusted by inspection" toward "data + a checked
  reduction"), at the cost of one new trusted parser. Recommend the parser
  be kept minimal and the load-time checks from §3.1/§3.2 run against the
  data.

### 3.5 Stand up a minimal "paranoid mode" prototype

Even a partial simple-dynamic-core that re-checks `reduce_prim` outputs
(recompute the body by explicit unfold + literal eval and compare) would
operationalize the mirror principle for the highest-risk rule. This is the
kernel-design §11.5 vision in miniature and a natural home for §3.1's
property checks.

### 3.6 Cross-validation and an external model

Lower priority, higher assurance: cross-check theorems against HOL Light
proper; a Lean/Coq model of the rule set for an independent consistency
proof (both listed in kernel-design §9). These are big but don't block
anything.

---

## 4. Assumption tracking — the design

> **Forward-looking design.** Not a demand to implement now. Realizes
> [`observers.md`](./observers.md) §7.2 ("this proof doesn't use `Nat`")
> and the [`kernel-design.md`](./kernel-design.md) §11 narrow-waist /
> trusted-observer direction. The code in §4.4 is illustrative.

### 4.1 The principle: a trusted observer = a sound assumption + an efficient representation

`observers.md` §7's core claim is that `Int`/`Bytes`/`Nat` are *trusted
observers*: the only thing separating a trusted observer from an untrusted
one is that "this observer is sound" is an **assumption with a compiled-in
representation** rather than a hypothesis threaded through `Thm::assume`. The
*logical content* is identical; only the cost of carrying it differs.

Assumption tracking is the machinery that makes that content **visible**
without making it **expensive**. Every accelerated/oracular/postulated step
is, morally, a discharge of a named assumption ("nat acceleration is sound",
"the WASM spec executor is sound", "`lem`"). Today those discharges are
invisible. The design gives each `Thm` an **assumption set** recording which
ones it used, while keeping the *default interface unburdened* by treating
the standard base set as implicitly valid.

### 4.2 The base assumption set and its lattice

Define a small, extensible set of **base assumptions**, each a named tag:

```
Accel(NatAccel) Accel(IntAccel) Accel(BytesAccel) Accel(FixedWidthAccel)
Axiom(Lem)      Axiom(Choice)   Axiom(Peano)      Axiom(UnitSingleton)
Obs(TypeId)     -- one per Rust observer type (WasmSpec, Store, Blake3, …)
Postulate(Hash) -- one per content-addressed assumed body (Thm::assume)
```

An **assumption set** is a set of these tags (efficiently: a small bitset
for the fixed base tags + a set for the open-ended `Obs`/`Postulate` tags).
Sets form a **join-semilattice** under union with bottom `∅` ("uses no
assumption beyond the bare logic"). Each rule computes its result's set as
the **union of its premises' sets, plus any tag the rule itself introduces**:

- `reduce_prim(t)` adds the `Accel(_)` tag(s) for the literal kinds it
  touched (`NatAccel` for `nat.*`, etc.).
- `unfold_term_spec` adds nothing for a *user* spec (it's a definitional
  let-binding, sound for any body) but adds the appropriate `Accel` tag when
  unfolding a *coupled* kernel-shipped spec (because that spec's
  consistency rests on the body-vs-reduce coupling — see §1.5).
- `lem` adds `Axiom(Lem)`; `select_ax`/`spec_ax` add `Axiom(Choice)`;
  `nat_induct`/`succ_inj`/`zero_ne_succ` add `Axiom(Peano)`; `unit_eq` adds
  `Axiom(UnitSingleton)`.
- `obs_eq`/`obs_true`/`obs_imp` add `Obs(TypeId::of::<O>())`.
- `Thm::assume(body)` *also* records `Postulate(hash(body))` (in addition to
  the existing self-hyp), so an assumed fact is queryable by content hash.
- The pure logical rules (`refl`, `trans`, `mk_comb`, `abs`, `beta_conv`,
  `eq_mp`, `deduct_antisym`, `inst`, `inst_tfree`, the connective rules)
  add **nothing** — they preserve the union of premises.

This is *exactly* parallel to how `hyps` already propagate (union on
multi-premise rules, identity on single-premise rules), so the
implementation slots into the existing `Ctx::union` plumbing.

### 4.3 The null-base default — everyday proving is unburdened

The key ergonomic requirement: **the default interface treats the base
assumption set as NULL** (assumed valid). Concretely:

- The assumption set is an **additional, ignored-by-default field** on
  `Thm`. Existing code — every rule, every consumer — keeps working
  unchanged; nobody is forced to thread or discharge assumptions.
- `Thm::Display`, equality, hashing, and the existing `has_no_obs` are
  **unaffected**. Proving `2 + 2 = 4` via `reduce_prim` just works; the
  `NatAccel` tag rides along silently.
- The set is **purely additive provenance**: it never blocks a rule, never
  changes a conclusion. It is an *audit annotation*, not a precondition.

So the cost model matches `observers.md` §7: the trusted assumptions are
"on" by default (null base = "I accept all standard base assumptions"), and
the tracking only *surfaces* what was used when you ask.

### 4.4 The query and discharge surface (illustrative API — PROPOSAL)

```rust
// PROPOSED — not in the codebase. Sketches the Thm-level mechanism.

/// A base assumption a Thm may rest on. The fixed variants are a bitset;
/// Obs/Postulate are open-ended.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Assumption {
    NatAccel, IntAccel, BytesAccel, FixedWidthAccel,
    Lem, Choice, Peano, UnitSingleton,
    Obs(std::any::TypeId),
    Postulate(O256),           // content hash of the assumed body
}

/// A join-semilattice of assumptions. Bottom = ∅ = "bare logic only".
#[derive(Clone, Default)]
pub struct Assumptions { /* bitset + small set */ }

impl Thm {
    /// The assumptions this theorem rests on. NULL/empty for a proof in
    /// the bare logic. Cheap, non-failing, read-only.
    pub fn assumptions(&self) -> &Assumptions { /* … */ }

    /// Does this proof use a given assumption? e.g.
    /// `thm.uses(Assumption::NatAccel)`.
    pub fn uses(&self, a: Assumption) -> bool { /* … */ }

    /// Discharge an assumption by supplying a Thm that *proves it in the
    /// bare logic* (or under a strictly smaller assumption set). Removes
    /// the tag from `self`'s set. Fails if `proof` is not a valid
    /// discharge of `a`, or itself depends on `a` (no circularity).
    pub fn discharge(self, a: Assumption, proof: &Thm) -> Result<Thm> { /* … */ }
}
```

`uses` answers "does this proof use nat acceleration?" directly. `has_no_obs`
becomes a special case (`!assumptions().has_any_obs()`), and a *stronger*
new query "is this proof in the bare logic?" is `assumptions().is_empty()`.

### 4.5 Discharging an assumption by proving it — `Nat` without `NatAccel`

This is the payoff `observers.md` §7.2 names: **prove `nat`'s Peano
development without the nat-acceleration assumption, then identify the
accelerated `nat` with the defined naturals — no circularity.**

The path:

1. Develop Peano arithmetic over the *defined* naturals (the `defs/nat.rs`
   bodies: `nat.add` via `nat_rec`, etc.) **using only** `nat_induct` +
   the bare logical rules + `define` — *never* `reduce_prim`. Every such
   theorem carries an assumption set that **excludes `NatAccel`** (it may
   include `Axiom(Peano)`, which is fine — that is a genuine model
   commitment, not an acceleration shortcut).
2. Prove the development is **categorical** (the naturals are unique up to
   isomorphism) — so the accelerated `Nat` literals and the defined
   naturals are provably the same structure.
3. With that isomorphism *as a `NatAccel`-free theorem*, every
   `reduce_prim`-derived numeric equation can be **re-derived** from the
   defined operations: `discharge(NatAccel, isomorphism_proof)` strips the
   `NatAccel` tag, because the equation is now backed by a bare-logic proof
   that the accelerated answer equals the defined answer.

The **no-circularity** guarantee is structural: `discharge` rejects a
`proof` whose own assumption set contains the tag being discharged. Since
step 1's development is `NatAccel`-free *by construction* (it never calls
`reduce_prim`), the discharge is sound. `NatAccel` thereby moves from
*assumed* to *proved* — the observer becomes **known-sound by a proof, not
trusted** — exactly the "trust the WASM spec → prove it instead"
([`observers.md`](./observers.md) §4) pattern turned on the kernel's own
literals.

The same mechanism generalizes: a `WasmSpec` observer's `Obs(TypeId)` tag is
discharged once someone proves `WASM(P, D, A) ⟹ ∃D'. ZFC(D', A)`
([`observers.md`](./observers.md) §4); a `Postulate(hash)` is discharged by
a bare-logic proof of that body. The assumption set is the uniform ledger
across all three.

### 4.6 Relationship to the existing substrate and the migrations

- **`has_no_obs` is the seed.** It already does the *syntactic* half (walk
  for `Obs` leaves). The assumption set generalizes it to a *semantic*
  ledger that also records acceleration and axiom use — the thing
  `observers.md` §7.2 says becomes possible "once a literal is an
  observer." The design works *today* (literals are still `TermKind`
  variants) by having `reduce_prim` tag `NatAccel` directly; it does not
  *require* the §7.1 "drop the `TermKind` enum" move, but composes cleanly
  with it (a literal-as-observer would tag via its `Obs(TypeId)` instead).
- **`core.cov` migration interaction.** When the catalogue becomes data
  (§3.4), the coupled-spec tags (`Accel(_)` on `unfold_term_spec`) can be
  *read off the data* (which specs are in the reducible/coupled set is a
  property of the catalogue blob), and the frozen catalogue's content hash
  can itself be an `Assumption::Postulate`-style provenance root — "this
  proof trusts catalogue blob `O256(…)`." That ties the assumption ledger
  to the content-addressed-store discipline of `VISION.md` §4 ("every
  assumption bound to a named artifact").
- **Validators (`observers.md` §3).** The proposed `(M, P, mFrozen,
  pFrozen)` validator state and this assumption set are the same ledger
  viewed from two ends: the validator's precondition set `P` is the
  *upstream* aggregation of assumptions an observer needed; the `Thm`
  assumption set is the *downstream* record of which ones a given proof
  inherited. Discharge connects them.

---

## 5. Bottom line

The logical core is solid and the minting boundary is genuinely small and
well-isolated. The trust is concentrated, correctly, in the *non-logical*
extensions — acceleration, the coupled catalogue subset, and the handful of
postulated-but-derivable axioms — and the current verification of those is
**example-based testing plus careful docstrings**, which found a real hole
once and could miss another. The single most valuable structural
improvement is **assumption tracking** (§4): it turns "what does this proof
trust?" from an un-answerable question into a cheap query, makes
`has_no_obs` a special case of a richer ledger, and gives a principled,
no-circularity path to *retire* the most-used trusted assumptions
(`NatAccel` first) by proving them — the same earn-your-trust discipline the
oracle story already prescribes, applied to the kernel's own foundations.
