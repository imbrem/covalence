# Architecture & Philosophy (v2)

> A content-addressed substrate on which **logic**, **computation**, and **evidence**
> are kept deliberately distinct, and on which trust is assembled from agreement
> between mutually-checking parts rather than asserted by any single authority.
> Storage *is* a version-control system; the whole thing mounts as a filesystem.

Orienting north star for implementation agents and collaborators. Explains *what we
are building*, *why the unusual choices are load-bearing*, and *which invariants must
never be violated*. Read before touching the kernel or the store.

---

## 0. The one idea

We never assert a convenient global lie. We assert **scoped truths about named,
content-addressed artifacts**, and build confidence by making *independent paths to the
same conclusion agree*. Every layer is the same move on a different axis. The
irreducible trust is pushed to a human inspecting the smallest possible statement — and
even that residual can be measured, shared, and disputed in numbers.

There is **no privileged layer and no privileged notion of "axiom."** Axioms, oracle
results, cryptographic assumptions, format-validity, and the base meta-logic itself are
all the same kind of thing: scoped assumptions you choose to discharge, connected by
edges that transport trust along whatever they preserve.

The recurring structural move (it appears **at least seven times** — kernel, logic,
execution, content, format, naming, storage): a **simple trusted core** + **arbitrarily
clever untrusted machinery** + **soundness by re-checkability against the core**.

---

## 1. The substrate

Two pieces of infrastructure underlie everything:

1. **A content-addressed store** (the VCS, §12–13). Untrusted at the API surface;
   its *read/write primitive* is in the TCB (a false read asserts a false fact).
2. **An evaluator for WASM components.** The execution engine, exposed *into* the prover
   as oracles.

A loaded blob can be interpreted, by a program on the executor, as: **syntax** in some
logic (self-embedding), **data**, **a program** for an executor oracle, **a hash**
naming further blobs, or **a signature / ZK payload** for a cryptographic oracle. The
planes below are not separate systems — they are interpretations of one content-addressed
soup, performed by the executor, under one trust discipline.

---

## 2. The kernel: LCF over arenas, HOL variant, opaque-relation oracles

### 2.1 The overriding invariant

> **INVARIANT (syntactic well-formedness).** Well-formedness of a type or term is
> **purely syntactic — never dependent on what is provable.** Decidable by structural
> recursion, inspecting nothing about provability-in-any-context.

This is the kernel-level form of "no global lie." It is what lets the **empty context
stop being privileged**: there is no difference between an axiom and an assumption,
because the oracle system works *through* the assumption system, not through separate
oracle tags. A user/oracle may assert `P` as a hypothesis on a sequent, but a hypothesis
cannot authorize a *global* type constant without making the type context-dependent — so
any primitive that inspects provability-in-empty-context is reworked away (§2.4).

### 2.2 Representation

Terms are **indices into nested, flat arenas**. A theorem is a **union-find over arena
indices**. An arena **freezes** into an immutable structure and imports — yielding a
**content-addressable theory DAG** (persistence *and* structural sharing in one).

> **INVARIANT (canonical freeze).** Same theory ⇒ same hash, independent of derivation
> order. One canonical tyvar ordering (§2.5) must be threaded uniformly through
> type-operator formation, constant polymorphism, and serialization, or the same object
> hashes differently by different paths.

> **INVARIANT (minimal kernel surface).** Union-find merge is a trusted invariant: keep
> it dead-simple-and-audited **or** have it emit a checkable certificate (the merge
> sequence as a proof object). A merge bug is a soundness hole.

### 2.3 The only trust primitive: opaque-relation discharge

An oracle may **write only to its own opaque (uninterpreted) relation symbol.** "Program
`P` evaluates to `E`" introduces a *relation*, not a truth. To *use* it you add an
explicit **meaning-assumption** ("if `P` evals to `E` then `E` is a valid evaluation of
`P` per spec `S`"). This is an assumption like any other — **no privileged axiom.** Trust
moves from "I believe this computation" to "I believe this spec characterizes this
computation," which is where a human should audit.

> **INVARIANT (hash-indexed meaning).** Meaning-assumptions are keyed to a **specific
> binary by hash**, never by name. Relation is `eval(hash, input, output)`; a binary's
> meaning-axiom must be **impossible** to apply to a different binary.

> **INVARIANT (safe axiom class — the mount rule, §12).** An oracle writer may add **any
> implication whose positive/head relations are oracle relations under that writer's
> authority** (body unrestricted). Such additions are *conservative* over the interpreted
> theory: an uninterpreted head always has a model ("everything true"; or head `:= ∅`),
> so no previously-unprovable interpreted statement becomes provable. Heads must **never**
> be interpreted relations or relations owned by another authority.

### 2.4 Existence obligations (the disjunct trick)

Subset types form **unconditionally**. For `subset P` (type `σ`, `rep : σ → α`,
`abs : α → σ`):

1. `abs (rep a) = a` — unconditional.
2. `rep (abs x) = x ↔ (P x ∨ ¬∃y. P y)` — the disjunct **replaces** the nonemptiness side
   condition.

Consistent (model: if `∃y.P y`, ordinary typedef `σ ≅ {x | P x}`; else `σ ≅ α`), and
gives `rep (abs (ε P)) = ε P` unconditionally — the Hilbert-epsilon bargain lifted to
*type formation*. The nonemptiness obligation moves from a **meta-level side condition**
to an **object-level disjunct** that propagates to use sites, where the assumption's/
oracle's `P a` discharges `∃y.P y` and collapses the disjunct to ordinary behaviour. Cost
lands exactly where inhabitation hasn't been established — correct.

- **`new_specification`** — same phenomenon; stop discharging, expose the disjunct.
- **`new_definition`** — trivial existence; only syntactic conditions (closedness, type
  vars) remain.
- **`new_type` / infinity** — flat, syntactic *standing assumptions*; they never inspect
  the assumption set, so they don't violate §2.1. (Choice/`ε` leans on inhabitation; fine.)

**Syntactic side conditions on `subset P`:** `P` locally closed (no escaping de Bruijn
indices); `fv(P) = ∅` (a free *term* var would make the type context-dependent — the real
hazard); free *type* vars allowed (they make `subset_P` a polymorphic type operator).

> **GUIDANCE (ε vs THE).** Where content-addressed dereference uses Hilbert ε, prefer a
> definite description (`THE`) with a uniqueness side-condition (from
> collision-resistance-in-store), even classically, to keep the constructive door open for
> intuitionistic/categorical embeddings.

### 2.5 Type-variable ordering & content-addressed type identity

Tyvar order is **user-declared at def-time** (the Isabelle choice): order is part of the
operator's *interface*, not an artifact of how `P` is written. Def-time check: declared
list is a permutation of `tyvars(P)` (or superset for phantom params).

Forward-compat baked in: store each slot as `(tyvar, kind)` with `kind` defaulting to `*`
(HOL-Omega becomes a change to the slot's *value*, not its *shape* — no
content-address-breaking schema change); placement convention is **declared params first
(in declared order), canonically-generalized params after**, so "declare all" and
"declare none" are endpoints of one scheme. **Regime split:** declared order for
user-facing interfaces (type operators, polymorphic constants); canonical order
(occurrence-over-normal-form) for pure internal machinery (serialization,
auto-generalization).

> **INVARIANT (type identity).** A type operator's identity is `(normalized P, declared
> tyvar order)` — **not** the user-facing name (a name is a namespace binding pointing at
> the address). Same `P`, different declared order ⇒ genuinely different operators ⇒
> different hashes (correct; nothing to dedup).

### 2.6 Structural types: derive, don't trust

Efficiency comes from the **representation layer**, not from kernel-primitive status: a
derived sum compiled to a `(tag, a, b)` cell is exactly as fast as a primitive one;
primitive status only adds axioms to the trusted core. Promote to primitive **only** when
(a) it can't be derived at all, or (b) the representation can't be achieved by derivation.
Binary structures compose; arity-indexed families don't (n-ary characteristic functions
bake arity into the type — no polymorphic record tail, projections need `ε`). So: one
binary primitive, everything n-ary by nesting.

| Keep primitive | Derive (native `(tag,a,b)` representation) |
|---|---|
| `pair` / `FST` / `SND` (three flat slot-native equations) | `sum` / `INL` / `INR` / `CASE` (tagged pair over `bool`) |
| `unit` (terminal object, record tail) | `option` / `SOME` / `NONE` (`unit + A`) |
| iteration: `DOWHILE` (Elgot) | `sexpr` / `CONS` / `CAR` / `CDR` (`μX. atom + X×X`) |
| `bits` / `blob` carriers (machine-backed; §1) | `ITER` (from `DOWHILE` + counter); `num`/`ZERO`/`SUCC` (Peano) |

`DOWHILE` is strictly more expressive than `ITER` (captures non-terminating iteration
primitive recursion can't); `ITER` is derived. Cuts the trusted list from ~22 to ~8–10
with **no efficiency loss**.

> **DECISION (settle before finalizing kernel).** FFI integer efficiency is a **`bits`**
> concern (unary `SUCC` would make a 64-bit count 2⁶⁴ nested cells — catastrophic), not a
> `num` concern. Therefore `num` stays **derived/Peano** for reasoning. The **only
> structural primitives are `pair`, `unit`, `DOWHILE`** plus the `bits`/`blob` carriers.
> Confirm and lock.

### 2.7 The evaluator and store are oracles
Evaluation and content lookup are oracles under the same discipline. Reflection
(logic→computation) and citation (computation→logic) are the coupling directions (§6).

---

## 3. Idiomatic use: metalogic, not direct proof

You **do not** prove in the base. The base is a *less conservative Isabelle*:

1. Define a term language for an **internal logic `L`**.
2. Via LCF, derive **`provable_L(P)`**.
3. Rather than adding oracles, **assume the WASM spec** and verify **decision procedures**
   — often for `L`. **Sound, not complete**; may be **nondeterministic**.
4. Need more power? **Borrow `L`'s strength** by assuming "`L` consistent" — but usually
   you shouldn't need to.

**Metalogic is the game.** Prove in *as weak a logic as possible* (even algebraic
term-tree rewrites), then prove **embeddings** (`provable_HOL(P) → provable_ZF(Emb P)`),
**equiconsistency**, **strength orderings**. Mapping proof-existence to rich models
(topoi in Grothendieck–Tarski set theory, HoTT, categorical logic) is a **first-class use
case**, not a toy.

### 3.1 Why classical HOL + a Turing-complete executor as the base
The base must be the **most accommodating host** — constrain what lives above as little as
possible. Classical HOL + Turing-complete oracle is near-maximally permissive:
classicality at the meta-level does not *impose* classicality on embedded object logics,
it merely declines to *forbid* anything. **Classicality as ecumenism, not a position.**
**Constructivity is something you embed, not assume:** define an intuitionistic internal
logic, prove its metatheory classically; what is classically true *about* `Provable_L`
says nothing constructively *within* `L`.

---

## 4. The mirror principle (adequacy as reachability)

No system internally certifies its own faithfulness (Tarski, second incompleteness,
reflection). We **point a second mirror** and let *agreement* carry confidence.

- You need not any particular `L` faithful — you need the **graph of logics** to contain
  one node faithful by *inspection* (the **silvered node**, e.g. an obviously-correct ZFC
  presentation nobody computes with). Adequacy **propagates along proven edges**;
  adequacy is a **reachability property of the graph**.
- Cost is inverted *on purpose*: proof *production* effort is irrelevant (meta-theorems
  written once, never by a user), so spend arbitrarily much to make the trusted endpoint
  transparent. Pattern: `efficientEncoding ⇔ obviouslyCorrectEncoding`.

### 4.1 What the mirror moves, not removes
- **Edges become the TCB.** `provable_A(P) ⇔ provable_B(emb P)` encodes *both* logics +
  the map; a skew embedding *typechecks*. Burden moves from "is this node faithful" to
  "does this edge state the agreement I mean" — more local, better.
- **Defense is redundancy.** Reach a node by **independent** edge-paths; a skew surfaces
  as inter-path disagreement *unless all paths share it*. The **residual blind spot** =
  "the region where all independent paths share an assumption" — small, explicit,
  locatable, attackable, **never zero** (the last mirror's silvering is a human).

> **INVARIANT (edge directionality).** Strength/equiconsistency edges carry valid
> **direction** in their type. Equiconsistency symmetric; `Con(T) → Con(T')` is **not**.
> Downward transport on an upward-only edge is a *construction error*, not a soundness
> bug found later. The kernel sees only opaque discharges and won't stop you — the type
> system must.

### 4.2 First-class commutative diagrams (untrusted over trusted)
The diagram layer is **host-layer bookkeeping bottoming out in kernel-checked
compositions.** A diagram is a *proof plan*; the composed theorem is the *proof*. A
fallible API for pasting squares has **zero soundness exposure** — it produces a genuine
composed theorem or fails. **Per-output commutativity** is the sharp tool (you rarely need
universal `emb₁;f = emb₂;g` — you need it on *this* elaborated output, often decidable).
**Surface languages elaborate to many embeddings** + verify commutativity (social
mathematics). **Multiple equivalent compilations into the *same* logic** is the
**privileged adequacy probe** (fixed semantics, varies only the untrusted elaboration).
Compiler = **LLVM with logics as targets**: surface → IR → pluggable backends
`IR → (logic, theorem, witnesses)` → commutativity checker. A buggy backend can only
*fail to produce a witness*, never a false theorem.

> **OPEN.** Cone (distinguished semantic apex all agree with — cleaner adequacy) vs
> apex-free diagram (flexible). Default: cone anchored at a silvered node.

---

## 5. The three planes (one architecture, three axes)

### 5.1 Logic plane — trust by faithful embedding
Nodes = logics-as-HOL-theories; edges = embedding / equiconsistency / strength; trust =
reachability from a silvered node. (§3–4.)

### 5.2 Execution plane — trust by consensus
A constructive proof *is* a program: `provable_intuitionistic(P)` discharges (hash-keyed
decision-procedure oracle) to a **runnable extracted artifact**. **"There is a compiler"**
is the meaning of intuitionism; there can be **many** (many realizers = independent
mirrors). Other oracles add executors (x86, RISC-V…); executors **implement each other**
via HOL-proven emulation: `emulate_x86_on_wasm(p,i)=o ↔ run_x86(p,i)=o` (transports
*behavioral agreement*, not truth). **Consilience:** small trusted-executor set + edges ⇒
a result is trustworthy if you trust an executor *or* if independently-built executors
**agree** (agreement needs **no** individually-trusted executor).

> **HAZARD (spec-level independence).** Executor independence is harder to eyeball than
> logic independence — engines share lineage invisibly (NaN canonicalization, float
> rounding, memory-ordering). Consilience is only as independent as the **specs and their
> human readers**, not the ISAs. If all edges prove against one imported semantics, all
> mirrors silver from one blank. Seek **independent semantics per executor** and prove
> *those* agree.

> **OPEN (WasmCert).** No mechanization covers *both* multi-module linking *and* GC.
> Decide: import WasmCert-Isabelle/Coq (strong single node) vs author our own semantics
> for the executed fragment vs multiple independent semantics (genuine spec mirrors).

### 5.3 Content plane — trust by scoped, degrading assumption
The anti-lie, three ways (scope differs per primitive):

| primitive | scoped assumption | property | scope |
|---|---|---|---|
| hash | "no two distinct stored blobs collide" | injectivity-on-present | store |
| signature | "every `(sig,K,D)` present is valid" | soundness-on-present | store |
| ZKP | "every proof present at level λ is sound" | soundness-on-present | store **×** λ |

Stores **compose** (not naively — a cross-collision can appear in `A ∪ B`; *prove* the
composite collision-free), **swap hash functions**, and **degrade gracefully**.

> **Worked example (SHAttered).** Load the SHAttered PDFs ⇒ "no collisions in store"
> *correctly false* (system reports degradation, doesn't sit on a falsehood). Yet a
> *particular Git repo* as a SHA-1 store almost certainly has no collision ⇒ scoped
> theorem holds *for that repo* and store-generic metatheory applies. Dial (weaker per
> notch): collision-free (checkable) → SHA-1 preimage-resistance (assumption, not refuted)
> → trust-the-remote (operational). Slide as far as your threat model forces, **no
> further**; where you stopped is recorded as a discharged assumption. Wrap the repo in a
> BLAKE3 name as desired.

### 5.4 Open-store problem → the global store
Stores are *open*; a later load could retroactively falsify a snapshot theorem. Fix by
**changing the quantifier domain** (the honest version of real cryptographic practice):
assume a **global store of everything seen by everyone in your interaction graph** lacks
`$BAD`; assert each local store — possibly **mapped/filtered** — is a **subset**. "No
`$BAD`" is **downward-closed**, transports to subsets free; growth never retroactively
falsifies. A later blob is either already covered or your **subset/provenance** claim was
false — and provenance is *auditable*. Traded an uncheckable growing obligation for a
checkable per-blob one.

> **INVARIANT (honest bookkeeping, mechanized).** Every hash/sig/ZKP use **must** discharge
> a scoped global-store assumption — no shortcut, no global lie. The *bookkeeping*
> (threading the assumption, generating `f(local) ⊆ global` obligations, discharging
> trivial ones, surfacing non-trivial) is **untrusted compiler elaboration** emitted into
> kernel-checkable form. Human carries *semantic* honesty (what to assume); machine
> carries *syntactic* honesty (proving every use sits under it).

> **HAZARD (map trust).** A buggy/malicious provenance map `f` could send a `$BAD` blob to
> *something else* in the global store, passing the subset check. Content-plane honesty
> bottoms out in execution-plane honesty (maps run on the executor), which bottoms out in
> *its* spec-independence. Restrict maps to a verified-by-consensus class **or** rely on
> re-derivation through an independent `f'`.

---

## 6. The coupling (mutually recursive, not three stacks)
- **logic⇄logic** — `P` faithful because independent embeddings agree (adequacy of
  *meaning*).
- **exec⇄exec** — a computation trustworthy because independent executors agree (adequacy
  of *running*).
- **logic→exec** — a proof's constructive content is a runnable, checkable artifact
  (realizability).
- **exec→logic** — a computation's result is admissible because executor-agreement
  discharges the oracle relation (sound-not-complete decision procedures).

Loop: prove in weak logic → reflect the procedure to the executor → run under
*consensus* → feed the result back as an oracle discharge. Every hop's trust is an
inspected silvered node **or** a consensus among independent mirrors. A shared skew must
survive *across the coupling* — a much smaller residual.

---

## 7. Quantitative confidence (probability as an internal logic)
Define `L_prob` like any logic; its premises (ROM, independence, security parameter) are
*its* scoped meaning-axioms. **Zero new mechanism.** Turns the dial from *ordinal* to
*metric*.
- The **meta-assumption becomes an object of study**: prove `P(store has a collision |
  ROM, k, N) ≤ ε` — a theorem *about* the assumption.
- **Independence becomes a correlation term.** Two agreeing paths give confidence
  depending on `P(both wrong | wrong)` (=1 for colluding mirrors, small for independent).
  A skeptic supplies a higher correlation prior and re-runs the edge; your confidence
  drops by exactly the warranted amount. *Disagreement becomes a number.*
- **Composes as proofs:** union bounds assembled mechanically (`P(fail) ≤ P(L unsound) +
  P(premises false) + P(ROM misapplied) + …`). Infinite but **convergent in usefulness**;
  stop when the next term is below tolerance — because you chose to.
- Even bound **`P(model applies)`** (`P(ROM applies here) ≥ 1−δ`). The un-modeled residual
  relocates to *model choice* — exactly the cryptographer's irreducible human judgment.

> **OPEN (frequentist vs subjective).** Frequentist bounds: objective, compose by
> union/independence, exist only where a real model does. Subjective credences: compose by
> priors, not hash-stable across people. Likely **both, clearly segregated** — named
> prior-objects make "under prior π, confidence ε" a shareable theorem.

---

## 8. No privileged base: the functorial base-shift
Every logic is **data** (a HOL theory), so a functor `F : HOL → NewBase` carries the
**entire logic graph along automatically** — you port the *one* base, not the graph. The
development is **base-parametric** (as Isabelle developments are `THEORY`-parametric).
**A functor preserves what it preserves:** to a stronger/equivalent base, total and
boring; to a *weaker* base, **partial and diagnostic** — it audits which theorems leaned
on dropped strength (EM, choice). The base is **just another node**, `F` **just another
edge**, in a **graph of bases**; prove `F`, `G : NewBase → HOL`, and an
adjunction/equivalence on the relevant fragment ⇒ **base trust becomes consensus** between
two foundations.

> **CRITICAL DECISION (resolve before kernel-2).** (1) **Internal re-hosting** — embed
> `NewBase` as an internal logic; `F`'s functoriality is a theorem in the *current* base;
> "shift" = embed-and-transport; real base stays HOL forever (vindicates the
> maximally-permissive thesis — everything, incl. new foundations, is an internal logic).
> (2) **External re-hosting** — re-implement the kernel over `NewBase`; `F` is a
> development translation checked by *both* kernels; true base-independence at the cost of
> two trusted kernels agreeing. **Default: build (1) first; treat (2) as a later
> consilience upgrade for the base itself.**

---

## 9. Why a non-collapsed trinity (the philosophical spine)
Strong computational trinitarianism (Curry–Howard–Lambek) **collapses two corners**
(proofs *are* programs; propositions *are* types). Our conservativity breaks the collapse
**on purpose**: "`P` evaluates to `E`" is a **fact/observation** (opaque relation),
separate from any *logical* claim about its meaning, separate again from the *proof* that
manipulates it. Three genuinely distinct corners:
- **Computation** (executor) — operational; *happens*; known to the kernel only as opaque
  "observed." **Running a program does not produce a proof.**
- **Logic** (LCF) — normative; what *follows from* what.
- **Facts/observations** (content/oracle) — evidential; what is *the case*, witnessed.

A system letting "`P` evals to `E`" directly *be* a proof = the collapsed trinity =
**unsound the moment the executor is wrong** — the property we engineered away. **The
honest trinity and the conservative kernel force each other.** Classical trinitarianism
*lacks* the **evidence** corner; Hilbert-style foundations *weld* logical truth to trusted
observation by calling both "axiom." **We un-weld them:** an axiom is *just an observation
you decided to trust*. This is **trinitarianism plus a first-class epistemology of
evidence** — where Tarski and the cryptographers live.

> **STANCE.** The observation corner is **irreducible**: "this is the case" is
> categorically different from "this is provable" and "this computes"; no discharge erases
> it (it only *scopes* and *prices* it). Keep the corners distinct in the type system;
> collapsing for convenience is a soundness regression, not an optimization.

---

## 10. Naming, namespaces & the mountable view

### 10.1 Namespaces = prefix-indexed relations; enter = curry, mount = extend
A directory *is* a relation with its first column fixed; a file *is* the relation that
remains. **`enter` is currying** (`R[name,…] ↦ R_name[…]`); **`mount` is relation
extension under a fresh prefix.** One type — a prefix-indexed relation — two operations.
Merge "facts by union, directories by nested union" is **one algebra**: a join-semilattice
under **union, the only combinator.** Each kernel is rooted at a **self-symbol** with sole
authority over its namespace; roots are disjoint by construction, so a collision can only
arise *inside a shared mount* — which is a **detected mirror disagreement** (information,
not corruption).

### 10.2 Mount is sound *for free* (the implication reading)
`mount Q at P` ≡ `∀x. Q(x) ⇒ P(x)`. Sound because the **body is an oracle relation** ⇒ a
conservative Horn-clause-with-oracle-head (§2.3 safe axiom class). Free to assert now;
**meaningful only when `Q` is later grounded** (the source's facts discharged) — a
*deferred transport edge*. The **two-layer import** "key K claims kernel V says B" =
mount-source/credential (a **signature/identity fact**, evidence) **+** the translation
`V-namespace → my-root` (a **logic-plane embedding**, proof). **Keep these two apart** —
fusing them re-welds the truth/evidence corners (§9).

> **DECISION (conflict merge).** When two mounts assert conflicting facts about the same
> foreign relation, the merge **preserves both and marks the region inconsistent** — never
> silently shadows one. Shadowing is the namespace-layer global lie. Precedence is allowed
> only as an *explicit, recorded, scoped* resolution ("I trust K over K′ here"), itself a
> discharged assumption, never a default.

### 10.3 Three name-kinds, keyed to trust corners
- **UUID** (probabilistic collision-freedom) — **content-plane** scoped assumption (adds
  `$BAD = UUID-collision`); serializable, mountable.
- **Opaque gensym** (unserializable) — **no** cross-kernel assumption; provably local;
  can't be mounted (a feature).
- **Serial / deduped under a well-known prefix** — **authority-plane**; collision-freedom
  *enforced* by the allocator, not assumed; meaningful only relative to prefix authority.

Pick by: need to mount it → UUID; need provably-local → gensym; need dense/ordered/deduped
and you own the prefix → serial.

### 10.4 The `.self` node-fact and the mountable filesystem view
`true(some/path/here)` does **not** entail `true(some/path)` — a node may be both a
directory and a fact-bearer, so node-fact ≠ child-facts. Resolve by adjoining a fresh
inhabitant `∎` per name type; `R[…path…, ∎]` is the node-fact, `R[…path…, x≠∎]` is the
child-fact (disjoint by freshness, union-only preserved). The FS projection renders `∎` as
a **reserved `.self` entry**.

Encoding `Relation[fn₁,fn₂,fn₃ | A,B,C,D]`:
- left filenames → directory path (each a `repr_addr` of your choosing).
- **`.self` at the leaf → the table** (SQLite/prolly) with schema `(A,B,C,D)` — *the
  node's own data*.
- **symbolic/reference right-columns → symlinks** alongside (target = `repr_addr`);
  **materialized right-columns → `.self` table cells / regular files.** **`st_mode`
  (file/symlink/dir) is the fact-kind discriminator** — an agent learns a node from one
  `ls -l` + one `cat .self`.
- `unit` = existence = empty-schema `.self`; **distinct** from empty directory (no
  `.self`).

> **INVARIANTS (mountable view).**
> - **`.`/`..` are POSIX noise** — always ignored on import, never emitted as facts.
> - **Empty directories are scratch, not state** (default): a prefix is materialized iff a
>   row exists at/below it; `FS→DB→FS` may drop empty dirs — defined behavior.
> - **`mount` ⟺ attach-under-prefix** (SQLite `ATTACH DATABASE 'f' AS foo` makes `foo.t`
>   queryable and cross-DB joins first-class — the coend/profunctor composition;
>   `SQLITE_MAX_ATTACHED`≈125 is the real ceiling, route a large mount graph through a
>   vtab). The Unix spelling is canonical; `ATTACH` is the backing op.

### 10.5 The profunctor structure (variance, Merkle, VCS ops)
`R[α, β]` reads as a **profunctor** `Cᵒᵖ × D → Set`: **left = contravariant (addresses you
consume), right = covariant (references you produce).** So:
- **`repr_addr` is universal** (every type needs a key, injective *within scope* — by
  authority | assumption | construction).
- **`repr_val` is optional-per-materialization** (faithful, invertible `β ⇄ DBCol`, needed
  only on edges you choose to materialize). **Storing facts about symbolic β is the
  normal case** (you proved theorems about executors you never ran). Symbolic = symlink;
  **dangling symlinks are expected.**
- **Merkle = iterated profunctor composition:** `repr_val` at level *n* serves as
  `repr_addr` at *n−1* (content-address feeds navigation); composition is the **coend over
  the shared blob type** — existential-over-intermediate = Merkle link. **Composition is
  address-level; materialization is value-level; independent.**
- **VCS ops are the profunctor's functorial action:** rename/rebase = precompose on the
  left (contravariant); re-encode blobs = postcompose on the right (covariant).
- **Filename is demoted, not dropped:** one `repr_addr` choice in a left column; a Git tree
  entry `(name, hash)` is two left-addresses for one right-value (FS navigates by `name`,
  stores/verifies by `hash`). **A Git repo = the self-addressing special case** where every
  left column's `repr_addr` is itself content-addressed.

> **OPEN (cross-store composition).** The coend needs the middle β's `repr_addr` to align.
> Hard requirement (only compose stores sharing a hash) vs translatable (a proven
> `repr_addr_A ≅ repr_addr_B` edge lets you compose across hash functions). Latter is one
> more edge in the graph; decide before the store-composition API hardens.

---

## 11. Storage: the VCS native format
Storage **is** the VCS. Two structures, **both content-addressed, both in the TCB** (a
false read asserts a false fact):
- **Git-like trees** — directory structure / the left (path) columns.
- **Dolt-style prolly-tree tables** — the right (data) tuples; content-defined chunking ⇒
  **canonical root** (same logical table = same hash, regardless of insertion order ⇒
  dedup, structural sharing, table-level mirror agreement, diffable/mergeable).

> **INVARIANTS (TCB store).**
> - **Verifiable reads.** A lookup returns `(value, merkle_path)`; a false read **fails**
>   to hash up (not merely "unlikely"). Simplicity of read/write is a *soundness*
>   requirement, not a perf choice.
> - **Merge is untrusted + certificate-checked.** A merge emits `(result_root, proof)`;
>   the proof is checked by a *simple trusted* checker (every input row appears in result
>   or in a marked conflict; every result row comes from an input; roots hash correctly).
>   Clever merge algorithm = untrusted; merge *checker* = simple/trusted. (Sixth instance
>   of the pattern.)
> - **Conflict = preserved diff** (§10.2), never silently shadowed.

> **Untrusted overlays (outside TCB; re-checkable against the prolly tree).** SQLite
> (live query/index acceleration, `ATTACH`-as-mount). Parquet/DuckDB (analytic scans over
> **frozen** data; columnar/immutable/compressed/content-addressed = the natural **"git
> object" / committed relation**). Frozen Parquet mounts into a live session via
> attach-as-mount — the **frozen/live seam = the commit/checkout seam**. *Commit* =
> freeze live table → content-addressed columnar artifact; *checkout/mount* = attach it.

---

## 12. Formats & validity (the format plane)
A format is **not** kernel machinery — it's an **oracle relation `valid(format, data)`**;
validation is a **sound-not-complete decision procedure** on the executor, discharged via
meaning-assumption. A **root format** ("this data is valid") is the format analogue of the
root namespace / silvered node; a format **spec is itself data** valid under a meta-format
⇒ formats-describe-formats bottoms out in one human-inspected root (the format graph **is**
the logic graph wearing a parser).

**Identity = keyed BLAKE3.** A typed value is `id = BLAKE3_keyed(key = format_id, data =
payload)` — the format is the **key**, not bytes in the preimage ⇒ **domain separation for
free** (no concatenation ambiguity), the id is a **genuine third thing** (≠ format, ≠
payload), and it's still a plain CAS entry (validity is **one bit on top of the CAS**).

> **INVARIANTS (formats).**
> - **Validity is keyed.** Validity facts are *minted by a format-specific validator*; the
>   keying **is** the proof the id belongs to that format. Meaning-assumption shape:
>   `∀payload. valid_under(format, payload) ⇒ valid(keyed(format, payload))`. Never assert
>   bare `valid(id)` for an id whose keying you didn't witness. Then `id ⇒ (valid:bool)`
>   is sound with the format *absorbed into the identity* (not stored as a column).
> - **Split planes:** keep `id ⇒ payload_hash` (pure CAS fact, re-checkable by re-keying)
>   separate from `id ⇒ valid` (format-plane oracle fact). Materialized table is a join of
>   the two; don't weld them.
> - **256-bit format ids, infinite by nesting.** A nested format's payload is itself a
>   tagged blob: `keyed(Outer, keyed(Inner, payload))`; fixed-width tag per level,
>   unbounded depth. **Nesting is authority-plane (explicit wrapping).**
> - **Domain-split bit** in the id distinguishes **assigned** (UUID / well-known,
>   authority-plane) from **spec-hash-derived** (content-plane) ids — provably disjoint, no
>   smuggled collision assumption.

> **OPEN (refutation).** Monotone-valid-only (validators only *assert* validity;
> absence = unknown; a spec change makes a *new* format id, so no conflict; dodges the
> conflict-merge rule) **vs** an explicit `invalid`/refuter relation (a positive,
> shareable, mountable "K claims this malformed" that can *conflict* with another
> validator's `valid` ⇒ mirror disagreement under the conflict-merge discipline). Default:
> **monotone, absence-as-unknown, no stored `invalid`** until a refuter component demands
> it.

### 12.1 `Name256` and the carrier+refinement rule
A 256-bit name is **physically a `blob` of length 32** and **logically `Name256 = { b :
blob | len b = 32 }`** — i.e. *just a format* (validator: `len == 32`). **Carrier + optional
refinement is the universal answer to "dedicated type or raw blob":** strong-typed
(`Name256`, compile-time safety) and loose (`blob`, generic plumbing) are the **same value
with/without the refinement proof attached** — `Name256 → blob` forgets (zero-cost,
identity on representation), `blob → Name256` is the checked injection. **`blob` is the
universal carrier; every "type" is a carrier (tuple) + a validity refinement = a format.**

> **DECISIONS.** `Name256` is a **well-known UUID format** (authority-plane primitive,
> stable id alongside "WASM executor", "BLAKE3 CAS"). A name is **32 opaque bytes with no
> intrinsic meaning** — the *consuming position / column type supplies the interpretation*
> (hash vs keyed-id vs UUID vs gensym), consistent with "interpretation is never stored in
> the datum." Adopt unless a case needs a self-describing name (then a small kind/hash-fn
> discriminator alongside the 32 bytes).

---

## 13. Invariant checklist (for reviewers and agents)
1. **Syntactic well-formedness** — never provability-dependent. (§2.1)
2. **Canonical freeze + one threaded tyvar order.** (§2.2, §2.5)
3. **Minimal kernel surface** — union-find audited or certificate-emitting. (§2.2)
4. **Hash-indexed meaning-axioms** — never name-indexed. (§2.3)
5. **Safe axiom class** — heads are own-authority oracle relations only. (§2.3, §10.2)
6. **Disjunct trick** for existence; subset side-conditions `lc` + `fv=∅`. (§2.4)
7. **Type identity = (normalized P, declared tyvar order)**, not the name. (§2.5)
8. **Derive, don't trust** — primitives only `pair`/`unit`/`DOWHILE` + `bits`/`blob`. (§2.6)
9. **`num` derived (Peano); `bits` for FFI integers.** (§2.6, lock this)
10. **No global lie** — every crypto/eval/format use discharges a *scoped* assumption.
11. **Edge directionality typed.** (§4.1)
12. **Diagram layer untrusted**; prefer same-target multi-elaboration as adequacy probe.
13. **Seek spec-level independence** for executor consensus. (§5.2)
14. **Downward-closed global-store assumptions**; provenance auditable; bookkeeping
    mechanized + untrusted. (§5.4)
15. **Probability is an internal logic**; segregate frequentist vs named priors. (§7)
16. **Decide internal vs external base-shift before kernel-2.** (§8)
17. **Keep the three corners distinct** — never collapse evidence into proof. (§9)
18. **Union is the only namespace combinator;** mount = `∀x. Q(x)⇒P(x)`. (§10.1–10.2)
19. **Conflict = preserved + marked inconsistent, never shadowed.** (§10.2, §11)
20. **`repr_addr` universal; `repr_val` optional;** symbolic-by-default; dangling symlinks
    expected. (§10.5)
21. **TCB store = verifiable reads + certificate-checked merges;** overlays re-checkable.
    (§11)
22. **Validity is keyed; format absorbed into identity;** 256-bit ids nest;
    domain-split bit. (§12)
23. **Carrier + refinement** for every type; `Name256` = `blob` len 32, opaque. (§12.1)

---

## 14. Glossary
- **Silvered node** — node whose trust is established by direct human inspection; endpoint
  of trust propagation.
- **Mirror** — an independent path to the same conclusion; confidence = agreement.
- **Residual blind spot** — region where all independent paths share an assumption; small,
  locatable, never zero.
- **Edge** — a proven relationship (embedding, equiconsistency, emulation, subset, mount,
  functor) transporting trust along whatever it preserves.
- **Opaque relation** — uninterpreted symbol an oracle may write to; meaningless until a
  meaning-assumption is discharged.
- **Meaning-assumption** — a (hash-indexed) assumption interpreting an opaque relation
  against a spec; the sole trust boundary.
- **Scoped assumption** — a true statement about a named artifact (this store/repo/λ/
  global store) replacing a false global universal.
- **Plane** — one of {logic, execution, content, format}; each a graph-of-mirrors over the
  substrate.
- **Base-shift** — transporting the whole development along `F : HOL → NewBase`.
- **Disjunct trick** — replacing typedef's nonemptiness side-condition with an object-level
  disjunct `P x ∨ ¬∃y.P y`.
- **`.self` / `∎`** — the node's own fact, distinct from its children; rendered as a
  reserved FS entry / table.
- **`repr_addr` / `repr_val`** — a type's key (universal) / faithful content encoding
  (per-materialization).
- **Keyed identity** — `BLAKE3_keyed(format_id, payload)`; a typed value's content-address.
- **Carrier + refinement** — a type = a `blob`/tuple carrier plus an optional validity
  refinement (itself a format).
