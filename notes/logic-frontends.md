# Logic frontends — bringing external systems in as Metamath-defined logics

> **STATUS: DESIGN SKETCH (umbrella).** A uniform plan for bringing external
> proof systems — MLTT, book HoTT, NuPRL, ACL2/Lisp, LF/Dedukti, Lean/Coq,
> Isabelle, … — into Covalence *as object logics over the internal Metamath
> thin waist*, with native accelerators and soundness bridges. This is the
> "north stars are first-class" direction made concrete. Per-family detail in
> the sketches under [`sketches/`](./sketches/):
> [`sketches/type-theories.md`](./sketches/type-theories.md) (MLTT / book HoTT /
> NuPRL / IZF→MLTT), [`sketches/acl2-lisp.md`](./sketches/acl2-lisp.md),
> [`sketches/lf-dedukti.md`](./sketches/lf-dedukti.md).
>
> Read first for context: [`VISION.md`](./VISION.md) §1 (the three-layer
> stack), [`theories-models-and-logics.md`](./theories-models-and-logics.md)
> §5.6/§5.7 (Metamath as the shared logic-definition substrate / the thin
> waist), [`metatheory.md`](./metatheory.md) §5.5 (the two pillars),
> [`roadmap.md`](./roadmap.md).

---

## 1. The frame: every system is a logic over one waist

Covalence does not "support" external provers by re-implementing each one. The
architecture is the three-layer stack:

```
  executors + content-addressing   (WASM / Lisp / native; disk + CPU = root of trust)
  HOL metalogic                    (HOL Light → HOL-ω; the logic we reason IN)
  internal Metamath thin waist     (∃D. ValidProof(D, P, Ax) = Derivable_L(P))
```

Every external system `L` enters through the **top waist**: we write `L` down as
a Metamath database `D_L` (constants, typed variables, axioms + inference rules
as substitution schemas). The "standard theorem of `L`" then *means*, precisely,

```
   Derivable_L(P)  :=  ∃D. ValidProof(D, P, D_L)
```

— a pure, proof-irrelevant **existence** statement. We never store or inspect
the (possibly astronomically large) derivation `D`; we only ever *certify its
existence*, by whatever practical witness is cheapest (a native HOL proof, a
replayed export, a WASM oracle). Everything other than the waist — the HOL
kernel, structured encodings, de Bruijn, set.mm-scale ingestion — is an
**optimization** over this base.

This is what makes the menu uniform: MLTT, ACL2, and Dedukti differ enormously
as systems, but each reduces to *"pick a database `D_L`, certify existence of
derivations in it, and relate it to other databases."*

## 2. The four artifacts per system

Bringing in a system `L` means producing up to four artifacts. Only the first is
mandatory; the rest are accelerations and bridges.

1. **Definition — `D_L` (mandatory).** A Metamath database: `L`'s grammar as
   typecodes, its variables, its axioms and rules as substitution schemas. This
   is the *statability medium* — `L`'s language and rules written in the
   universal substrate. `Derivable_L` is then `derivable(db_rule_set(D_L), ·)`
   (the engine already unifies these — `metalogic::database::Derivable_DB`).

2. **Native accelerator (optional).** A fast Rust/HOL engine — or a WASM oracle,
   or `L`'s own checker run as an untrusted frontend — that *decides or
   constructs* `Derivable_L` goals far faster than blind proof search. For
   computational systems this includes an **executor** (§4): a reducer/evaluator
   that discharges ground-evaluation goals.

3. **Faithfulness — `Metamath-L ≅ native-L` (the admission ticket).** A HOL
   metatheorem that the database means what we intend. It does double duty (the
   down/up duality): *down* it certifies the definition `D_L` is correct (a `.mm`
   database is otherwise just symbols + schemas); *up* it admits every
   accelerator — a hard `Derivable_L(P)` goal is discharged by running the fast
   procedure and transporting its result across `≅`.

4. **Transport — `S`-rewriting + interpretation metatheorems (the payoff).**
   Computable rewriting functions `S` on Metamath terms with existence-transport
   theorems `Derivable_{L₁}(A) ⟹ Derivable_{L₂}(S A)` — relative interpretation,
   conservative extension, model isomorphism. This is pillar-1 (induction on
   derivations) phrased natively in the substrate; it is how systems *relate*.
   The IZF→MLTT translation (sketch) is one such `S`; the HOL bridge is the
   special case where `L₂ = HOL`'s `IsThm`.

## 3. What is hard is never the same thing twice — the difficulty axes

The cost of a frontend is not one number. It decomposes along independent axes,
and a system can be cheap on one and expensive on another:

- **Statability** — can the substrate *express* `L`'s judgments at all?
  - *Trivial:* first-order, no binders in the object terms — ACL2, set theories
    (ZF/IZF/CZF). The waist's metavariable+DV substitution does everything.
  - *Moderate:* genuine binding + dependent judgments — MLTT, LF, NuPRL, CIC.
    Needs an explicit binding discipline (de Bruijn, or the binder-free
    explicit-substitution/CwF presentation, which fits the waist best — see
    [`sketches/type-theories.md`](./sketches/type-theories.md) §2).

- **Binding & the `≅` cost.** Once binders exist, you pick a representation
  (Metamath-metavariable+DV / de Bruijn / locally nameless / HOAS) and pay for
  the equivalence proofs between them. This *is* pillar-2 (representation
  equivalence) and is reusable across every type-theoretic frontend — write it
  once for the type-theory family.

- **Computation / executor.** Does `L` have definitional equality or evaluation?
  - *None:* pure deduction (set theories, propositional/first-order). No executor.
  - *Ground eval:* ACL2 / Lisp — closed terms evaluate. A Lisp/WASM **executor**
    in the bottom layer discharges these; "proven-WASM compilation" is the
    admission protocol.
  - *Conversion:* MLTT / LF-modulo-rewriting — typechecking needs a reducer.
  - *Untyped reduction + PER:* NuPRL — an untyped computation system underneath
    typing, with extensional (undecidable) equality.

- **Strength for a HOL *model* (only for transport *into HOL facts*).** Crucially,
  **`Derivable_L` replay needs no strength at all** — it is syntax + existence.
  Strength only bites when you want a *semantic* bridge (a HOL model of `L`, so
  `L`'s theorems become HOL facts):
  - *In-HOL:* ACL2 (≈ε₀), LF, predicative MLTT, CZF — HOL has the model outright.
  - *Needs universes:* book HoTT's univalent universes, NuPRL's cumulative
    hierarchy — HOL with enough universes / added strength.
  - *Needs a Grothendieck universe (TG):* full IZF / ZF — equiconsistent with ZF,
    so no HOL model without `∃ inaccessible` (the Mizar move). This is the wall
    in [`sketches/type-theories.md`](./sketches/type-theories.md) §5.

- **Import frontend to crib.** Does `L` already export to a replayable format?
  set.mm (done), OpenTheory (HOL family — `covalence-opentheory`), Dedukti /
  Logipedia (LF), ACL2 books, Lean/Coq export. An existing exporter turns
  artifact #2 into "replay someone else's checker as an untrusted frontend."

## 4. The menu at a glance

Difficulty is given as **Derivable** (define `D_L` + replay derivations — the
mandatory floor) **/ +model** (the semantic HOL bridge — only if you want
theorems-as-HOL-facts). "—" model means a pure scoped-truth frontend (transport,
not absolute soundness), which is the *common* case and avoids the strength wall.

| System | Logic family | Statability | Executor | Strength for +model | Crib frontend | Derivable / +model |
|---|---|---|---|---|---|---|
| **set.mm / ZFC** | FOL + ZFC | trivial | none | TG (scoped: —) | set.mm ✓ | **done** / TG-gated |
| **ACL2** | FO computational, ε₀-induction | trivial | ground Lisp eval | in-HOL | ACL2 books | low / low–mod |
| **Lisp** (executor) | — (evaluator) | n/a | *is* the executor | n/a | — | low (bottom-layer) |
| **LF / λΠ** | dependent (Π only) | moderate | conversion | in-HOL | Twelf, Dedukti | moderate / moderate |
| **Dedukti** | λΠ-modulo-rewriting | moderate | rewriting | depends on encoding | Dedukti/Logipedia ✓ | mod–high / per-theory |
| **MLTT** (predicative) | dependent TT | moderate | conversion | in-HOL | Agda export | moderate / moderate |
| **book HoTT** | MLTT + univalence + HITs | moderate | conversion | universes | — | mod–high / high |
| **CZF** | constructive set theory | trivial | none | in-HOL (W-types) | — | low / moderate |
| **IZF** | impredicative const. set thy | trivial | none | **TG / impredicative Ω** | — | low / **blocked** |
| **NuPRL / CTT** | extensional computational TT | moderate | untyped reduction + PER | universes | Nuprl, Rahli-Coq | high / high |
| **Lean / Coq** | CIC (impred. Prop + univ. + ind.) | moderate–hard | conversion | universes | Lean/Coq export | high / high |
| **Isabelle/Pure** | minimal LF (intuit. HO) | moderate | β/η | in-HOL | — | low–mod / low–mod |
| **HOL4 / HOL Light** | classical HOL | (native) | β/η | native | OpenTheory ✓ | done-ish / native |
| **Mizar** | FOL + TG set theory | trivial | none | TG (native) | MML | mod / TG |

(See the per-family sketches for the cells that need a paragraph rather than a
word. Difficulty words are deliberately coarse; there are no LoC/time estimates
here on purpose.)

## 5. Recommended order

The order follows "cheap, high-leverage, reusable infrastructure first":

1. **ACL2 / Lisp** — first-order, weak strength, clean in-HOL model, and the
   *executor* it forces (ground Lisp eval → WASM) is reusable by everything
   computational. It exercises the executor axis with the least logical risk and
   is a named north star. See [`sketches/acl2-lisp.md`](./sketches/acl2-lisp.md).

2. **LF / λΠ** — the smallest dependent type theory (Π only). Building it lays
   the binding + conversion infrastructure that MLTT/HoTT/NuPRL all reuse, and it
   unlocks **Dedukti/Logipedia** ingestion (a second universal-substrate
   ecosystem we can consume). See [`sketches/lf-dedukti.md`](./sketches/lf-dedukti.md).

3. **MLTT (predicative) → book HoTT** — reuses LF's binding machinery; the
   CwF/explicit-substitution presentation is binder-free and fits the waist
   natively. HoTT is MLTT + univalence (cheap) + a finite HIT menu (fiddly). The
   IZF→MLTT translation rides on top as a transport `S`. See
   [`sketches/type-theories.md`](./sketches/type-theories.md).

4. **NuPRL / CTT** — most distinctive (untyped computation system + PER
   semantics + extensional equality); highest cost, but well-charted by the
   Rahli Coq formalization. Do last in the type-theory family. Same sketch §6.

Lean/Coq (CIC), Isabelle/Pure, Mizar, PVS, Andromeda, Agda, Cedille are further
targets — each is a variation on a family already covered (CIC = MLTT +
impredicative Prop + inductive schema; Pure = LF restricted to →; Mizar = the TG
move; Andromeda = NuPRL-flavored). They get a row in the table, not yet a sketch.

## 6. The deep point — many waists, one substrate

LF/Dedukti is special: it is *itself* a "universal logic substrate," a direct
cousin of our Metamath waist (dependently typed + binding-native + proof-
relevant, where ours is first-order + substitution-only + proof-irrelevant). So
the most ambitious artifact in this whole plan is a **waist-to-waist `≅`**:
encode the λΠ typing judgment as a Metamath database, encode Metamath as a λΠ
signature, and relate them. That positions Covalence to consume the entire
Dedukti/Logipedia interchange ecosystem *through* the substrate it already has —
the ultimate expression of "everything else is an optimization." See
[`sketches/lf-dedukti.md`](./sketches/lf-dedukti.md) §5.
