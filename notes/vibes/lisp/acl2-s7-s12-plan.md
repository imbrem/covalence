# ACL2 S7–S12: the remaining stages, concretely

Forward plan for finishing [`acl2-full-plan.md`](./acl2-full-plan.md). S0–S6 are
committed; S5 (ordinals, full-ε₀ wf) + the S11-lite book front end are landed and
awaiting audit+commit. Each stage below names its design inputs, its hard part, and
its gate. Stage designs follow the established discipline: a no-judgment-calls-left
design note **before** implementation (crown proofs skeletoned at `subst_sema`
precision — S2/S6/S5 all closed first-try on their skeletons), adversarial audit
before commit, SKELETONS walls for anything partial.

## S7 — Full definitional principle (NEXT)

Consumes S5. The S5 design (`acl2-s5-design.md` §7, the "S7 seam") already
specifies the entry points:

1. **S5c/S5d first** (walled from S5, precise SKELETONS entries in
   `init/acl2/SKELETONS.md`): `install_user_rows` hand-row seam; `with_ordinals`
   + the seven ordinal UserRows (`def_eq_model` = the already-proved defining
   equations in `ordinal.rs` — pin against `model_image` output); the S5 axiom
   pack (classical `cases` row + equal-mp/contra/truth Schema arms + typed-arith
   ModelImplies rows); `transport_implies_open` (IMPLIES-form open transport —
   needed to *consume* measure obligations and for most real defthms).
2. **IND-ORD** clause family (designed in S5 §8): single measured variable,
   O-P-totality premise + per-IH guarded O<-decrease premises; soundness discharge
   routed through `wf_induct` at `P := λa. ∀σ. eval m σ = a ⟹ eval f σ ≠ anil` —
   the S5 design argues this is structurally *simpler* than the committed S6 IND
   discharge.
3. **Measured defun admission**: obligations = `(O-P (measure …))` +
   `(O< (measure args-of-rec-call) (measure formals))` under the governing tests
   (ACL2's "rulers"), derived in-object via the Hilbert compiler; on success the
   model function comes from **well-founded recursion over o<** — the
   `recursion.rs` graph-construction recipe with `wf_induct` replacing
   `nat_induct` (seam designed in S5 §7). This model-side recursion theorem is
   S7's hard part.
4. **Mutual recursion**: encode as a single function on a tagged sum (the
   standard reduction) or defer with a SKELETONS wall — decide in the S7 design.

**Gate**: a genuinely non-structural defun admitted and used — `ackermann`
(measure = lexicographic pair as an ordinal) or merge-sort by length; a defthm
about it transported. Cross-check: re-derive an S6-provable theorem via IND-ORD
with measure `(acl2-count x)`.

## S8 — Rationals (then complex rationals)

- `rat` as a quotient over `int × posnat` — the recipe is `init/int.rs` itself
  (built as `(nat×nat)/~`; same component-layer + recon pattern).
- Carrier upgrade: the payload-parametric carve makes this a payload swap
  (`coprod int bytes` → `coprod rat bytes`), and all arithmetic flows through the
  single `intval` seam in `prims.rs` — re-point it (`ratval`) and re-prove the
  S1 arithmetic axioms. `aint i` becomes the embedded integer; `integerp` =
  denominator-is-1. New prims: `numerator/denominator/rationalp`.
- Complex rationals afterwards as `rat × rat` (`complex-rationalp`,
  `realpart/imagpart`); `acl2-numberp` = the union. Books rarely need them early.
- Risk: every ground-arith gate in S1–S7 re-runs; budget a full audit round.

## S9 — defchoose / defun-sk

- HOL's ε (init's select machinery) supplies the model witness: for
  `(defchoose w (bv) (φ w bv))`, define the model function by ε and prove the
  defchoose axiom `(implies (φ x bv) (φ (w bv) bv))` as a ModelHolds row.
  Conservativity is by construction (it's a definition + a proved theorem).
- `defun-sk` = defchoose + a defun wrapper; the `forall`/`exists` duals are
  IF-shape macros at translation.
- Fits the existing `Discharge::{ModelEq,ModelHolds}` API without new machinery —
  expected to be a small stage. Note ε-use is *inside* the model (consistent with
  the foundation-invariant guardrail: it never leaks into transported statements).

## S10 — Encapsulation + functional instantiation (hardest remaining)

- **Encapsulate**: process local witness events, prove the exported constraints
  *of the witnesses* (ModelHolds rows), then expose only constrained rows. The
  model is total, so signatures always have witnesses; the honesty question is
  only which constraints were actually proved.
- **Functional instantiation**: given a theorem derived in an env with
  constrained `f`, and concrete `g` satisfying the constraints, conclude the
  `f:=g` instance. Recommended shape (design decision to confirm): a Rust-level
  **certificate transformer** — replay the stored derivation with rows re-bound
  to `g`, re-discharging the constraint obligations — rather than an in-logic
  rule. Soundness is inherited because the replayed certificate is checked from
  scratch in the target env; no new trusted path. If replay cost bites, that is
  the moment to build `family_soundness` (the recorded escape hatch).

## S11 — Full book front end (upgrade the landed S11-lite)

- Wire **induction-backed defthms** into the pipeline: generic premise builder
  for IND/IND-ORD goals (the deferral recorded in `acl2-book-frontend.md` §5 —
  the S6 gate test shows the per-theorem shape; generalize it). Single-variable
  heuristic: try each formal as the induction/measured variable.
- `defmacro`: honest subset — expand quasi-quote-template bodies in Rust
  (logic-invisible, pre-translation); reject computational macros with a tally
  reason. `local` two-pass semantics (visible while processing, stripped from
  the exported theory). `include-book :dir` keyword table + portcullis commands.
- **Gate**: one real community book (candidates: something from `books/std/lists/`
  with only defun/defthm/include-book) imports end-to-end; tally shows a nonzero
  *transported* row; every transported statement spot-checked.

## S12 — Guards

`verify-guards`, guard declarations, `mbe`: logic-irrelevant — accept, record in
the tally notes. One afternoon.

## Cross-cutting consolidation (production-grade track)

Items validated by this program, now worth doing properly (see also
`acl2-agent-guide.md` §process):

1. **Promote `ladder.rs` → `metalogic/`**: the unary `derive_mixed` twin +
   β-bridges now have two proven consumers (acl2; pa/toy migration pending).
2. **Theory-ladder API**: reify/soundness/transport as a trait over
   (clause set, model, interpretation) — 4th instance (ACL2) proves the shape;
   K/SpecTec are the next clients.
3. **Perf seams**: per-env soundness re-proof (measure it; `family_soundness`
   if it bites), batch `Terms::build_with` rebuilds, shared LazyLock sessions.
4. **Process**: workflow scripts must treat a *dead* audit/verify agent as a
   failure, not silence (the S5 run's script bug); audit-before-commit stays
   mandatory for theory stages.
