# Skeletons — `covalence-hol/src/peano`

Intentional placeholders in the Peano-arithmetic deep embedding. See
`CLAUDE.md` § Skeletons and the [crate index](../SKELETONS.md). Build plan:
[`docs/peano-arithmetic-plan.md`](../../../../docs/peano-arithmetic-plan.md).

## Status (what is done)

The deep PA-in-HOL embedding is now a **proper deep embedding** (Phases A–B of
the plan, restructured per `docs/theories-models-and-logics.md §5.5`):

- `fol.rs` — reified locally-nameless FOL syntax (single-sorted Church carrier +
  `Fol` AST) and substitution (`open`/`close`/`shift`/`subst_fvar`), with the
  substitution laws as tests. **Done, proven.**
- `sem.rs` — the **two-sorted HOAS semantic carrier** `Φ_sem⟨'t,'r⟩` (terms →
  `'t`, formulas → `'r`, quantifiers HOAS `all : ('t→'r)→'r`), the encoder
  `encode_form` (de Bruijn → HOAS), and the standard denotation `⟦·⟧` **as a
  single Church fold** at `'t:=nat, 'r:=bool` — the re-packaging that makes the
  impredicative soundness proof go through. **Done, proven.**
- `deep.rs` — the original by-hand standard interpretation; `sem.rs::denote`
  agrees with it up to β (and still supplies `denote_term`). **Done, proven.**
- `pa.rs` — the proper deep embedding:
  - **`Derivable_PA A := ∀d. Closed_PA d ⟹ d A`** (`derivable`) — pure syntactic
    data, the impredicative Church predicate exactly as
    `init/prop.rs::Derivable_Prop`. A derivation is `⊢ Derivable_PA ⌜A⌝` and
    carries **no `⊢ ⟦A⟧`**. Working constructors: `derive_axiom`, `derive_mp`.
  - **`Closed_PA`** has 11 closure clauses — PA1–PA6, modus ponens, the
    induction schema, ∀-specialisation, Leibniz (equality substitutivity), and
    ∀-generalisation — **all proved sound** (the soundness proof discharges each).
  - **The single internalized soundness theorem** `⊢ Derivable_PA A ⟹ ⟦A⟧`
    (`soundness`/`soundness_at`), proved **once** by rule induction
    (`inst d := ⟦·⟧`, discharge `Closed_PA ⟦·⟧` clause by clause: axioms →
    `init::nat` theorems, MP → `imp_elim`, induction → `Thm::nat_induct`,
    specialise/generalise → `Thm::all_elim`/`all_intro`, Leibniz → `eq_mp`).
  - **One-step projection** `project` — soundness applied to a finished
    derivation, a single `imp_elim` + a final β-normalisation of the denotation
    fold to the standard-model `nat`/`bool` form. The acceptance test
    `project_axiom_in_one_step` derives PA3 (`∀x. 0+x=x`) as a *pure* derivability
    witness (no `⟦·⟧`) and projects it in one move to `⊢ ⟦∀x. 0+x=x⟧`, asserting
    it equals `init::nat::add_base`.

  **Done, proven, hypothesis- and oracle-free.** The old lock-step `Derivation`
  is **removed**; a `LockstepDerivation` placeholder documents the secondary
  "directly obtain a HOL fact" path (no constructors yet — see below).

## Now an instance of the generic engine

`Derivable_PA` is wired onto [`crate::metalogic`](../../metalogic/) — the
generic `Derivable_L` substrate. `pa_rule_set` exposes PA's 11 clauses as a
`metalogic::RuleSet` (the single clause source of truth is `pa::clauses_at`);
`derivable`/`derive_axiom`/`derive_mp` reimplement on the engine's
`derivable`/`derive_via_closed`/`nth_conjunct`, pinned byte-identical to the
bespoke shape by `derivable_via_engine_matches`. Soundness/projection are
unchanged (still hand-written here, sharing `clauses_at`).

## Deferred

### Derivation constructors for the quantifier/equality clauses (motive encoding)

The specialise/induction/Leibniz/generalise **closure clauses are present and
proved sound** (`soundness` discharges them), but their **derivation
constructors** — building `⊢ Derivable_PA ⌜A⌝` *through* those clauses for a
concrete arithmetic theorem (e.g. the full `∀x. x+0=x` by induction-on-
derivations) — are **not landed**. The blocker is a real encoding issue, not new
mathematics. The clauses quantify a motive `Q : 't→'r`; `all_cons(Q)` β-closes
the Church handlers *around a free `Q`*, and instantiating `Q := q` for a
concrete motive `q` that mentions the arithmetic handlers (`eq`/`add`/…) leaves
`q`'s handlers **un-captured** (capture-avoiding `all_elim` correctly renames the
binders), so the result does not match `encode_form`'s handler-bound shape.

**Corrected diagnosis (this pass — the naive fix is *unsound*).** The
SKELETONS-suggested "make the motive `Q : Θ_sem → Φ_sem` over whole encoded
terms (injected via `var_t : 't → Θ_sem`)" was tried and **breaks the soundness
proof**, so it is not the fix as stated. Concretely: with a carrier-term motive,
the specialise clause's denotation needs `⟦Q w⟧ = ⟦Q (var_t ⟦w⟧)⟧` for arbitrary
`Q : Θ_sem→Φ_sem` and arbitrary encoded term `w` — but `Q` is an arbitrary HOL
function applied to a *whole carrier value*, so it can distinguish `w` from
`var_t ⟦w⟧` (they are different HOL terms with equal `'t`-denotations).
Equivalently for induction: `nat_induct` needs a genuine `nat→bool` predicate
`P̂`, and `⟦Q (zero_term)⟧ = P̂ 0 = ⟦Q (var_t 0)⟧` fails for the same reason. The
**fold-level** motive `Q : 't→'r` (current design) is exactly the one for which
soundness *is* automatic (`⟦q_at(Q,x)⟧` reduces to `Q x` at `'t:=nat`), so the
fix must **keep the fold-level motive and solve only the constructor capture** —
not change the clause shape.

**What the real fix needs.** Make the *concrete* motive carry **no free handler
variables** so `all_elim(Q := q)` is capture-free, while still being a
`'t→'r` fold. That means parameterizing the motive over the handler
environment explicitly (a motive relative to a fixed handler tuple, threaded by
the clause) — a co-evolution of the clause statement, its soundness discharge,
and the constructor, all kept green together. This is a real multi-step
redesign (the reason it stayed deferred), not a one-line carrier swap.
Additionally, a full FOL calculus wants the **propositional Hilbert schemas**
(as `prop.rs`) so the induction *step* `(x+0=x) ⟹ (Sx+0=Sx)` is itself
derivable (the current 11 clauses have no deduction theorem / no `⟹`-intro at
the derivability level), so even with the motive fix the headline `∀x. x+0=x`
needs those schemas added before it derives purely.

### The `LockstepDerivation` constructors (secondary convenience)

`LockstepDerivation` (a `Fol` + its `⊢ ⟦A⟧`, built together) is declared but has
**no constructors** — a documented placeholder for the secondary path. Add
axiom/rule constructors here if the convenience is wanted; the primary path is
the pure `Derivable_PA` + `project` above.

### `.cov` surface (Phase C)

PA is **not** exposed through the `.cov` script language. The two `.cov`
elaborator features the plan §4 calls for are still missing (they block
expressing PA metatheorems in `.cov`, and `prop.cov` already recorded them):

- a `(pa-induct …)` / impredicative rule-induction tactic — the `inst d := P`
  + `Closed P` discharge has no `.cov` surface;
- **β/η-aware `#concl` matching** — statements over a *bound* variable
  (pervasive in FOL: every `∀x. …`) cannot be re-stated through the current
  first-order, no-β `#concl` matcher.

Phases A–B stand alone in Rust (above), so this is recorded as the next
elaborator work rather than blocking the development.
