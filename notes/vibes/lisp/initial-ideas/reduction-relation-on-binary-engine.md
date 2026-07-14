# A proper Lisp `Reduces` relation on the binary `Derivable` engine (design)

Goal (from the ask): give Lisp a **proper reduction relation — the transitive closure of a
small-step operational semantics** — built (like k-frontend's CFG `Derives` and the
mm-metatheory `Derivable_DB`) on the kernel's inductive-relation engine. Then integer
literals (⇒ **two dialects**: with / without integers). **Keep the value semantics as an
option.** The relation is the foundation for recursive definitions → full Scheme.

## The engine already exists — `crate::metalogic::binary`

The merged CFG stratum ships a reusable **binary inductive-relation engine**
(`crates/kernel/hol/init/src/metalogic/binary.rs`), the two-argument twin of the Metamath
`Derivable` metatheory:

```text
Derives_L n w := ∀d : A → B → bool.  Closed_L d  ⟹  d n w        (impredicative lfp)
```

- `RuleSet2::new(a_ty, b_ty, clauses)` — define a relation `d : A → B → bool` by a fixed
  ordered list of closure clauses (each a `bool` term built via `d_apply(n,w)`).
- `derivable2(rs, n, w)` — the proposition `Derives_L n w`.
- `derive_mixed(rs, clause_idx, n_clauses, word_args, premises)` — discharge
  `⊢ Derives_L n w` through clause `clause_idx`, peeling its `∀`s with `word_args` and its
  antecedents with `premises`: `Premise::Side(thm)` = a leaf theorem of *another* relation,
  `Premise::Derivation(thm)` = a sub-derivation of *this* relation. **Every step
  kernel-rechecked** — a driver bug can only fail to prove, never forge.
- `rule_induction2(pred, clause_proofs, …)` — rule induction, for metatheorems
  (determinism, progress, soundness) later.

All clauses are first-order (∀ over the carriers only), so the β-capture wall doesn't bite.
This is the same shape as `init/regex`'s `Matches` and the CFG `Derives_E` — we reuse it.

## `Step : sexpr → sexpr → bool` — the small-step relation

Carriers `(A, B) = (sexpr, sexpr)`. One `RuleSet2` clause per reduction rule. Redex rules
are base clauses (word-args = the sub-terms, no premises); congruence rules carry one
`Premise::Derivation` (a `Step` sub-derivation):

| clause | shape |
|---|---|
| `car` | `∀h t. Step (car (scons h t)) h` |
| `cdr` | `∀h t. Step (cdr (scons h t)) t` |
| `atom?`-cons / -atom / -nil | `∀…. Step (atom? V) NIL` / `… T` (⇒ **sexpr** `t`/`nil`, not HOL bool) |
| `consp?` / `null?` | analogous, sexpr-valued |
| `eq?` atoms | `∀a b. Step (eq? (atom a) (atom b)) ⌜a==b ? t : nil⌝` |
| `cond` | `Step (cond (t . rest)) …` / `Step (cond (nil . rest)) (cond rest)` — a **sexpr** truthiness test (nil = false, else true), which *dissolves the "truthy-data cond" wall* the value semantics hit |
| β | `∀x b a. Step ((lambda x b) a) b[a/x]` |
| δ (defun) | `∀…. Step (f args) body[args]` — referencing the def (a `Premise::Side` def-equation, exactly the defun-as-hypothesis mechanism, now feeding a `Step` clause) |
| **congruence** | `∀a a'. Step a a' ⟹ Step (car a) (car a')`, … per elimination context (leftmost-innermost) |

Key win: making `t`/`nil` **sexpr atoms** (not HOL `bool`) unifies the value kinds — the
`Bool`-vs-`Data` split and the truthy-`cond` blocker from the value semantics both vanish.
Everything is an sexpr value; a value is `atom | snil | scons chain` (numbers later).

## `Reduces = Step*` — the reflexive-transitive closure

A **second** `RuleSet2`, referencing `Step`:

| clause | shape |
|---|---|
| refl | `∀t. Reduces t t` |
| step | `∀a b c. Step a b ⟹ Reduces b c ⟹ Reduces a c` |

`Step a b` is a `Premise::Side` (a `Step` theorem); `Reduces b c` is a `Premise::Derivation`
(a `Reduces` sub-derivation). A driver builds `⊢ Reduces input value` by: prove each
`⊢ Step tᵢ tᵢ₊₁`, then fold with the `step` clause + a final `refl`. (For the REPL's
left-to-right streaming — append a step at the *end* — either build right-nested from the
value back, or prove a small `Reduces a b ⟹ Step b c ⟹ Reduces a c` snoc lemma via
`rule_induction2` once.)

`⊢ Reduces input output` is now a genuine **membership theorem**, not an equation —
partial/nondeterministic/non-terminating reductions are all expressible (the
`reduction-relations-and-state.md` shape, finally on real kernel machinery).

## Wiring: a new `Semantics`, value semantics kept

Two `covalence_repl_core::Semantics` impls over the same `Repr = sexpr Term`:

- **`ValueSemantics`** (the current `LispSemantics`) — each step a kernel equation
  `⊢ from = to`, composed by `trans` into `⊢ input = value`. *Kept as an option* (fast,
  big-step, deterministic-terminating).
- **`RelationalSemantics`** (new) — each step a `⊢ Step from to` membership theorem,
  composed into `⊢ Reduces input cur` via the `Reduces` closure. The `StepCert::thm` is a
  `Step` theorem; `compose` snocs it onto the `Reduces` chain.

The `Session` gets a mode (a `#semantics value|reduction` directive, or a dialect flag).
Same reader, same driver structure (leftmost-innermost redex search), different `Semantics`.

## Two dialects via integer literals

Integers enter as **extra `Step` clauses** over int-literal sexpr atoms:
`∀a b. Step (+ (int a) (int b)) (int ⌜a+b⌝)` (and `-`, `*`, `<`, `=`), backed by the
kernel int-arithmetic computation the eval tier already has. That yields **two dialects**:

- `sector` — the pure McCarthy fragment (no integers).
- `sector+int` — adds the integer `Step` clauses.

They form the refinement order from `lisp-dialects-and-order.md`: `sector ⊑ sector+int`
(every `sector` program reduces identically in `sector+int`). A dialect = a chosen clause
subset of the `Step` `RuleSet2`.

## Build plan

1. **`Step`/`Reduces` relations** in a kernel module (`init/lisp_step.rs` beside
   `init/lisp.rs`, or a `covalence-lisp` module under `hol`): the two `RuleSet2`s + a
   driver `prove_step(redex) -> ⊢ Step …` and `prove_reduces(input) -> (value, ⊢ Reduces
   input value)`. Tests: `⊢ Reduces (car (cons a b)) a`; multi-step
   `⊢ Reduces (car (cdr (quote (a b c)))) b`; a stuck term has no step.
2. **sexpr `t`/`nil` + truthy `cond`** — define the sexpr booleans, retarget the predicate
   clauses; this is the piece the value semantics couldn't do.
3. **`RelationalSemantics`** in covalence-lisp + a `Session` mode toggle; keep
   `ValueSemantics`. Both drive the same REPL; `#semantics` switches. Differential test:
   where both terminate, the relation's `output` = the value semantics' `value`.
4. **Integer dialect** — the int `Step` clauses; the two-dialect flag; tests
   `⊢ Reduces (+ 2 2) 4` in `sector+int`, and `(+ 2 2)` *stuck* in `sector`.
5. **Recursion in the relation** — the δ-clause fed by the defun hypotheses (already the
   sound mechanism); now non-termination is a genuine unbounded `Step` stream (fuel-bounded
   driver), the foundation for full Scheme.

Metatheorems (later, via `rule_induction2`): determinism of `Step`, `Reduces` = `Step`
reflexive-transitive closure, `sector ⊑ sector+int` inclusion.
